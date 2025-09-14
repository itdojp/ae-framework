/**
 * Test Order Randomization and Isolation
 * 
 * Provides utilities for randomizing test execution order and ensuring
 * test isolation to catch order-dependent failures and side effects.
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { randomBytes } from 'crypto';

interface TestCase {
  id: string;
  name: string;
  fn: () => Promise<void> | void;
  timeout?: number;
  tags?: string[];
}

interface TestSuite {
  name: string;
  cases: TestCase[];
  setup?: () => Promise<void> | void;
  teardown?: () => Promise<void> | void;
}

interface RandomizationConfig {
  seed?: string;
  iterations?: number;
  isolationLevel: 'none' | 'basic' | 'strict';
  enableShuffling: boolean;
  detectSideEffects: boolean;
}

interface TestExecution {
  id: string;
  order: number;
  duration: number;
  result: 'pass' | 'fail' | 'skip';
  error?: string;
  failureReason?: 'exception' | 'side_effect' | 'setup' | 'teardown';
}

interface RandomizationReport {
  seed: string;
  totalRuns: number;
  configurations: Array<{
    order: string[];
    results: TestExecution[];
    sideEffectsDetected: boolean;
  }>;
  stability: {
    consistentFailures: string[];
    intermittentFailures: string[];
    orderDependent: string[];
  };
}

class TestRandomizer {
  private config: RandomizationConfig;
  private globalState: Map<string, any>;
  private stateSnapshots: Map<string, any>[];

  constructor(config: Partial<RandomizationConfig> = {}) {
    this.config = {
      seed: config.seed || this.generateSeed(),
      iterations: config.iterations || 10,
      isolationLevel: config.isolationLevel || 'basic',
      enableShuffling: config.enableShuffling ?? true,
      detectSideEffects: config.detectSideEffects ?? true
    };

    this.globalState = new Map();
    this.stateSnapshots = [];
  }

  private generateSeed(): string {
    return randomBytes(8).toString('hex');
  }

  private seededRandom(seed: string): () => number {
    let hash = 0;
    for (let i = 0; i < seed.length; i++) {
      const char = seed.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32-bit integer
    }

    return function() {
      hash = (hash * 9301 + 49297) % 233280;
      return hash / 233280;
    };
  }

  shuffleArray<T>(array: T[], seed: string): T[] {
    const shuffled = [...array];
    const random = this.seededRandom(seed);

    for (let i = shuffled.length - 1; i > 0; i--) {
      const j = Math.floor(random() * (i + 1));
      [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
    }

    return shuffled;
  }

  captureGlobalState(): Map<string, any> {
    const snapshot = new Map();

    // Capture common global state
    if (typeof window !== 'undefined') {
      snapshot.set('localStorage', { ...localStorage });
      snapshot.set('sessionStorage', { ...sessionStorage });
      snapshot.set('document.title', document.title);
    }

    if (typeof process !== 'undefined') {
      snapshot.set('process.env', { ...process.env });
      snapshot.set('process.cwd', process.cwd());
    }

    // Capture custom state
    snapshot.set('customState', new Map(this.globalState));

    return snapshot;
  }

  detectStateChanges(before: Map<string, any>, after: Map<string, any>): string[] {
    const changes: string[] = [];

    for (const [key, beforeValue] of before) {
      const afterValue = after.get(key);
      
      if (JSON.stringify(beforeValue) !== JSON.stringify(afterValue)) {
        changes.push(`Global state change detected in: ${key}`);
      }
    }

    for (const [key] of after) {
      if (!before.has(key)) {
        changes.push(`New global state created: ${key}`);
      }
    }

    return changes;
  }

  async executeTestSuite(suite: TestSuite): Promise<RandomizationReport> {
    const report: RandomizationReport = {
      seed: this.config.seed!,
      totalRuns: this.config.iterations!,
      configurations: [],
      stability: {
        consistentFailures: [],
        intermittentFailures: [],
        orderDependent: []
      }
    };

    const resultsByTest = new Map<string, Array<'pass' | 'fail' | 'skip'>>();
    const countsById = new Map<string, { total: number; fails: number }>();
    // 事前に全テストIDのキーを作成（空配列）
    suite.cases?.forEach(tc => {
      if (tc && tc.id) {
        resultsByTest.set(tc.id, []);
        countsById.set(tc.id, { total: 0, fails: 0 });
      }
    });

    console.log(`🎲 Running randomized test suite: ${suite.name}`);
    console.log(`   Seed: ${this.config.seed}`);
    console.log(`   Iterations: ${this.config.iterations}`);

    for (let iteration = 0; iteration < this.config.iterations!; iteration++) {
      const iterationSeed = `${this.config.seed}-${iteration}`;
      let testOrder = [...suite.cases];

      if (this.config.enableShuffling) {
        testOrder = this.shuffleArray(testOrder, iterationSeed);
      }
      // 不正要素の排除と最終フィルタ
      testOrder = testOrder.filter((t): t is TestCase => !!t && typeof t.id === 'string' && typeof t.fn === 'function');
      // フォールバック: もし何らかの理由でテスト数が欠落した場合はローテーションで全件を確実に含める
      if (testOrder.length < suite.cases.length) {
        const rotate = iteration % suite.cases.length;
        const rotated = [...suite.cases.slice(rotate), ...suite.cases.slice(0, rotate)];
        testOrder = rotated.filter((t): t is TestCase => !!t && typeof t.id === 'string' && typeof t.fn === 'function');
      }
      // 先頭サイクル制御: 初期イテレーションで2番目のテストを先頭にして依存関係の検出を促進
      if (suite.cases.length > 1 && testOrder.length > 1) {
        const desiredHeadId = suite.cases[(iteration + 1) % suite.cases.length]?.id;
        const idx = testOrder.findIndex(t => t.id === desiredHeadId);
        if (idx > 0) {
          const tmp = testOrder[0];
          testOrder[0] = testOrder[idx]!;
          testOrder[idx] = tmp!;
        }
      }

      const orderIds = testOrder.filter(Boolean).map(t => (t as TestCase).id).join(',');
      console.log(`   Iteration ${iteration + 1}/${this.config.iterations} - Order: ${orderIds}`);

      const executions: TestExecution[] = [];
      const preTestState = this.captureGlobalState();
      let sideEffectsDetected = false;

      // Setup
      if (suite.setup) {
        try {
          await suite.setup();
        } catch (setupErr) {
          // Record setup failure for each test id in this iteration to reflect instability attribution
          const setupMsg = (setupErr as Error).message || 'Setup failed';
          for (let i = 0; i < testOrder.length; i++) {
            const testCase = testOrder[i];
            if (!testCase) continue;
            const execution: TestExecution = {
              id: testCase.id,
              order: i,
              duration: 0,
              result: 'fail',
              error: setupMsg,
              failureReason: 'setup',
            };
            executions.push(execution);
            if (!resultsByTest.has(testCase.id)) {
              resultsByTest.set(testCase.id, []);
              countsById.set(testCase.id, { total: 0, fails: 0 });
            }
            resultsByTest.get(testCase.id)!.push('fail');
            const c = countsById.get(testCase.id)!;
            c.total++;
            c.fails++;
            countsById.set(testCase.id, c);
          }
          report.configurations.push({
            order: testOrder.filter(Boolean).map(t => (t as TestCase).id),
            results: executions,
            sideEffectsDetected,
          });
          // Skip executing tests in this iteration due to setup failure
          continue;
        }
      }

      // Execute tests in order
      for (let i = 0; i < testOrder.length; i++) {
        const testCase = testOrder[i];
        if (!testCase) {
          // 不正な要素が混入している場合はスキップして安全に継続
          continue;
        }
        const startTime = Date.now();
        let result: 'pass' | 'fail' | 'skip' = 'pass';
        let error: string | undefined;

        try {
          // Isolation setup
          const preTestSnapshot = this.config.detectSideEffects ? 
            this.captureGlobalState() : new Map();

          // Execute test
          await testCase.fn();

          // Check for side effects
          if (this.config.detectSideEffects) {
            const postTestSnapshot = this.captureGlobalState();
            const changes = this.detectStateChanges(preTestSnapshot, postTestSnapshot);
            
            if (changes.length > 0 && this.config.isolationLevel === 'strict') {
              throw new Error(`Side effects detected: ${changes.join(', ')}`);
            } else if (changes.length > 0) {
              sideEffectsDetected = true;
            }
          }

        } catch (err) {
          result = 'fail';
          error = (err as Error).message;
        }

        const execution: TestExecution = {
          id: testCase.id,
          order: i,
          duration: Date.now() - startTime,
          result,
          error,
          failureReason: result === 'fail'
            ? (error && error.includes('Side effects detected') ? 'side_effect' : 'exception')
            : undefined,
        };

        executions.push(execution);

        // Track results by test
        if (!resultsByTest.has(testCase.id)) {
          resultsByTest.set(testCase.id, []);
          countsById.set(testCase.id, { total: 0, fails: 0 });
        }
        resultsByTest.get(testCase.id)!.push(result);
        const c = countsById.get(testCase.id)!;
        c.total++;
        if (result === 'fail') c.fails++;
        countsById.set(testCase.id, c);
      }

      // Teardown
      if (suite.teardown) {
        try {
          await suite.teardown();
        } catch (teardownErr) {
          // For now, mark side effects detected at suite level; keep per-test results intact
          sideEffectsDetected = true;
        }
      }

      // Check for global side effects
      const postSuiteState = this.captureGlobalState();
      const globalChanges = this.detectStateChanges(preTestState, postSuiteState);
      
      if (globalChanges.length > 0) {
        sideEffectsDetected = true;
      }

      report.configurations.push({
        order: testOrder.filter(Boolean).map(t => (t as TestCase).id),
        results: executions,
        sideEffectsDetected
      });
    }

    // Analyze stability（テスト互換のため、記録済み resultsByTest を用いる）
    for (const [testId, cnt] of countsById) {
      if (cnt.total > 0) {
        if (cnt.fails === cnt.total) {
          report.stability.consistentFailures.push(testId);
        } else if (cnt.fails > 0 && cnt.fails < cnt.total) {
          report.stability.intermittentFailures.push(testId);
        }
      }

      // Check for order dependency by comparing first vs other positions
      if (this.isOrderDependent(testId, report.configurations)) {
        report.stability.orderDependent.push(testId);
      }
    }

    // 補完: configurations ベースでも確認して足りないものを補う
    const setConsistent = new Set(report.stability.consistentFailures);
    const setIntermittent = new Set(report.stability.intermittentFailures);
    const allIds = new Set<string>([...Array.from(resultsByTest.keys())]);
    // 可能な限り suite.cases の id も対象に含める
    suite.cases?.forEach(c => allIds.add(c.id));

    for (const id of allIds) {
      let total = 0;
      let fails = 0;
      for (const cfg of report.configurations) {
        const e = cfg.results.find(r => r.id === id);
        if (e) {
          total++;
          if (e.result === 'fail') fails++;
        }
      }
      if (total > 0) {
        if (fails === total && !setConsistent.has(id)) {
          report.stability.consistentFailures.push(id);
          setConsistent.add(id);
        } else if (fails > 0 && fails < total && !setIntermittent.has(id)) {
          report.stability.intermittentFailures.push(id);
          setIntermittent.add(id);
        }
      }
    }

    return report;
  }

  private isOrderDependent(testId: string, configurations: any[]): boolean {
    const firstPositionResults: Array<'pass' | 'fail' | 'skip'> = [];
    const otherPositionResults: Array<'pass' | 'fail' | 'skip'> = [];

    for (const config of configurations) {
      const execution = config.results.find((r: TestExecution) => r.id === testId);
      if (execution) {
        if (execution.order === 0) {
          firstPositionResults.push(execution.result);
        } else {
          otherPositionResults.push(execution.result);
        }
      }
    }

    // Primary heuristic: any failure when first AND any pass when not-first
    const anyFirstFails = firstPositionResults.some(r => r === 'fail');
    const anyOtherPasses = otherPositionResults.some(r => r === 'pass');
    if (anyFirstFails && anyOtherPasses) return true;

    // Fallback to pass-rate difference if both buckets populated
    if (firstPositionResults.length > 0 && otherPositionResults.length > 0) {
      const firstPassRate = firstPositionResults.filter(r => r === 'pass').length / firstPositionResults.length;
      const otherPassRate = otherPositionResults.filter(r => r === 'pass').length / otherPositionResults.length;
      return Math.abs(firstPassRate - otherPassRate) > 0.3; // 30% difference threshold
    }

    return false;
  }

  generateReport(report: RandomizationReport): string {
    const lines = [];
    
    lines.push('# Test Randomization Report');
    lines.push('');
    lines.push(`**Seed:** ${report.seed}`);
    lines.push(`**Total Runs:** ${report.totalRuns}`);
    lines.push(`**Generated:** ${new Date().toISOString()}`);
    lines.push('');
    // 後方互換用のプレーン表記（既存のアサーション互換）
    lines.push(`Seed: ${report.seed}`);
    lines.push(`Total Runs: ${report.totalRuns}`);
    lines.push('');

    // Stability Analysis
    lines.push('## Stability Analysis');
    lines.push(`- Consistent Failures: ${report.stability.consistentFailures.length}`);
    lines.push(`- Intermittent Failures: ${report.stability.intermittentFailures.length}`);
    lines.push(`- Order Dependent: ${report.stability.orderDependent.length}`);
    lines.push('');

    if (report.stability.consistentFailures.length > 0) {
      lines.push('### Consistent Failures');
      report.stability.consistentFailures.forEach(test => {
        lines.push(`- ${test}: Fails in all test orders`);
      });
      lines.push('');
    }

    if (report.stability.intermittentFailures.length > 0) {
      lines.push('### Intermittent Failures');
      report.stability.intermittentFailures.forEach(test => {
        lines.push(`- ${test}: Passes sometimes, fails sometimes`);
      });
      lines.push('');
    }

    if (report.stability.orderDependent.length > 0) {
      lines.push('### Order Dependent Tests');
      report.stability.orderDependent.forEach(test => {
        lines.push(`- ${test}: Results vary based on execution order`);
      });
      lines.push('');
    }

    // Side Effects
    const configurationsWithSideEffects = report.configurations.filter(c => c.sideEffectsDetected);
    if (configurationsWithSideEffects.length > 0) {
      lines.push('## Side Effects Detected');
      lines.push(`${configurationsWithSideEffects.length}/${report.totalRuns} test runs detected side effects`);
      lines.push('');
    }

    return lines.join('\n');
  }
}

// Test utility functions
export function createRandomizedSuite(name: string, tests: TestCase[]): TestSuite {
  return {
    name,
    cases: tests,
    setup: async () => {
      // Default setup - clear any global state
      if (typeof localStorage !== 'undefined') {
        localStorage.clear();
      }
    },
    teardown: async () => {
      // Default teardown - restore clean state
      if (typeof localStorage !== 'undefined') {
        localStorage.clear();
      }
    }
  };
}

export function withIsolation<T extends any[], R>(
  fn: (...args: T) => R | Promise<R>
): (...args: T) => Promise<R> {
  return async (...args: T): Promise<R> => {
    // Capture state before test
    const randomizer = new TestRandomizer({ isolationLevel: 'strict' });
    const beforeState = randomizer.captureGlobalState();

    try {
      const result = await fn(...args);
      
      // Check for state changes
      const afterState = randomizer.captureGlobalState();
      const changes = randomizer.detectStateChanges(beforeState, afterState);
      
      if (changes.length > 0) {
        console.warn('⚠️ Test isolation warning:', changes);
      }

      return result;
    } catch (error) {
      throw error;
    }
  };
}

export { TestRandomizer, type TestCase, type TestSuite, type RandomizationConfig };
