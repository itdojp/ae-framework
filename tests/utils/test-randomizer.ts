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

    console.log(`🎲 Running randomized test suite: ${suite.name}`);
    console.log(`   Seed: ${this.config.seed}`);
    console.log(`   Iterations: ${this.config.iterations}`);

    for (let iteration = 0; iteration < this.config.iterations!; iteration++) {
      const iterationSeed = `${this.config.seed}-${iteration}`;
      let testOrder = [...suite.cases];

      if (this.config.enableShuffling) {
        testOrder = this.shuffleArray(testOrder, iterationSeed);
      }

      // Guard against any malformed test entries
      testOrder = testOrder.filter((t): t is TestCase => !!t && typeof t.id === 'string' && typeof t.fn === 'function');
      console.log(`   Iteration ${iteration + 1}/${this.config.iterations} - Order: ${testOrder.map(t => t.id).join(',')}`);

      const executions: TestExecution[] = [];
      const preTestState = this.captureGlobalState();
      let sideEffectsDetected = false;

      // Setup
      if (suite.setup) {
        await suite.setup();
      }

      // Execute tests in order
      for (let i = 0; i < testOrder.length; i++) {
        const testCase = testOrder[i];
        if (!testCase) {
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
          error
        };

        executions.push(execution);

        // Track results by test
        if (testCase.id) {
          if (!resultsByTest.has(testCase.id)) {
            resultsByTest.set(testCase.id, []);
          }
          resultsByTest.get(testCase.id)!.push(result);
        }
      }

      // Teardown
      if (suite.teardown) {
        await suite.teardown();
      }

      // Check for global side effects
      const postSuiteState = this.captureGlobalState();
      const globalChanges = this.detectStateChanges(preTestState, postSuiteState);
      
      if (globalChanges.length > 0) {
        sideEffectsDetected = true;
      }

      report.configurations.push({
        order: testOrder.map(t => t?.id).filter((id): id is string => typeof id === 'string'),
        results: executions,
        sideEffectsDetected
      });
    }

    // Analyze stability
    for (const [testId, results] of resultsByTest) {
      const failures = results.filter(r => r === 'fail').length;
      const total = results.length;

      if (failures === total) {
        report.stability.consistentFailures.push(testId);
      } else if (failures > 0 && failures < total) {
        report.stability.intermittentFailures.push(testId);
      }

      // Check for order dependency by comparing first vs other positions
      if (this.isOrderDependent(testId, report.configurations)) {
        report.stability.orderDependent.push(testId);
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

    // Simple heuristic: if results differ significantly between positions
    const firstPassRate = firstPositionResults.filter(r => r === 'pass').length / firstPositionResults.length;
    const otherPassRate = otherPositionResults.filter(r => r === 'pass').length / otherPositionResults.length;

    return Math.abs(firstPassRate - otherPassRate) > 0.3; // 30% difference threshold
  }

  generateReport(report: RandomizationReport): string {
    const lines = [];
    
    lines.push('# Test Randomization Report');
    lines.push('');
    lines.push(`**Seed:** ${report.seed}`);
    lines.push(`**Total Runs:** ${report.totalRuns}`);
    lines.push(`**Generated:** ${new Date().toISOString()}`);
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
