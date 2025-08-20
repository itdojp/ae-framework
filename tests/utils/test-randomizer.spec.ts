/**
 * Test Randomization and Isolation Tests
 * 
 * Validates the test randomization system and demonstrates
 * order-dependent test detection capabilities.
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { TestRandomizer, TestCase, createRandomizedSuite, withIsolation } from './test-randomizer.js';

describe('Test Randomization System', () => {
  let randomizer: TestRandomizer;

  beforeEach(() => {
    randomizer = new TestRandomizer({
      seed: 'test-seed-123',
      iterations: 5,
      isolationLevel: 'basic',
      enableShuffling: true,
      detectSideEffects: true
    });
  });

  it('should generate consistent shuffles with same seed', () => {
    const array = ['a', 'b', 'c', 'd', 'e'];
    
    const shuffle1 = randomizer.shuffleArray(array, 'seed1');
    const shuffle2 = randomizer.shuffleArray(array, 'seed1');
    const shuffle3 = randomizer.shuffleArray(array, 'seed2');
    
    expect(shuffle1).toEqual(shuffle2); // Same seed = same order
    expect(shuffle1).not.toEqual(shuffle3); // Different seed = different order
    expect(shuffle1).toHaveLength(array.length);
  });

  it('should detect global state changes', () => {
    const before = new Map([
      ['localStorage', { key1: 'value1' }],
      ['customState', { counter: 0 }]
    ]);

    const after = new Map([
      ['localStorage', { key1: 'value1', key2: 'value2' }], // Added key
      ['customState', { counter: 1 }] // Changed value
    ]);

    const changes = randomizer.detectStateChanges(before, after);
    
    expect(changes).toHaveLength(2);
    expect(changes.some(c => c.includes('localStorage'))).toBe(true);
    expect(changes.some(c => c.includes('customState'))).toBe(true);
  });

  it('should run randomized test suite and detect issues', async () => {
    let globalCounter = 0;
    let testExecutionOrder: string[] = [];

    const problematicTests: TestCase[] = [
      {
        id: 'test-a',
        name: 'Test A - Increments counter',
        fn: () => {
          globalCounter++;
          testExecutionOrder.push('A');
        }
      },
      {
        id: 'test-b', 
        name: 'Test B - Depends on counter',
        fn: () => {
          testExecutionOrder.push('B');
          if (globalCounter === 0) {
            throw new Error('Test B requires Test A to run first');
          }
        }
      },
      {
        id: 'test-c',
        name: 'Test C - Independent',
        fn: () => {
          testExecutionOrder.push('C');
          expect(true).toBe(true);
        }
      }
    ];

    const suite = createRandomizedSuite('Problematic Suite', problematicTests);
    const report = await randomizer.executeTestSuite(suite);

    expect(report.totalRuns).toBe(5);
    expect(report.configurations).toHaveLength(5);
    
    // Should detect order dependency in test-b
    expect(report.stability.orderDependent).toContain('test-b');
    
    console.log('🔍 Detected order-dependent test:', report.stability.orderDependent);
  });

  it('should handle consistently failing tests', async () => {
    const consistentlyFailingTests: TestCase[] = [
      {
        id: 'always-pass',
        name: 'Always Pass',
        fn: () => {
          expect(true).toBe(true);
        }
      },
      {
        id: 'always-fail',
        name: 'Always Fail',
        fn: () => {
          throw new Error('This test always fails');
        }
      }
    ];

    const suite = createRandomizedSuite('Consistent Failure Suite', consistentlyFailingTests);
    const report = await randomizer.executeTestSuite(suite);

    expect(report.stability.consistentFailures).toContain('always-fail');
    expect(report.stability.consistentFailures).not.toContain('always-pass');
  });

  it('should detect intermittent failures', async () => {
    let callCount = 0;

    const intermittentTests: TestCase[] = [
      {
        id: 'stable-test',
        name: 'Stable Test',
        fn: () => {
          expect(true).toBe(true);
        }
      },
      {
        id: 'flaky-test',
        name: 'Flaky Test',
        fn: () => {
          callCount++;
          // Fail every other call to simulate flakiness
          if (callCount % 2 === 0) {
            throw new Error('Intermittent failure');
          }
        }
      }
    ];

    const suite = createRandomizedSuite('Flaky Suite', intermittentTests);
    const report = await randomizer.executeTestSuite(suite);

    expect(report.stability.intermittentFailures).toContain('flaky-test');
    expect(report.stability.intermittentFailures).not.toContain('stable-test');
  });

  it('should generate comprehensive reports', async () => {
    const simpleTests: TestCase[] = [
      {
        id: 'test-1',
        name: 'Test 1',
        fn: () => expect(1 + 1).toBe(2)
      },
      {
        id: 'test-2', 
        name: 'Test 2',
        fn: () => expect('hello').toContain('ell')
      }
    ];

    const suite = createRandomizedSuite('Simple Suite', simpleTests);
    const report = await randomizer.executeTestSuite(suite);
    const reportText = randomizer.generateReport(report);

    expect(reportText).toContain('Test Randomization Report');
    expect(reportText).toContain('Seed: test-seed-123');
    expect(reportText).toContain('Total Runs: 5');
    expect(reportText).toContain('Stability Analysis');
  });

  it('should support test isolation wrapper', async () => {
    let sideEffectCounter = 0;

    const testWithSideEffects = async () => {
      sideEffectCounter++;
      return sideEffectCounter;
    };

    const isolatedTest = withIsolation(testWithSideEffects);
    
    // The isolation wrapper should still allow the test to run
    const result = await isolatedTest();
    expect(result).toBe(1);
  });

  it('should handle test setup and teardown correctly', async () => {
    let setupCalled = false;
    let teardownCalled = false;

    const customSuite = {
      name: 'Custom Suite',
      cases: [
        {
          id: 'simple-test',
          name: 'Simple Test',
          fn: () => {
            expect(setupCalled).toBe(true);
            expect(teardownCalled).toBe(false);
          }
        }
      ],
      setup: async () => {
        setupCalled = true;
      },
      teardown: async () => {
        teardownCalled = true;
      }
    };

    await randomizer.executeTestSuite(customSuite);
    
    expect(setupCalled).toBe(true);
    expect(teardownCalled).toBe(true);
  });

  it('should respect isolation levels', () => {
    const strictRandomizer = new TestRandomizer({
      isolationLevel: 'strict',
      detectSideEffects: true
    });

    const basicRandomizer = new TestRandomizer({
      isolationLevel: 'basic',
      detectSideEffects: true
    });

    // Verify different randomizers have different behaviors
    expect(strictRandomizer['config'].isolationLevel).toBe('strict');
    expect(basicRandomizer['config'].isolationLevel).toBe('basic');
  });

  it('should handle edge cases gracefully', async () => {
    // Empty test suite
    const emptySuite = createRandomizedSuite('Empty Suite', []);
    const emptyReport = await randomizer.executeTestSuite(emptySuite);
    
    expect(emptyReport.configurations).toHaveLength(5); // Still runs iterations
    expect(emptyReport.stability.consistentFailures).toHaveLength(0);

    // Test with timeout
    const timeoutTest: TestCase = {
      id: 'timeout-test',
      name: 'Timeout Test',
      fn: async () => {
        await new Promise(resolve => setTimeout(resolve, 100));
        expect(true).toBe(true);
      },
      timeout: 5000
    };

    const timeoutSuite = createRandomizedSuite('Timeout Suite', [timeoutTest]);
    const timeoutReport = await randomizer.executeTestSuite(timeoutSuite);
    
    expect(timeoutReport.configurations[0].results[0].duration).toBeGreaterThan(50);
  });
});

// Example usage demonstration
describe('Test Randomization Demo', () => {
  it('should demonstrate order-dependent test detection', async () => {
    // This is a demonstration of how the randomizer catches order dependencies
    
    const demoRandomizer = new TestRandomizer({
      seed: 'demo-seed',
      iterations: 3,
      enableShuffling: true
    });

    let sharedState = { initialized: false };

    const orderDependentTests: TestCase[] = [
      {
        id: 'initializer',
        name: 'Initializer Test',
        fn: () => {
          sharedState.initialized = true;
          expect(true).toBe(true);
        }
      },
      {
        id: 'dependent',
        name: 'Dependent Test', 
        fn: () => {
          if (!sharedState.initialized) {
            throw new Error('Dependent test requires initialization');
          }
          expect(sharedState.initialized).toBe(true);
        }
      }
    ];

    const demoSuite = createRandomizedSuite('Demo Suite', orderDependentTests);
    const report = await demoRandomizer.executeTestSuite(demoSuite);

    console.log('📊 Demo Report:');
    console.log(`   Order dependent tests: ${report.stability.orderDependent.join(', ')}`);
    console.log(`   Configurations tested: ${report.configurations.length}`);
    
    // Reset shared state for clean test
    sharedState = { initialized: false };
  });
});