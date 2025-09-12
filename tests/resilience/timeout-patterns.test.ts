/**
 * Tests for Timeout Patterns
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  TimeoutWrapper,
  AdaptiveTimeout,
  HierarchicalTimeout,
  TimeoutManager,
  TimeoutError,
  type TimeoutOptions,
  type AdaptiveTimeoutOptions,
} from '../../src/resilience/timeout-patterns.js';

describe('TimeoutWrapper', () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Basic Timeout', () => {
    it('should execute operation successfully within timeout', async () => {
      const options: TimeoutOptions = { timeoutMs: 1000 };
      const wrapper = new TimeoutWrapper(options);
      const operation = vi.fn().mockResolvedValue('success');

      const result = await wrapper.execute(operation);

      expect(result).toBe('success');
      expect(operation).toHaveBeenCalledTimes(1);
    });

    it('should timeout long-running operations', async () => {
      const options: TimeoutOptions = { timeoutMs: 100 };
      const wrapper = new TimeoutWrapper(options);
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(resolve, 200))
      );

      const promise = wrapper.execute(operation, 'slow-operation');
      
      // Fast-forward past timeout
      vi.advanceTimersByTime(101);

      await expect(promise).rejects.toThrow(TimeoutError);
      await expect(promise).rejects.toThrow("Operation 'slow-operation' timed out after 100ms");
    });

    it('should call onTimeout callback', async () => {
      const onTimeout = vi.fn();
      const options: TimeoutOptions = { 
        timeoutMs: 100,
        onTimeout,
      };
      const wrapper = new TimeoutWrapper(options);
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(resolve, 200))
      );

      const promise = wrapper.execute(operation);
      vi.advanceTimersByTime(101);

      await expect(promise).rejects.toThrow(TimeoutError);
      expect(onTimeout).toHaveBeenCalledWith(100);
    });

    it('should handle AbortController', async () => {
      const abortController = new AbortController();
      const options: TimeoutOptions = { 
        timeoutMs: 100,
        abortController,
      };
      const wrapper = new TimeoutWrapper(options);
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(resolve, 200))
      );

      const promise = wrapper.execute(operation);
      vi.advanceTimersByTime(101);

      await expect(promise).rejects.toThrow(TimeoutError);
      expect(abortController.signal.aborted).toBe(true);
    });
  });

  describe('Validation', () => {
    it('should validate timeout options', () => {
      expect(() => new TimeoutWrapper({ timeoutMs: 0 }))
        .toThrow('Timeout must be greater than 0');

      expect(() => new TimeoutWrapper({ timeoutMs: -100 }))
        .toThrow('Timeout must be greater than 0');
    });
  });
});

describe('TimeoutError', () => {
  it('should have correct properties', () => {
    const error = new TimeoutError('Test timeout', 1000, 1050);

    expect(error.name).toBe('TimeoutError');
    expect(error.message).toBe('Test timeout');
    expect(error.timeoutMs).toBe(1000);
    expect(error.actualDuration).toBe(1050);
    expect(error instanceof Error).toBe(true);
    expect(error instanceof TimeoutError).toBe(true);
  });
});

describe('AdaptiveTimeout', () => {
  let adaptiveTimeout: AdaptiveTimeout;
  const defaultOptions: AdaptiveTimeoutOptions = {
    timeoutMs: 1000,
    baseTimeoutMs: 500,
    maxTimeoutMs: 2000,
    minTimeoutMs: 100,
    adaptationFactor: 0.1,
    windowSize: 10,
  };

  beforeEach(() => {
    vi.useFakeTimers();
    adaptiveTimeout = new AdaptiveTimeout(defaultOptions);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Basic Adaptation', () => {
    it('should start with base timeout', () => {
      expect(adaptiveTimeout.getCurrentTimeout()).toBe(500);
    });

    it('should adapt timeout based on execution patterns', async () => {
      // Simulate fast operations
      const fastOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('fast'), 50))
      );

      // Execute multiple fast operations
      for (let i = 0; i < 10; i++) {
        const promise = adaptiveTimeout.execute(fastOperation);
        vi.advanceTimersByTime(60);
        await promise;
      }

      const stats = adaptiveTimeout.getStats();
      expect(stats.successfulOperations).toBe(10);
      expect(stats.timeouts).toBe(0);
      expect(stats.averageExecutionTime).toBeLessThan(100);

      // Timeout should adapt downward for consistently fast operations
      expect(adaptiveTimeout.getCurrentTimeout()).toBeLessThanOrEqual(500);
    });

    it('should increase timeout after timeouts occur', async () => {
      const slowOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('slow'), 600))
      );

      // This should timeout with base timeout of 500ms
      const promise = adaptiveTimeout.execute(slowOperation);
      vi.advanceTimersByTime(501);

      await expect(promise).rejects.toThrow(TimeoutError);

      const stats = adaptiveTimeout.getStats();
      expect(stats.timeouts).toBe(1);
      
      // Timeout should increase after a timeout
      expect(adaptiveTimeout.getCurrentTimeout()).toBeGreaterThan(500);
    });
  });

  describe('Statistics', () => {
    it('should track comprehensive statistics', async () => {
      const operation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('success'), 100))
      );

      for (let i = 0; i < 3; i++) {
        const promise = adaptiveTimeout.execute(operation);
        vi.advanceTimersByTime(110);
        await promise;
      }

      const stats = adaptiveTimeout.getStats();
      expect(stats.totalOperations).toBe(3);
      expect(stats.successfulOperations).toBe(3);
      expect(stats.timeouts).toBe(0);
      expect(stats.timeoutRate).toBe(0);
      // Allow a small range to account for fake timers stepping beyond exact delay
      expect(stats.averageExecutionTime).toBeGreaterThanOrEqual(100);
      expect(stats.averageExecutionTime).toBeLessThanOrEqual(120);
    });

    it('should calculate timeout rate correctly', async () => {
      const fastOperation = vi.fn().mockResolvedValue('fast');
      const slowOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('slow'), 600))
      );

      // One success
      await adaptiveTimeout.execute(fastOperation);

      // One timeout
      const promise = adaptiveTimeout.execute(slowOperation);
      vi.advanceTimersByTime(501);
      await expect(promise).rejects.toThrow(TimeoutError);

      const stats = adaptiveTimeout.getStats();
      expect(stats.timeoutRate).toBe(0.5); // 1 timeout out of 2 operations
    });
  });

  describe('Manual Control', () => {
    it('should allow manual timeout setting', () => {
      adaptiveTimeout.setTimeout(800);
      expect(adaptiveTimeout.getCurrentTimeout()).toBe(800);

      // Should respect min/max bounds
      adaptiveTimeout.setTimeout(50);
      expect(adaptiveTimeout.getCurrentTimeout()).toBe(100); // Capped at min

      adaptiveTimeout.setTimeout(3000);
      expect(adaptiveTimeout.getCurrentTimeout()).toBe(2000); // Capped at max
    });

    it('should reset to base timeout', async () => {
      // Change timeout through adaptation
      const slowOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('slow'), 600))
      );

      const promise = adaptiveTimeout.execute(slowOperation);
      vi.advanceTimersByTime(501);
      await expect(promise).rejects.toThrow(TimeoutError);

      expect(adaptiveTimeout.getCurrentTimeout()).toBeGreaterThan(500);

      adaptiveTimeout.reset();

      expect(adaptiveTimeout.getCurrentTimeout()).toBe(500);
      expect(adaptiveTimeout.getStats().totalOperations).toBe(0);
    });
  });

  describe('Validation', () => {
    it('should validate adaptive timeout options', () => {
      expect(() => new AdaptiveTimeout({
        ...defaultOptions,
        baseTimeoutMs: 0,
      })).toThrow('Base timeout must be greater than 0');

      expect(() => new AdaptiveTimeout({
        ...defaultOptions,
        maxTimeoutMs: 50,
        minTimeoutMs: 100,
      })).toThrow('Max timeout must be greater than min timeout');

      expect(() => new AdaptiveTimeout({
        ...defaultOptions,
        baseTimeoutMs: 50,
        minTimeoutMs: 100,
      })).toThrow('Base timeout must be between min and max timeout');

      expect(() => new AdaptiveTimeout({
        ...defaultOptions,
        adaptationFactor: 1.5,
      })).toThrow('Adaptation factor must be between 0 and 1');

      expect(() => new AdaptiveTimeout({
        ...defaultOptions,
        windowSize: 0,
      })).toThrow('Window size must be greater than 0');
    });
  });
});

describe('HierarchicalTimeout', () => {
  let hierarchicalTimeout: HierarchicalTimeout;

  beforeEach(() => {
    vi.useFakeTimers();
    hierarchicalTimeout = new HierarchicalTimeout();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Hierarchical Operations', () => {
    it('should execute simple operation', async () => {
      const operation = vi.fn().mockResolvedValue('success');

      const result = await hierarchicalTimeout.executeWithHierarchy(
        operation,
        'op1',
        1000
      );

      expect(result).toBe('success');
      expect(hierarchicalTimeout.getActiveOperations()).toEqual([]);
    });

    it('should track active operations', async () => {
      const longOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('success'), 500))
      );

      const promise = hierarchicalTimeout.executeWithHierarchy(
        longOperation,
        'long-op',
        1000
      );

      expect(hierarchicalTimeout.getActiveOperations()).toContain('long-op');
      expect(hierarchicalTimeout.isOperationActive('long-op')).toBe(true);

      vi.advanceTimersByTime(600);
      await promise;

      expect(hierarchicalTimeout.getActiveOperations()).toEqual([]);
      expect(hierarchicalTimeout.isOperationActive('long-op')).toBe(false);
    });

    it('should timeout hierarchical operations', async () => {
      const slowOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('slow'), 2000))
      );

      const promise = hierarchicalTimeout.executeWithHierarchy(
        slowOperation,
        'slow-op',
        500
      );

      vi.advanceTimersByTime(501);

      await expect(promise).rejects.toThrow(TimeoutError);
      expect(hierarchicalTimeout.getActiveOperations()).toEqual([]);
    });

    it('should handle nested operations', async () => {
      const parentOperation = async () => {
        return hierarchicalTimeout.executeWithHierarchy(
          async () => {
            await new Promise(resolve => setTimeout(resolve, 100));
            return 'child-success';
          },
          'child-op',
          500,
          'parent-op'
        );
      };

      const promise = hierarchicalTimeout.executeWithHierarchy(
        parentOperation,
        'parent-op',
        1000
      );

      vi.advanceTimersByTime(150);
      const result = await promise;

      expect(result).toBe('child-success');
    });
  });

  describe('Cleanup Operations', () => {
    it('should cancel all active operations', async () => {
      const longOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('success'), 1000))
      );

      hierarchicalTimeout.executeWithHierarchy(longOperation, 'op1', 2000);
      hierarchicalTimeout.executeWithHierarchy(longOperation, 'op2', 2000);

      expect(hierarchicalTimeout.getActiveOperations()).toEqual(['op1', 'op2']);

      hierarchicalTimeout.cancelAll();

      expect(hierarchicalTimeout.getActiveOperations()).toEqual([]);
    });
  });
});

describe('TimeoutManager', () => {
  let timeoutManager: TimeoutManager;

  beforeEach(() => {
    vi.useFakeTimers();
    timeoutManager = new TimeoutManager();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Adaptive Timeout Management', () => {
    it('should create and manage adaptive timeouts', () => {
      const options: AdaptiveTimeoutOptions = {
        timeoutMs: 1000,
        baseTimeoutMs: 500,
        maxTimeoutMs: 2000,
        minTimeoutMs: 100,
        adaptationFactor: 0.1,
        windowSize: 10,
      };

      const timeout1 = timeoutManager.getAdaptiveTimeout('api-timeout', options);
      const timeout2 = timeoutManager.getAdaptiveTimeout('api-timeout', options);

      expect(timeout1).toBe(timeout2); // Should return same instance
    });

    it('should execute with adaptive timeout', async () => {
      const options: AdaptiveTimeoutOptions = {
        timeoutMs: 1000,
        baseTimeoutMs: 500,
        maxTimeoutMs: 2000,
        minTimeoutMs: 100,
        adaptationFactor: 0.1,
        windowSize: 10,
      };

      timeoutManager.getAdaptiveTimeout('test-timeout', options);

      const operation = vi.fn().mockResolvedValue('success');
      const result = await timeoutManager.executeWithAdaptiveTimeout(
        'test-timeout',
        operation,
        'test-op'
      );

      expect(result).toBe('success');
    });

    it('should throw error for non-existent adaptive timeout', async () => {
      const operation = vi.fn().mockResolvedValue('success');

      await expect(timeoutManager.executeWithAdaptiveTimeout('non-existent', operation))
        .rejects.toThrow("Adaptive timeout 'non-existent' not found");
    });
  });

  describe('Hierarchical Timeout Management', () => {
    it('should execute with hierarchical timeout', async () => {
      const operation = vi.fn().mockResolvedValue('success');

      const result = await timeoutManager.executeWithHierarchicalTimeout(
        operation,
        'test-op',
        1000
      );

      expect(result).toBe('success');
    });

    it('should track hierarchical operations', async () => {
      const longOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('success'), 500))
      );

      const promise = timeoutManager.executeWithHierarchicalTimeout(
        longOperation,
        'long-op',
        1000
      );

      expect(timeoutManager.getActiveHierarchicalOperations()).toContain('long-op');

      vi.advanceTimersByTime(600);
      await promise;

      expect(timeoutManager.getActiveHierarchicalOperations()).toEqual([]);
    });
  });

  describe('Statistics and Management', () => {
    it('should provide all timeout statistics', async () => {
      const options: AdaptiveTimeoutOptions = {
        timeoutMs: 1000,
        baseTimeoutMs: 500,
        maxTimeoutMs: 2000,
        minTimeoutMs: 100,
        adaptationFactor: 0.1,
        windowSize: 10,
      };

      const adaptiveTimeout = timeoutManager.getAdaptiveTimeout('stats-timeout', options);
      
      const operation = vi.fn().mockResolvedValue('success');
      await adaptiveTimeout.execute(operation);

      const allStats = timeoutManager.getAllStats();
      
      expect(allStats['stats-timeout']).toBeDefined();
      expect(allStats['stats-timeout'].totalOperations).toBe(1);
    });

    it('should reset all timeout managers', async () => {
      const options: AdaptiveTimeoutOptions = {
        timeoutMs: 1000,
        baseTimeoutMs: 500,
        maxTimeoutMs: 2000,
        minTimeoutMs: 100,
        adaptationFactor: 0.1,
        windowSize: 10,
      };

      const adaptiveTimeout = timeoutManager.getAdaptiveTimeout('reset-timeout', options);
      
      const operation = vi.fn().mockResolvedValue('success');
      await adaptiveTimeout.execute(operation);

      expect(adaptiveTimeout.getStats().totalOperations).toBe(1);

      timeoutManager.resetAll();

      expect(adaptiveTimeout.getStats().totalOperations).toBe(0);
    });

    it('should cancel all operations', async () => {
      const longOperation = vi.fn().mockImplementation(() =>
        new Promise(resolve => setTimeout(() => resolve('success'), 1000))
      );

      timeoutManager.executeWithHierarchicalTimeout(longOperation, 'op1', 2000);
      
      expect(timeoutManager.getActiveHierarchicalOperations()).toContain('op1');

      timeoutManager.cancelAllOperations();

      expect(timeoutManager.getActiveHierarchicalOperations()).toEqual([]);
    });
  });
});
