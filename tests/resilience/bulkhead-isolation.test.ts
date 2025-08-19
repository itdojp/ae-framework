/**
 * Tests for Bulkhead Isolation Pattern
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { Bulkhead, BulkheadManager, type BulkheadOptions } from '../../src/resilience/bulkhead-isolation.js';

describe('Bulkhead', () => {
  let bulkhead: Bulkhead;
  const defaultOptions: BulkheadOptions = {
    name: 'test-bulkhead',
    maxConcurrent: 2,
    maxQueued: 3,
    timeoutMs: 1000,
  };

  beforeEach(() => {
    vi.useFakeTimers();
    bulkhead = new Bulkhead(defaultOptions);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Basic Execution', () => {
    it('should execute operations within concurrency limit', async () => {
      const operation = vi.fn().mockResolvedValue('success');

      const result = await bulkhead.execute(operation);

      expect(result).toBe('success');
      expect(operation).toHaveBeenCalledTimes(1);
      expect(bulkhead.getStats().active).toBe(0);
      expect(bulkhead.getStats().totalExecuted).toBe(1);
    });

    it('should handle concurrent operations up to limit', async () => {
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 100))
      );

      const promises = [
        bulkhead.execute(operation),
        bulkhead.execute(operation),
      ];

      expect(bulkhead.getStats().active).toBe(2);

      await vi.runAllTimersAsync();
      const results = await Promise.all(promises);

      expect(results).toEqual(['success', 'success']);
      expect(bulkhead.getStats().totalExecuted).toBe(2);
    });

    it('should queue operations when at capacity', async () => {
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 100))
      );

      // Fill capacity
      const promise1 = bulkhead.execute(operation);
      const promise2 = bulkhead.execute(operation);
      
      expect(bulkhead.getStats().active).toBe(2);

      // This should be queued
      const promise3 = bulkhead.execute(operation);
      
      expect(bulkhead.getStats().queued).toBe(1);

      await vi.runAllTimersAsync();
      const results = await Promise.all([promise1, promise2, promise3]);

      expect(results).toEqual(['success', 'success', 'success']);
      expect(bulkhead.getStats().totalExecuted).toBe(3);
    });
  });

  describe('Queue Management', () => {
    it('should reject operations when queue is full', async () => {
      const longOperation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 1000))
      );

      // Fill capacity and queue
      const promises = [];
      for (let i = 0; i < 5; i++) {
        promises.push(bulkhead.execute(longOperation));
      }

      expect(bulkhead.getStats().active).toBe(2);
      expect(bulkhead.getStats().queued).toBe(3);

      // This should be rejected
      await expect(bulkhead.execute(longOperation)).rejects.toThrow('Queue full');
      expect(bulkhead.getStats().totalRejected).toBe(1);
    });

    it('should timeout queued operations', async () => {
      const longOperation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 2000))
      );

      // Fill capacity
      bulkhead.execute(longOperation);
      bulkhead.execute(longOperation);

      // Queue operation that will timeout
      const queuedPromise = bulkhead.execute(longOperation);

      expect(bulkhead.getStats().queued).toBe(1);

      // Fast-forward past timeout
      vi.advanceTimersByTime(1001);

      await expect(queuedPromise).rejects.toThrow('timed out in queue');
      expect(bulkhead.getStats().totalRejected).toBe(1);
    });
  });

  describe('Statistics', () => {
    it('should track execution statistics', async () => {
      const fastOperation = vi.fn().mockResolvedValue('fast');
      const slowOperation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('slow'), 200))
      );

      await bulkhead.execute(fastOperation);
      
      const slowPromise = bulkhead.execute(slowOperation);
      await vi.runAllTimersAsync();
      await slowPromise;

      const stats = bulkhead.getStats();
      expect(stats.totalExecuted).toBe(2);
      expect(stats.averageExecutionTime).toBeGreaterThan(0);
    });

    it('should calculate load factor correctly', () => {
      expect(bulkhead.getLoadFactor()).toBe(0);

      // Add one active operation
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 100))
      );
      
      bulkhead.execute(operation);
      expect(bulkhead.getLoadFactor()).toBe(0.2); // 1 / (2 + 3)
    });

    it('should assess health correctly', async () => {
      expect(bulkhead.isHealthy()).toBe(true);

      // Fill most of capacity to make unhealthy
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 1000))
      );

      for (let i = 0; i < 4; i++) {
        bulkhead.execute(operation).catch(() => {}); // Ignore rejections
      }

      expect(bulkhead.isHealthy()).toBe(false);
    });
  });

  describe('Reset Functionality', () => {
    it('should reset statistics and cancel queued operations', async () => {
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 1000))
      );

      // Add some operations
      bulkhead.execute(operation).catch(() => {});
      bulkhead.execute(operation).catch(() => {});
      bulkhead.execute(operation).catch(() => {});

      expect(bulkhead.getStats().active).toBe(2);
      expect(bulkhead.getStats().queued).toBe(1);

      bulkhead.reset();

      const stats = bulkhead.getStats();
      expect(stats.active).toBe(0); // Active operations continue but aren't tracked
      expect(stats.queued).toBe(0);
      expect(stats.totalExecuted).toBe(0);
      expect(stats.totalRejected).toBe(1); // Queued operation was rejected
    });
  });

  describe('Validation', () => {
    it('should validate options', () => {
      expect(() => new Bulkhead({
        name: '',
        maxConcurrent: 2,
        maxQueued: 3,
        timeoutMs: 1000,
      })).toThrow('Bulkhead name is required');

      expect(() => new Bulkhead({
        name: 'test',
        maxConcurrent: 0,
        maxQueued: 3,
        timeoutMs: 1000,
      })).toThrow('Max concurrent must be greater than 0');

      expect(() => new Bulkhead({
        name: 'test',
        maxConcurrent: 2,
        maxQueued: -1,
        timeoutMs: 1000,
      })).toThrow('Max queued must be greater than or equal to 0');

      expect(() => new Bulkhead({
        name: 'test',
        maxConcurrent: 2,
        maxQueued: 3,
        timeoutMs: 0,
      })).toThrow('Timeout must be greater than 0');
    });
  });

  describe('Callbacks', () => {
    it('should call onReject callback', async () => {
      const onReject = vi.fn();
      const bulkheadWithCallback = new Bulkhead({
        ...defaultOptions,
        onReject,
      });

      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 1000))
      );

      // Fill capacity and queue
      for (let i = 0; i < 5; i++) {
        bulkheadWithCallback.execute(operation).catch(() => {});
      }

      // This should trigger callback
      await expect(bulkheadWithCallback.execute(operation)).rejects.toThrow();
      
      expect(onReject).toHaveBeenCalledWith('queue_full');
    });
  });
});

describe('BulkheadManager', () => {
  let manager: BulkheadManager;

  beforeEach(() => {
    vi.useFakeTimers();
    manager = new BulkheadManager();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Bulkhead Management', () => {
    it('should create and retrieve bulkheads', () => {
      const options: BulkheadOptions = {
        name: 'test-bulkhead',
        maxConcurrent: 2,
        maxQueued: 3,
        timeoutMs: 1000,
      };

      const bulkhead1 = manager.getBulkhead(options);
      const bulkhead2 = manager.getBulkhead(options);

      expect(bulkhead1).toBe(bulkhead2); // Should return same instance
      expect(manager.getBulkheadNames()).toContain('test-bulkhead');
    });

    it('should execute operations in named bulkheads', async () => {
      const options: BulkheadOptions = {
        name: 'api-bulkhead',
        maxConcurrent: 1,
        maxQueued: 1,
        timeoutMs: 1000,
      };

      manager.getBulkhead(options);

      const operation = vi.fn().mockResolvedValue('success');
      const result = await manager.executeInBulkhead('api-bulkhead', operation);

      expect(result).toBe('success');
      expect(operation).toHaveBeenCalledTimes(1);
    });

    it('should throw error for non-existent bulkhead', async () => {
      const operation = vi.fn().mockResolvedValue('success');

      await expect(manager.executeInBulkhead('non-existent', operation))
        .rejects.toThrow('Bulkhead non-existent not found');
    });
  });

  describe('System Health', () => {
    it('should provide system health overview', () => {
      const options1: BulkheadOptions = {
        name: 'bulkhead-1',
        maxConcurrent: 2,
        maxQueued: 2,
        timeoutMs: 1000,
      };

      const options2: BulkheadOptions = {
        name: 'bulkhead-2',
        maxConcurrent: 3,
        maxQueued: 3,
        timeoutMs: 1000,
      };

      manager.getBulkhead(options1);
      manager.getBulkhead(options2);

      const health = manager.getSystemHealth();
      
      expect(health.totalBulkheads).toBe(2);
      expect(health.healthyBulkheads).toBe(2);
      expect(health.healthy).toBe(true);
      expect(health.totalActive).toBe(0);
      expect(health.totalQueued).toBe(0);
    });

    it('should detect unhealthy system', async () => {
      const options: BulkheadOptions = {
        name: 'overloaded-bulkhead',
        maxConcurrent: 1,
        maxQueued: 1,
        timeoutMs: 1000,
      };

      const bulkhead = manager.getBulkhead(options);

      // Overload the bulkhead
      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(() => resolve('success'), 2000))
      );

      bulkhead.execute(operation).catch(() => {});
      bulkhead.execute(operation).catch(() => {});

      const health = manager.getSystemHealth();
      expect(health.healthy).toBe(false);
    });
  });

  describe('Statistics', () => {
    it('should provide all bulkhead statistics', async () => {
      const options: BulkheadOptions = {
        name: 'stats-bulkhead',
        maxConcurrent: 2,
        maxQueued: 2,
        timeoutMs: 1000,
      };

      const bulkhead = manager.getBulkhead(options);
      
      const operation = vi.fn().mockResolvedValue('success');
      await bulkhead.execute(operation);

      const allStats = manager.getAllStats();
      
      expect(allStats['stats-bulkhead']).toBeDefined();
      expect(allStats['stats-bulkhead'].totalExecuted).toBe(1);
    });
  });

  describe('Cleanup', () => {
    it('should reset all bulkheads', async () => {
      const options: BulkheadOptions = {
        name: 'reset-bulkhead',
        maxConcurrent: 1,
        maxQueued: 1,
        timeoutMs: 1000,
      };

      const bulkhead = manager.getBulkhead(options);
      
      const operation = vi.fn().mockResolvedValue('success');
      await bulkhead.execute(operation);

      expect(bulkhead.getStats().totalExecuted).toBe(1);

      manager.resetAll();

      expect(bulkhead.getStats().totalExecuted).toBe(0);
    });

    it('should remove bulkheads', () => {
      const options: BulkheadOptions = {
        name: 'removable-bulkhead',
        maxConcurrent: 1,
        maxQueued: 1,
        timeoutMs: 1000,
      };

      manager.getBulkhead(options);
      expect(manager.getBulkheadNames()).toContain('removable-bulkhead');

      const removed = manager.removeBulkhead('removable-bulkhead');
      expect(removed).toBe(true);
      expect(manager.getBulkheadNames()).not.toContain('removable-bulkhead');

      const removedAgain = manager.removeBulkhead('removable-bulkhead');
      expect(removedAgain).toBe(false);
    });
  });
});