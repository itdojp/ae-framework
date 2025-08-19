/**
 * Bulkhead Isolation Pattern Implementation
 * Isolates critical resources to prevent cascading failures
 */

export interface BulkheadOptions {
  name: string;
  maxConcurrent: number;
  maxQueued: number;
  timeoutMs: number;
  onReject?: (reason: 'capacity' | 'timeout' | 'queue_full') => void;
}

export interface BulkheadStats {
  name: string;
  active: number;
  queued: number;
  maxConcurrent: number;
  maxQueued: number;
  totalExecuted: number;
  totalRejected: number;
  averageExecutionTime: number;
  rejectionReasons: Record<string, number>;
}

interface QueuedOperation {
  operation: () => Promise<any>;
  resolve: (value: any) => void;
  reject: (reason: any) => void;
  enqueuedAt: number;
  timeoutId: NodeJS.Timeout;
}

export class Bulkhead {
  private active: number = 0;
  private queue: QueuedOperation[] = [];
  private totalExecuted: number = 0;
  private totalRejected: number = 0;
  private executionTimes: number[] = [];
  private rejectionReasons: Record<string, number> = {
    capacity: 0,
    timeout: 0,
    queue_full: 0,
  };

  constructor(private options: BulkheadOptions) {
    this.validateOptions();
  }

  /**
   * Execute operation within bulkhead constraints
   */
  public async execute<T>(
    operation: () => Promise<T>,
    operationName: string = 'operation'
  ): Promise<T> {
    return new Promise<T>((resolve, reject) => {
      // Check if we can execute immediately
      if (this.active < this.options.maxConcurrent) {
        this.executeImmediately(operation, resolve, reject);
        return;
      }

      // Check if queue has space
      if (this.queue.length >= this.options.maxQueued) {
        this.handleRejection('queue_full', reject, `Queue full for bulkhead ${this.options.name}`);
        return;
      }

      // Add to queue with timeout
      let queuedOp: QueuedOperation;
      const timeoutId = setTimeout(() => {
        this.removeFromQueue(queuedOp);
        this.handleRejection('timeout', reject, `Operation timed out in queue for bulkhead ${this.options.name}`);
      }, this.options.timeoutMs);

      queuedOp = {
        operation,
        resolve,
        reject,
        enqueuedAt: Date.now(),
        timeoutId,
      };

      this.queue.push(queuedOp);
    });
  }

  /**
   * Execute operation immediately
   */
  private async executeImmediately<T>(
    operation: () => Promise<T>,
    resolve: (value: T) => void,
    reject: (reason: any) => void
  ): Promise<void> {
    this.active++;
    const startTime = Date.now();

    try {
      const result = await operation();
      const executionTime = Date.now() - startTime;
      
      this.recordExecution(executionTime);
      resolve(result);
    } catch (error) {
      reject(error);
    } finally {
      this.active--;
      this.processQueue();
    }
  }

  /**
   * Process queued operations
   */
  private processQueue(): void {
    if (this.queue.length === 0 || this.active >= this.options.maxConcurrent) {
      return;
    }

    const queuedOp = this.queue.shift();
    if (!queuedOp) return;

    clearTimeout(queuedOp.timeoutId);

    // Check if operation timed out while queued
    const queueTime = Date.now() - queuedOp.enqueuedAt;
    if (queueTime >= this.options.timeoutMs) {
      this.handleRejection('timeout', queuedOp.reject, `Operation timed out in queue (${queueTime}ms)`);
      this.processQueue(); // Try next in queue
      return;
    }

    this.executeImmediately(queuedOp.operation, queuedOp.resolve, queuedOp.reject);
  }

  /**
   * Remove operation from queue
   */
  private removeFromQueue(targetOp: QueuedOperation): void {
    const index = this.queue.indexOf(targetOp);
    if (index !== -1) {
      this.queue.splice(index, 1);
    }
  }

  /**
   * Handle operation rejection
   */
  private handleRejection(
    reason: 'capacity' | 'timeout' | 'queue_full',
    reject: (reason: any) => void,
    message: string
  ): void {
    this.totalRejected++;
    this.rejectionReasons[reason]++;
    this.options.onReject?.(reason);
    reject(new Error(message));
  }

  /**
   * Record successful execution
   */
  private recordExecution(executionTime: number): void {
    this.totalExecuted++;
    this.executionTimes.push(executionTime);
    
    // Keep only last 1000 execution times for average calculation
    if (this.executionTimes.length > 1000) {
      this.executionTimes.shift();
    }
  }

  /**
   * Get bulkhead statistics
   */
  public getStats(): BulkheadStats {
    const averageExecutionTime = this.executionTimes.length > 0
      ? this.executionTimes.reduce((sum, time) => sum + time, 0) / this.executionTimes.length
      : 0;

    return {
      name: this.options.name,
      active: this.active,
      queued: this.queue.length,
      maxConcurrent: this.options.maxConcurrent,
      maxQueued: this.options.maxQueued,
      totalExecuted: this.totalExecuted,
      totalRejected: this.totalRejected,
      averageExecutionTime,
      rejectionReasons: { ...this.rejectionReasons },
    };
  }

  /**
   * Reset bulkhead statistics
   */
  public reset(): void {
    // Clear queue
    this.queue.forEach(op => {
      clearTimeout(op.timeoutId);
      this.handleRejection('capacity', op.reject, `Bulkhead ${this.options.name} was reset`);
    });
    this.queue = [];

    // Reset counters
    this.totalExecuted = 0;
    this.totalRejected = 0;
    this.executionTimes = [];
    this.rejectionReasons = {
      capacity: 0,
      timeout: 0,
      queue_full: 0,
    };
  }

  /**
   * Get current load factor (0-1)
   */
  public getLoadFactor(): number {
    const totalLoad = this.active + this.queue.length;
    const totalCapacity = this.options.maxConcurrent + this.options.maxQueued;
    return totalLoad / totalCapacity;
  }

  /**
   * Check if bulkhead is healthy
   */
  public isHealthy(): boolean {
    const loadFactor = this.getLoadFactor();
    const rejectionRate = this.totalRejected / (this.totalExecuted + this.totalRejected);
    
    return loadFactor < 0.8 && rejectionRate < 0.1;
  }

  /**
   * Validate bulkhead options
   */
  private validateOptions(): void {
    if (this.options.maxConcurrent <= 0) {
      throw new Error('Max concurrent must be greater than 0');
    }
    if (this.options.maxQueued < 0) {
      throw new Error('Max queued must be greater than or equal to 0');
    }
    if (this.options.timeoutMs <= 0) {
      throw new Error('Timeout must be greater than 0');
    }
    if (!this.options.name || this.options.name.trim() === '') {
      throw new Error('Bulkhead name is required');
    }
  }
}

/**
 * Bulkhead Manager for managing multiple isolated bulkheads
 */
export class BulkheadManager {
  private bulkheads: Map<string, Bulkhead> = new Map();

  /**
   * Create or get a bulkhead
   */
  public getBulkhead(options: BulkheadOptions): Bulkhead {
    if (!this.bulkheads.has(options.name)) {
      this.bulkheads.set(options.name, new Bulkhead(options));
    }
    return this.bulkheads.get(options.name)!;
  }

  /**
   * Execute operation in named bulkhead
   */
  public async executeInBulkhead<T>(
    bulkheadName: string,
    operation: () => Promise<T>,
    operationName?: string
  ): Promise<T> {
    const bulkhead = this.bulkheads.get(bulkheadName);
    if (!bulkhead) {
      throw new Error(`Bulkhead ${bulkheadName} not found`);
    }

    return bulkhead.execute(operation, operationName);
  }

  /**
   * Get all bulkhead statistics
   */
  public getAllStats(): Record<string, BulkheadStats> {
    const stats: Record<string, BulkheadStats> = {};
    
    for (const [name, bulkhead] of this.bulkheads) {
      stats[name] = bulkhead.getStats();
    }
    
    return stats;
  }

  /**
   * Get system health across all bulkheads
   */
  public getSystemHealth(): {
    healthy: boolean;
    totalBulkheads: number;
    healthyBulkheads: number;
    totalActive: number;
    totalQueued: number;
    averageLoadFactor: number;
  } {
    const bulkheadArray = Array.from(this.bulkheads.values());
    const healthyBulkheads = bulkheadArray.filter(b => b.isHealthy()).length;
    const totalActive = bulkheadArray.reduce((sum, b) => sum + b.getStats().active, 0);
    const totalQueued = bulkheadArray.reduce((sum, b) => sum + b.getStats().queued, 0);
    const averageLoadFactor = bulkheadArray.length > 0
      ? bulkheadArray.reduce((sum, b) => sum + b.getLoadFactor(), 0) / bulkheadArray.length
      : 0;

    return {
      healthy: healthyBulkheads === bulkheadArray.length,
      totalBulkheads: bulkheadArray.length,
      healthyBulkheads,
      totalActive,
      totalQueued,
      averageLoadFactor,
    };
  }

  /**
   * Reset all bulkheads
   */
  public resetAll(): void {
    for (const bulkhead of this.bulkheads.values()) {
      bulkhead.reset();
    }
  }

  /**
   * Remove a bulkhead
   */
  public removeBulkhead(name: string): boolean {
    const bulkhead = this.bulkheads.get(name);
    if (bulkhead) {
      bulkhead.reset();
      this.bulkheads.delete(name);
      return true;
    }
    return false;
  }

  /**
   * Get bulkhead names
   */
  public getBulkheadNames(): string[] {
    return Array.from(this.bulkheads.keys());
  }
}