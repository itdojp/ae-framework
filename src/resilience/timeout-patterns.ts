/**
 * Advanced Timeout Patterns Implementation
 * Provides sophisticated timeout handling strategies
 */

export interface TimeoutOptions {
  timeoutMs: number;
  onTimeout?: (duration: number) => void;
  abortController?: AbortController;
  timeoutMessage?: string;
}

export interface AdaptiveTimeoutOptions extends TimeoutOptions {
  baseTimeoutMs: number;
  maxTimeoutMs: number;
  minTimeoutMs: number;
  adaptationFactor: number;
  windowSize: number;
}

export interface TimeoutStats {
  totalOperations: number;
  timeouts: number;
  successfulOperations: number;
  averageExecutionTime: number;
  timeoutRate: number;
  currentTimeoutMs: number;
}

/**
 * Basic timeout wrapper for operations
 */
export class TimeoutWrapper {
  constructor(private options: TimeoutOptions) {
    this.validateOptions();
  }

  /**
   * Execute operation with timeout
   */
  public async execute<T>(
    operation: () => Promise<T>,
    operationName: string = 'operation'
  ): Promise<T> {
    const startTime = Date.now();

    let timeoutId: NodeJS.Timeout | undefined;
    const timeoutPromise = new Promise<never>((_, reject) => {
      timeoutId = setTimeout(() => {
        const duration = Date.now() - startTime;
        this.options.onTimeout?.(duration);
        if (this.options.abortController) {
          this.options.abortController.abort();
        }
        const message = this.options.timeoutMessage ||
          `Operation '${operationName}' timed out after ${this.options.timeoutMs}ms`;
        reject(new TimeoutError(message, this.options.timeoutMs, duration));
      }, this.options.timeoutMs);
    });

    const opPromise = operation();

    // When operation settles, clear the timeout
    opPromise.finally(() => {
      if (timeoutId) {
        clearTimeout(timeoutId);
        timeoutId = undefined;
      }
    });

    return Promise.race([opPromise, timeoutPromise]);
  }

  private validateOptions(): void {
    if (this.options.timeoutMs <= 0) {
      throw new Error('Timeout must be greater than 0');
    }
  }
}

/**
 * Custom timeout error
 */
export class TimeoutError extends Error {
  public override readonly name = 'TimeoutError';
  
  constructor(
    message: string,
    public readonly timeoutMs: number,
    public readonly actualDuration: number
  ) {
    super(message);
    Object.setPrototypeOf(this, TimeoutError.prototype);
  }
}

/**
 * Adaptive timeout that adjusts based on historical performance
 */
export class AdaptiveTimeout {
  private executionTimes: number[] = [];
  private totalOperations: number = 0;
  private timeouts: number = 0;
  private successfulOperations: number = 0;
  private currentTimeoutMs: number;

  constructor(private options: AdaptiveTimeoutOptions) {
    this.validateOptions();
    this.currentTimeoutMs = options.baseTimeoutMs;
  }

  /**
   * Execute operation with adaptive timeout
   */
  public async execute<T>(
    operation: () => Promise<T>,
    operationName: string = 'operation'
  ): Promise<T> {
    this.totalOperations++;
    const startTime = Date.now();

    try {
      const twOptions: TimeoutOptions = {
        timeoutMs: this.currentTimeoutMs,
        onTimeout: (duration) => {
          this.timeouts++;
          this.options.onTimeout?.(duration);
          this.adaptTimeout(false);
        },
      };
      if (this.options.abortController !== undefined) {
        twOptions.abortController = this.options.abortController;
      }
      if (this.options.timeoutMessage !== undefined) {
        twOptions.timeoutMessage = this.options.timeoutMessage;
      }

      const timeoutWrapper = new TimeoutWrapper(twOptions);

      // Capture end time at operation resolution to avoid drift from extra timer advances
      let endAt = 0;
      const timedOperation = async () => {
        const r = await operation();
        endAt = Date.now();
        return r;
      };

      const result = await timeoutWrapper.execute(timedOperation, operationName);
      
      const executionTime = (endAt || Date.now()) - startTime;
      this.recordSuccess(executionTime);
      
      return result;
    } catch (error) {
      if (error instanceof TimeoutError) {
        throw error;
      }
      
      // Non-timeout error
      const executionTime = Date.now() - startTime;
      this.recordSuccess(executionTime);
      throw error;
    }
  }

  /**
   * Record successful operation and adapt timeout
   */
  private recordSuccess(executionTime: number): void {
    this.successfulOperations++;
    this.executionTimes.push(executionTime);
    
    // Keep only recent executions for adaptation
    if (this.executionTimes.length > this.options.windowSize) {
      this.executionTimes.shift();
    }
    
    this.adaptTimeout(true);
  }

  /**
   * Adapt timeout based on recent performance
   */
  private adaptTimeout(success: boolean): void {
    // If a timeout occurred, adapt immediately even without history
    if (!success) {
      this.currentTimeoutMs = Math.min(
        Math.max(
          Math.floor(this.currentTimeoutMs * (1 + this.options.adaptationFactor)),
          this.options.minTimeoutMs
        ),
        this.options.maxTimeoutMs
      );
      return;
    }

    if (this.executionTimes.length < 5) {
      // Not enough data for adaptation on success
      return;
    }

    const recentExecutions = this.executionTimes.slice(-this.options.windowSize);
    const averageTime = recentExecutions.reduce((sum, time) => sum + time, 0) / recentExecutions.length;
    const maxTime = Math.max(...recentExecutions);
    const p95Time = this.calculatePercentile(recentExecutions, 0.95);

    if (success) {
      // Operation succeeded, potentially decrease timeout if we're being too conservative
      const targetTimeout = Math.max(p95Time * 1.5, averageTime * 2);
      
      if (this.currentTimeoutMs > targetTimeout * 1.2) {
        this.currentTimeoutMs = Math.max(
          this.currentTimeoutMs * (1 - this.options.adaptationFactor),
          this.options.minTimeoutMs
        );
      }
    } else {
      // Timeout occurred, increase timeout
      const targetTimeout = Math.max(maxTime * 1.5, p95Time * 2);
      this.currentTimeoutMs = Math.min(
        Math.max(targetTimeout, this.currentTimeoutMs * (1 + this.options.adaptationFactor)),
        this.options.maxTimeoutMs
      );
    }
  }

  /**
   * Calculate percentile from sorted array
   */
  private calculatePercentile(values: number[], percentile: number): number {
    const sorted = [...values].sort((a, b) => a - b);
    const index = Math.ceil(sorted.length * percentile) - 1;
    return sorted[Math.max(0, index)] ?? sorted[0] ?? 0;
  }

  /**
   * Get timeout statistics
   */
  public getStats(): TimeoutStats {
    const averageExecutionTime = this.executionTimes.length > 0
      ? this.executionTimes.reduce((sum, time) => sum + time, 0) / this.executionTimes.length
      : 0;

    return {
      totalOperations: this.totalOperations,
      timeouts: this.timeouts,
      successfulOperations: this.successfulOperations,
      averageExecutionTime,
      timeoutRate: this.totalOperations > 0 ? this.timeouts / this.totalOperations : 0,
      currentTimeoutMs: this.currentTimeoutMs,
    };
  }

  /**
   * Reset statistics and timeout to base value
   */
  public reset(): void {
    this.executionTimes = [];
    this.totalOperations = 0;
    this.timeouts = 0;
    this.successfulOperations = 0;
    this.currentTimeoutMs = this.options.baseTimeoutMs;
  }

  /**
   * Get current timeout value
   */
  public getCurrentTimeout(): number {
    return this.currentTimeoutMs;
  }

  /**
   * Manually set timeout value
   */
  public setTimeout(timeoutMs: number): void {
    this.currentTimeoutMs = Math.max(
      this.options.minTimeoutMs,
      Math.min(timeoutMs, this.options.maxTimeoutMs)
    );
  }

  private validateOptions(): void {
    if (this.options.baseTimeoutMs <= 0) {
      throw new Error('Base timeout must be greater than 0');
    }
    if (this.options.minTimeoutMs <= 0) {
      throw new Error('Min timeout must be greater than 0');
    }
    if (this.options.maxTimeoutMs <= this.options.minTimeoutMs) {
      throw new Error('Max timeout must be greater than min timeout');
    }
    if (this.options.baseTimeoutMs < this.options.minTimeoutMs || 
        this.options.baseTimeoutMs > this.options.maxTimeoutMs) {
      throw new Error('Base timeout must be between min and max timeout');
    }
    if (this.options.adaptationFactor <= 0 || this.options.adaptationFactor >= 1) {
      throw new Error('Adaptation factor must be between 0 and 1');
    }
    if (this.options.windowSize <= 0) {
      throw new Error('Window size must be greater than 0');
    }
  }
}

/**
 * Hierarchical timeout with cascading timeouts for nested operations
 */
export class HierarchicalTimeout {
  private static readonly MAX_TIMEOUT_MS = 60000; // Maximum allowed timeout (60 seconds)
  private static readonly FALLBACK_TIMEOUT_MS = 30000; // Fallback timeout when restriction is applied
  
  private activeTimeouts: Map<string, NodeJS.Timeout> = new Map();
  private operationStack: string[] = [];

  /**
   * Execute operation with hierarchical timeout
   */
  public async executeWithHierarchy<T>(
    operation: () => Promise<T>,
    operationId: string,
    timeoutMs: number,
    parentOperationId?: string
  ): Promise<T> {
    // Check if parent timeout would trigger before this timeout
    if (parentOperationId && this.activeTimeouts.has(parentOperationId)) {
      const parentStartTime = Date.now();
      // Estimate remaining parent timeout (simplified)
      if (timeoutMs > HierarchicalTimeout.MAX_TIMEOUT_MS) { // If timeout is too long, restrict it
        timeoutMs = Math.min(timeoutMs, HierarchicalTimeout.FALLBACK_TIMEOUT_MS);
      }
    }

    return new Promise<T>((resolve, reject) => {
      let completed = false;

      // Set up timeout
      const timeoutId = setTimeout(() => {
        if (!completed) {
          completed = true;
          this.cleanupOperation(operationId);
          reject(new TimeoutError(
            `Hierarchical operation '${operationId}' timed out after ${timeoutMs}ms`,
            timeoutMs,
            timeoutMs
          ));
        }
      }, timeoutMs);

      this.activeTimeouts.set(operationId, timeoutId);
      this.operationStack.push(operationId);

      // Execute operation
      operation()
        .then(result => {
          if (!completed) {
            completed = true;
            this.cleanupOperation(operationId);
            resolve(result);
          }
        })
        .catch(error => {
          if (!completed) {
            completed = true;
            this.cleanupOperation(operationId);
            reject(error);
          }
        });
    });
  }

  /**
   * Clean up operation timeout
   */
  private cleanupOperation(operationId: string): void {
    const timeoutId = this.activeTimeouts.get(operationId);
    if (timeoutId) {
      clearTimeout(timeoutId);
      this.activeTimeouts.delete(operationId);
    }

    const index = this.operationStack.indexOf(operationId);
    if (index !== -1) {
      this.operationStack.splice(index, 1);
    }
  }

  /**
   * Cancel all active timeouts
   */
  public cancelAll(): void {
    for (const timeoutId of this.activeTimeouts.values()) {
      clearTimeout(timeoutId);
    }
    this.activeTimeouts.clear();
    this.operationStack = [];
  }

  /**
   * Get active operations
   */
  public getActiveOperations(): string[] {
    return [...this.operationStack];
  }

  /**
   * Check if operation is active
   */
  public isOperationActive(operationId: string): boolean {
    return this.activeTimeouts.has(operationId);
  }
}

/**
 * Timeout manager for coordinating multiple timeout strategies
 */
export class TimeoutManager {
  private adaptiveTimeouts: Map<string, AdaptiveTimeout> = new Map();
  private hierarchicalTimeout: HierarchicalTimeout = new HierarchicalTimeout();

  /**
   * Create or get adaptive timeout instance
   */
  public getAdaptiveTimeout(name: string, options: AdaptiveTimeoutOptions): AdaptiveTimeout {
    if (!this.adaptiveTimeouts.has(name)) {
      this.adaptiveTimeouts.set(name, new AdaptiveTimeout(options));
    }
    return this.adaptiveTimeouts.get(name)!;
  }

  /**
   * Execute with adaptive timeout
   */
  public async executeWithAdaptiveTimeout<T>(
    name: string,
    operation: () => Promise<T>,
    operationName?: string
  ): Promise<T> {
    const adaptiveTimeout = this.adaptiveTimeouts.get(name);
    if (!adaptiveTimeout) {
      throw new Error(`Adaptive timeout '${name}' not found`);
    }

    return adaptiveTimeout.execute(operation, operationName);
  }

  /**
   * Execute with hierarchical timeout
   */
  public async executeWithHierarchicalTimeout<T>(
    operation: () => Promise<T>,
    operationId: string,
    timeoutMs: number,
    parentOperationId?: string
  ): Promise<T> {
    return this.hierarchicalTimeout.executeWithHierarchy(
      operation,
      operationId,
      timeoutMs,
      parentOperationId
    );
  }

  /**
   * Get all timeout statistics
   */
  public getAllStats(): Record<string, TimeoutStats> {
    const stats: Record<string, TimeoutStats> = {};
    
    for (const [name, adaptiveTimeout] of this.adaptiveTimeouts) {
      stats[name] = adaptiveTimeout.getStats();
    }
    
    return stats;
  }

  /**
   * Reset all timeout managers
   */
  public resetAll(): void {
    for (const adaptiveTimeout of this.adaptiveTimeouts.values()) {
      adaptiveTimeout.reset();
    }
    this.hierarchicalTimeout.cancelAll();
  }

  /**
   * Get active hierarchical operations
   */
  public getActiveHierarchicalOperations(): string[] {
    return this.hierarchicalTimeout.getActiveOperations();
  }

  /**
   * Cancel all active operations
   */
  public cancelAllOperations(): void {
    this.hierarchicalTimeout.cancelAll();
  }
}
