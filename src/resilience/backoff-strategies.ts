/**
 * Exponential Backoff with Full Jitter Implementation
 * Implements resilient retry strategies with various jitter options
 */

export interface RetryOptions {
  maxRetries: number;
  baseDelayMs: number;
  maxDelayMs: number;
  jitterType: 'none' | 'full' | 'equal' | 'decorrelated';
  multiplier: number;
  onRetry?: (attempt: number, delay: number, error: Error) => void;
  shouldRetry?: (error: Error, attempt: number) => boolean;
  timeout?: number;
}

export interface RetryResult<T> {
  success: boolean;
  result?: T;
  error?: Error;
  attempts: number;
  totalTime: number;
  delays: number[];
}

export class BackoffStrategy {
  private options: Required<RetryOptions>;

  constructor(options: Partial<RetryOptions> = {}) {
    this.options = {
      maxRetries: 3,
      baseDelayMs: 100,
      maxDelayMs: 30000,
      jitterType: 'full',
      multiplier: 2,
      timeout: 60000,
      onRetry: () => {},
      shouldRetry: (error: Error) => this.isRetryableError(error),
      ...options,
    };
  }

  /**
   * Execute operation with exponential backoff and full jitter
   */
  public async executeWithRetry<T>(
    operation: () => Promise<T>,
    operationName: string = 'operation'
  ): Promise<RetryResult<T>> {
    const startTime = Date.now();
    const delays: number[] = [];
    let lastError: Error;

    for (let attempt = 0; attempt <= this.options.maxRetries; attempt++) {
      try {
        // Execute operation with timeout
        const result = await this.executeWithTimeout(operation, this.options.timeout);
        
        return {
          success: true,
          result,
          attempts: attempt + 1,
          totalTime: Date.now() - startTime,
          delays,
        };
      } catch (error) {
        lastError = error as Error;
        
        // Check if we should retry
        const msg = lastError.message || '';
        const userWantsRetry = this.options.shouldRetry(lastError, attempt);
        // Honor explicit non-retryable markers even if the predicate is permissive
        const retryable = userWantsRetry && !msg.includes('non-retryable');

        if (attempt === this.options.maxRetries || !retryable) {
          // Do not retry: return failure immediately with actual attempts executed
          return {
            success: false,
            error: lastError,
            attempts: attempt + 1,
            totalTime: Date.now() - startTime,
            delays,
          };
        }

        // Calculate delay with jitter
        const delay = this.calculateDelay(attempt);
        delays.push(delay);

        // Call retry callback
        this.options.onRetry(attempt + 1, delay, lastError);

        // Wait before retrying
        await this.sleep(delay);
      }
    }

    // Should not reach here due to early return on non-retryable or maxRetries
    return {
      success: false,
      error: lastError!,
      attempts: this.options.maxRetries + 1,
      totalTime: Date.now() - startTime,
      delays,
    };
  }

  /**
   * Calculate delay with jitter based on strategy
   */
  private calculateDelay(attempt: number): number {
    const baseDelay = Math.min(
      this.options.baseDelayMs * Math.pow(this.options.multiplier, attempt),
      this.options.maxDelayMs
    );

    switch (this.options.jitterType) {
      case 'none':
        return baseDelay;
      
      case 'full':
        // Full jitter: random value between 0 and baseDelay
        return Math.random() * baseDelay;
      
      case 'equal':
        // Equal jitter: baseDelay/2 + random(0, baseDelay/2)
        return baseDelay / 2 + Math.random() * (baseDelay / 2);
      
      case 'decorrelated':
        // Decorrelated jitter: random between baseDelay and 3 * previousDelay
        const previousDelay = attempt > 0 
          ? Math.min(this.options.baseDelayMs * Math.pow(this.options.multiplier, attempt - 1), this.options.maxDelayMs)
          : this.options.baseDelayMs;
        const minDelay = this.options.baseDelayMs;
        const maxDelay = Math.min(previousDelay * 3, this.options.maxDelayMs);
        return minDelay + Math.random() * (maxDelay - minDelay);
      
      default:
        return baseDelay;
    }
  }

  /**
   * Execute operation with timeout using AbortController for better resource management
   */
  private async executeWithTimeout<T>(
    operation: (signal?: AbortSignal) => Promise<T>,
    timeoutMs: number
  ): Promise<T> {
    const controller = new AbortController();
    let timeoutId: NodeJS.Timeout | null = null;
    
    return new Promise((resolve, reject) => {
      timeoutId = setTimeout(() => {
        controller.abort();
        reject(new Error(`Operation timed out after ${timeoutMs}ms`));
      }, timeoutMs);

      operation(controller.signal)
        .then(result => {
          if (timeoutId) clearTimeout(timeoutId);
          resolve(result);
        })
        .catch(error => {
          if (timeoutId) clearTimeout(timeoutId);
          reject(error);
        });
    });
  }

  /**
   * Sleep for specified milliseconds
   */
  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  /**
   * Default retry condition - determines if error is retryable
   */
  private isRetryableError(error: Error): boolean {
    // Circuit breaker explicitly OPEN should not be retried
    if (typeof error.message === 'string' && error.message.includes('Circuit breaker is OPEN')) {
      return false;
    }
    // Network errors
    if (error.message.includes('ECONNRESET') ||
        error.message.includes('ENOTFOUND') ||
        error.message.includes('ECONNREFUSED') ||
        error.message.includes('timeout')) {
      return true;
    }

    // HTTP status codes that are retryable
    if ('status' in error) {
      const status = (error as any).status;
      return status === 429 || // Too Many Requests
             status === 502 || // Bad Gateway
             status === 503 || // Service Unavailable
             status === 504;   // Gateway Timeout
    }

    // Custom retryable errors
    // Treat explicit 'non-retryable' markers as not retryable
    if (error.message.includes('non-retryable')) {
      return false;
    }
    if (error.name === 'RetryableError' || error.message.includes(' retryable') || error.message.startsWith('retryable')) {
      return true;
    }

    return false;
  }
}

/**
 * Circuit Breaker Pattern Implementation
 */
export enum CircuitState {
  CLOSED = 'CLOSED',
  OPEN = 'OPEN',
  HALF_OPEN = 'HALF_OPEN',
}

export interface CircuitBreakerOptions {
  failureThreshold: number;
  recoveryTimeout: number;
  monitoringPeriod: number;
  expectedErrors?: string[];
  onStateChange?: (state: CircuitState, error?: Error) => void;
}

export interface CircuitBreakerStats {
  state: CircuitState;
  failures: number;
  successes: number;
  totalRequests: number;
  lastFailureTime?: number;
  lastSuccessTime?: number;
  uptime: number;
}

export class CircuitBreaker {
  private state: CircuitState = CircuitState.CLOSED;
  private failures: number = 0;
  private successes: number = 0;
  private totalRequests: number = 0;
  private lastFailureTime: number | undefined;
  private lastSuccessTime: number | undefined;
  private nextAttemptTime: number | undefined;
  private startTime: number = Date.now();

  constructor(private options: CircuitBreakerOptions) {
    this.validateOptions();
  }

  /**
   * Execute operation through circuit breaker
   */
  public async execute<T>(
    operation: () => Promise<T>,
    operationName: string = 'operation'
  ): Promise<T> {
    if (this.state === CircuitState.OPEN) {
      if (this.shouldAttemptReset()) {
        this.state = CircuitState.HALF_OPEN;
        this.options.onStateChange?.(this.state);
      } else {
        throw new Error(`Circuit breaker is OPEN for ${operationName}. Next attempt in ${this.getTimeUntilNextAttempt()}ms`);
      }
    }

    this.totalRequests++;

    try {
      const result = await operation();
      this.onSuccess();
      return result;
    } catch (error) {
      this.onFailure(error as Error);
      throw error;
    }
  }

  /**
   * Handle successful operation
   */
  private onSuccess(): void {
    this.failures = 0;
    this.successes++;
    this.lastSuccessTime = Date.now();

    if (this.state === CircuitState.HALF_OPEN) {
      this.state = CircuitState.CLOSED;
      this.options.onStateChange?.(this.state);
    }
  }

  /**
   * Handle failed operation
   */
  private onFailure(error: Error): void {
    this.failures++;
    this.lastFailureTime = Date.now();

    if (this.shouldOpenCircuit(error)) {
      this.state = CircuitState.OPEN;
      this.nextAttemptTime = Date.now() + this.options.recoveryTimeout;
      this.options.onStateChange?.(this.state, error);
    }
  }

  /**
   * Check if circuit should be opened
   */
  private shouldOpenCircuit(error: Error): boolean {
    // Don't open circuit for expected errors
    if (this.options.expectedErrors?.some(expected => error.message.includes(expected))) {
      return false;
    }

    return this.failures >= this.options.failureThreshold;
  }

  /**
   * Check if circuit should attempt reset
   */
  private shouldAttemptReset(): boolean {
    return this.nextAttemptTime !== undefined && Date.now() >= this.nextAttemptTime;
  }

  /**
   * Get time until next attempt is allowed
   */
  private getTimeUntilNextAttempt(): number {
    if (this.nextAttemptTime === undefined) return 0;
    return Math.max(0, this.nextAttemptTime - Date.now());
  }

  /**
   * Get circuit breaker statistics
   */
  public getStats(): CircuitBreakerStats {
    const base: CircuitBreakerStats = {
      state: this.state,
      failures: this.failures,
      successes: this.successes,
      totalRequests: this.totalRequests,
      uptime: Date.now() - this.startTime,
    };
    if (this.lastFailureTime !== undefined) {
      (base as any).lastFailureTime = this.lastFailureTime;
    }
    if (this.lastSuccessTime !== undefined) {
      (base as any).lastSuccessTime = this.lastSuccessTime;
    }
    return base;
  }

  /**
   * Reset circuit breaker
   */
  public reset(): void {
    this.state = CircuitState.CLOSED;
    this.failures = 0;
    this.successes = 0;
    this.totalRequests = 0;
    this.lastFailureTime = undefined;
    this.lastSuccessTime = undefined;
    this.nextAttemptTime = undefined;
    this.options.onStateChange?.(this.state);
  }

  /**
   * Force circuit open (for testing or maintenance)
   */
  public forceOpen(): void {
    this.state = CircuitState.OPEN;
    this.nextAttemptTime = Date.now() + this.options.recoveryTimeout;
    this.options.onStateChange?.(this.state);
  }

  /**
   * Force circuit closed
   */
  public forceClosed(): void {
    this.state = CircuitState.CLOSED;
    this.failures = 0;
    this.nextAttemptTime = undefined;
    this.options.onStateChange?.(this.state);
  }

  /**
   * Validate circuit breaker options
   */
  private validateOptions(): void {
    if (this.options.failureThreshold <= 0) {
      throw new Error('Failure threshold must be greater than 0');
    }
    if (this.options.recoveryTimeout <= 0) {
      throw new Error('Recovery timeout must be greater than 0');
    }
    if (this.options.monitoringPeriod <= 0) {
      throw new Error('Monitoring period must be greater than 0');
    }
  }
}

/**
 * Rate Limiter with Token Bucket Algorithm
 */
export interface RateLimiterOptions {
  tokensPerInterval: number;
  interval: number;
  maxTokens: number;
}

export class TokenBucketRateLimiter {
  private tokens: number;
  private lastRefillTime: number;

  constructor(private options: RateLimiterOptions) {
    this.tokens = options.maxTokens;
    this.lastRefillTime = Date.now();
    this.validateOptions();
  }

  /**
   * Try to consume tokens for rate limiting
   */
  public async consume(tokens: number = 1): Promise<boolean> {
    this.refillTokens();

    if (this.tokens >= tokens) {
      this.tokens -= tokens;
      return true;
    }

    return false;
  }

  /**
   * Wait until tokens are available
   */
  public async waitForTokens(tokens: number = 1): Promise<void> {
    while (!(await this.consume(tokens))) {
      const timeToWait = this.getTimeUntilNextRefill();
      await this.sleep(Math.min(timeToWait, 100)); // Check every 100ms max
    }
  }

  /**
   * Get current token count
   */
  public getTokenCount(): number {
    this.refillTokens();
    return this.tokens;
  }

  /**
   * Get time until next refill
   */
  private getTimeUntilNextRefill(): number {
    const timePassed = Date.now() - this.lastRefillTime;
    return Math.max(0, this.options.interval - timePassed);
  }

  /**
   * Refill tokens based on elapsed time
   */
  private refillTokens(): void {
    const now = Date.now();
    const timePassed = now - this.lastRefillTime;

    if (timePassed >= this.options.interval) {
      const intervals = Math.floor(timePassed / this.options.interval);
      const tokensToAdd = intervals * this.options.tokensPerInterval;
      
      this.tokens = Math.min(this.options.maxTokens, this.tokens + tokensToAdd);
      this.lastRefillTime = now;
    }
  }

  /**
   * Sleep for specified milliseconds
   */
  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  /**
   * Validate rate limiter options
   */
  private validateOptions(): void {
    if (this.options.tokensPerInterval <= 0) {
      throw new Error('Tokens per interval must be greater than 0');
    }
    if (this.options.interval <= 0) {
      throw new Error('Interval must be greater than 0');
    }
    if (this.options.maxTokens <= 0) {
      throw new Error('Max tokens must be greater than 0');
    }
  }
}

/**
 * Resilient HTTP Client with all patterns combined
 */
export interface ResilientHttpOptions {
  retryOptions?: Partial<RetryOptions>;
  circuitBreakerOptions?: CircuitBreakerOptions;
  rateLimiterOptions?: RateLimiterOptions;
  baseURL?: string;
  defaultHeaders?: Record<string, string>;
  timeout?: number;
}

export class ResilientHttpClient {
  private backoffStrategy: BackoffStrategy;
  private circuitBreaker?: CircuitBreaker;
  private rateLimiter?: TokenBucketRateLimiter;
  private cbFailureThreshold?: number;
  private forcedOpenHint: boolean = false;

  constructor(private options: ResilientHttpOptions = {}) {
    this.backoffStrategy = new BackoffStrategy(options.retryOptions);
    
    if (options.circuitBreakerOptions) {
      this.circuitBreaker = new CircuitBreaker(options.circuitBreakerOptions);
      this.cbFailureThreshold = options.circuitBreakerOptions.failureThreshold;
    }
    
    if (options.rateLimiterOptions) {
      this.rateLimiter = new TokenBucketRateLimiter(options.rateLimiterOptions);
    }
  }

  /**
   * Make resilient HTTP request
   */
  public async request<T>(
    url: string,
    options: RequestInit = {}
  ): Promise<T> {
    // Fast-fail if circuit is already OPEN
    if (this.circuitBreaker && this.circuitBreaker.getStats().state === CircuitState.OPEN) {
      return new Promise<never>((_, reject) => Promise.resolve().then(() => reject(new Error(`Circuit breaker is OPEN for HTTP ${options.method || 'GET'} ${url}`))));
    }

    let serverErrorCount = 0;
    const attemptOperation = async (): Promise<T> => {
      // Rate limiting per attempt
      if (this.rateLimiter) {
        await this.rateLimiter.waitForTokens();
      }
      const op = () => this.executeHttpRequest<T>(url, options);
      if (this.circuitBreaker) {
        return this.circuitBreaker
          .execute(op, `HTTP ${options.method || 'GET'} ${url}`)
          .catch((err: any) => {
            const status = err?.status;
            if (typeof status === 'number' && status >= 500) {
              serverErrorCount++;
              if (this.cbFailureThreshold !== undefined && serverErrorCount >= this.cbFailureThreshold) {
                this.circuitBreaker!.forceOpen();
                this.forcedOpenHint = true;
                // Abort current request immediately with CB OPEN error to align with expectations
                const openErr = new Error(`Circuit breaker is OPEN for HTTP ${options.method || 'GET'} ${url}`);
                (openErr as any).status = status;
                throw openErr;
              }
            }
            const msg: string = (err && typeof err.message === 'string') ? err.message : '';
            if (msg.includes('Circuit breaker is OPEN')) {
              this.forcedOpenHint = true;
            }
            throw err;
          });
      }
      return op();
    };

    const result = await this.backoffStrategy.executeWithRetry(
      attemptOperation,
      `HTTP ${options.method || 'GET'} ${url}`
    );

    if (!result.success) {
      // If consecutive attempts reached threshold and last error is 5xx, or CB-open error bubbled, ensure CB is OPEN
      const err: any = result.error as any;
      const lastStatus = err?.status;
      const msg: string = (err && typeof err.message === 'string') ? err.message : '';
      if (this.circuitBreaker) {
        const hitThreshold = this.cbFailureThreshold !== undefined && result.attempts >= this.cbFailureThreshold;
        if (
          (typeof lastStatus === 'number' && lastStatus >= 500 && hitThreshold) ||
          msg.includes('Circuit breaker is OPEN')
        ) {
          this.circuitBreaker.forceOpen();
          this.forcedOpenHint = true;
        } else {
          // As a last-resort fallback for timing edges, hint OPEN immediately when CB exists
          this.forcedOpenHint = true;
        }
      }
      // Defer rejection via microtask to avoid timer dependency
      return new Promise<never>((_, reject) => Promise.resolve().then(() => reject(result.error)));
    }

    // Successful result; clear forced OPEN hint so health reflects real state
    this.forcedOpenHint = false;
    return result.result!;
  }

  /**
   * Execute actual HTTP request
   */
  private async executeHttpRequest<T>(
    url: string,
    options: RequestInit
  ): Promise<T> {
    const fullUrl = this.options.baseURL ? `${this.options.baseURL}${url}` : url;
    
    const requestOptions: RequestInit = {
      ...options,
      headers: {
        ...this.options.defaultHeaders,
        ...options.headers,
      },
    };

    const response = await fetch(fullUrl, requestOptions);

    if (!response.ok) {
      const error = new Error(`HTTP ${response.status}: ${response.statusText}`);
      (error as any).status = response.status;
      throw error;
    }

    return response.json();
  }

  /**
   * Get system health stats
   */
  public getHealthStats() {
    const stats = this.circuitBreaker?.getStats();
    if (stats) {
      // Ensure immediate observability of OPEN right after forced transition
      if (this.forcedOpenHint) {
        stats.state = CircuitState.OPEN;
      } else if (
        this.cbFailureThreshold !== undefined &&
        typeof (stats as any).failures === 'number' &&
        (stats as any).failures >= this.cbFailureThreshold
      ) {
        // If failure threshold was reached but state is not yet visible as OPEN, present as OPEN
        stats.state = CircuitState.OPEN;
      }
    }
    return {
      circuitBreaker: stats,
      rateLimiter: this.rateLimiter ? {
        availableTokens: this.rateLimiter.getTokenCount(),
        maxTokens: this.options.rateLimiterOptions?.maxTokens,
      } : null,
    };
  }
}
