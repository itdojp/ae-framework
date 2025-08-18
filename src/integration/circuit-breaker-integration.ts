import { circuitBreakerManager, CircuitBreaker } from '../utils/circuit-breaker.js';
import { EventEmitter } from 'events';

/**
 * AE-Framework specific error types for circuit breaker filtering
 */
export class AgentCommunicationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'AgentCommunicationError';
  }
}

export class StateManagementError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'StateManagementError';
  }
}

export class PhaseTransitionError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'PhaseTransitionError';
  }
}

export class ExternalServiceError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ExternalServiceError';
  }
}

export class ResourceExhaustionError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ResourceExhaustionError';
  }
}

/**
 * Circuit Breaker Integration for AE-Framework Components
 */
export class AEFrameworkCircuitBreakerIntegration extends EventEmitter {
  private static instance: AEFrameworkCircuitBreakerIntegration;

  private constructor() {
    super();
    this.setupGlobalEventHandlers();
  }

  /**
   * Get singleton instance
   */
  static getInstance(): AEFrameworkCircuitBreakerIntegration {
    if (!this.instance) {
      this.instance = new AEFrameworkCircuitBreakerIntegration();
    }
    return this.instance;
  }

  /**
   * Get circuit breaker for agent communication
   */
  getAgentCircuitBreaker(agentName: string): CircuitBreaker {
    return circuitBreakerManager.getCircuitBreaker(`agent-${agentName}`, {
      failureThreshold: 5,
      successThreshold: 3,
      timeout: 30000,
      monitoringWindow: 60000,
      expectedErrors: [AgentCommunicationError, ExternalServiceError],
      fallback: () => this.agentFallback(agentName),
      enableMonitoring: true
    });
  }

  /**
   * Get circuit breaker for state management operations
   */
  getStateManagementCircuitBreaker(): CircuitBreaker {
    return circuitBreakerManager.getCircuitBreaker('state-management', {
      failureThreshold: 3,
      successThreshold: 2,
      timeout: 15000,
      monitoringWindow: 30000,
      expectedErrors: [StateManagementError],
      fallback: () => this.stateManagementFallback(),
      enableMonitoring: true
    });
  }

  /**
   * Get circuit breaker for phase transitions
   */
  getPhaseTransitionCircuitBreaker(): CircuitBreaker {
    return circuitBreakerManager.getCircuitBreaker('phase-transition', {
      failureThreshold: 2,
      successThreshold: 1,
      timeout: 60000,
      monitoringWindow: 60000,
      expectedErrors: [PhaseTransitionError, StateManagementError],
      fallback: () => this.phaseTransitionFallback(),
      enableMonitoring: true
    });
  }

  /**
   * Get circuit breaker for external service calls
   */
  getExternalServiceCircuitBreaker(serviceName: string): CircuitBreaker {
    return circuitBreakerManager.getCircuitBreaker(`external-${serviceName}`, {
      failureThreshold: 3,
      successThreshold: 2,
      timeout: 20000,
      monitoringWindow: 60000,
      expectedErrors: [ExternalServiceError],
      fallback: (...args: any[]) => this.externalServiceFallback(serviceName, ...args),
      enableMonitoring: true
    });
  }

  /**
   * Get circuit breaker for resource-intensive operations
   */
  getResourceCircuitBreaker(resourceType: string): CircuitBreaker {
    return circuitBreakerManager.getCircuitBreaker(`resource-${resourceType}`, {
      failureThreshold: 2,
      successThreshold: 1,
      timeout: 45000,
      monitoringWindow: 90000,
      expectedErrors: [ResourceExhaustionError],
      fallback: () => this.resourceFallback(resourceType),
      enableMonitoring: true
    });
  }

  /**
   * Execute agent operation with circuit breaker protection
   */
  async executeAgentOperation<T>(
    agentName: string,
    operation: () => Promise<T>,
    context?: any
  ): Promise<T> {
    const breaker = this.getAgentCircuitBreaker(agentName);
    
    try {
      return await breaker.execute(async () => {
        this.emit('agentOperationStarted', { agentName, context });
        const result = await operation();
        this.emit('agentOperationCompleted', { agentName, context, result });
        return result;
      });
    } catch (error) {
      this.emit('agentOperationFailed', { agentName, context, error });
      throw error;
    }
  }

  /**
   * Execute state management operation with circuit breaker protection
   */
  async executeStateOperation<T>(
    operationType: string,
    operation: () => Promise<T>,
    context?: any
  ): Promise<T> {
    const breaker = this.getStateManagementCircuitBreaker();
    
    try {
      return await breaker.execute(async () => {
        this.emit('stateOperationStarted', { operationType, context });
        const result = await operation();
        this.emit('stateOperationCompleted', { operationType, context, result });
        return result;
      });
    } catch (error) {
      this.emit('stateOperationFailed', { operationType, context, error });
      throw error;
    }
  }

  /**
   * Execute phase transition with circuit breaker protection
   */
  async executePhaseTransition<T>(
    fromPhase: string,
    toPhase: string,
    operation: () => Promise<T>,
    context?: any
  ): Promise<T> {
    const breaker = this.getPhaseTransitionCircuitBreaker();
    
    try {
      return await breaker.execute(async () => {
        this.emit('phaseTransitionStarted', { fromPhase, toPhase, context });
        const result = await operation();
        this.emit('phaseTransitionCompleted', { fromPhase, toPhase, context, result });
        return result;
      });
    } catch (error) {
      this.emit('phaseTransitionFailed', { fromPhase, toPhase, context, error });
      throw error;
    }
  }

  /**
   * Execute external service call with circuit breaker protection
   */
  async executeExternalServiceCall<T>(
    serviceName: string,
    operation: () => Promise<T>,
    context?: any
  ): Promise<T> {
    const breaker = this.getExternalServiceCircuitBreaker(serviceName);
    
    try {
      return await breaker.execute(async () => {
        this.emit('externalServiceCallStarted', { serviceName, context });
        const result = await operation();
        this.emit('externalServiceCallCompleted', { serviceName, context, result });
        return result;
      });
    } catch (error) {
      this.emit('externalServiceCallFailed', { serviceName, context, error });
      throw error;
    }
  }

  /**
   * Execute resource-intensive operation with circuit breaker protection
   */
  async executeResourceOperation<T>(
    resourceType: string,
    operation: () => Promise<T>,
    context?: any
  ): Promise<T> {
    const breaker = this.getResourceCircuitBreaker(resourceType);
    
    try {
      return await breaker.execute(async () => {
        this.emit('resourceOperationStarted', { resourceType, context });
        const result = await operation();
        this.emit('resourceOperationCompleted', { resourceType, context, result });
        return result;
      });
    } catch (error) {
      this.emit('resourceOperationFailed', { resourceType, context, error });
      throw error;
    }
  }

  /**
   * Get comprehensive health status for all AE-Framework circuit breakers
   */
  getFrameworkHealthStatus(): {
    overall: 'healthy' | 'degraded' | 'critical';
    components: {
      agents: { [agentName: string]: 'healthy' | 'degraded' | 'critical' };
      stateManagement: 'healthy' | 'degraded' | 'critical';
      phaseTransitions: 'healthy' | 'degraded' | 'critical';
      externalServices: { [serviceName: string]: 'healthy' | 'degraded' | 'critical' };
      resources: { [resourceType: string]: 'healthy' | 'degraded' | 'critical' };
    };
    recommendations: string[];
  } {
    const allBreakers = circuitBreakerManager.getAllBreakers();
    const recommendations: string[] = [];
    
    const components = {
      agents: {} as { [agentName: string]: 'healthy' | 'degraded' | 'critical' },
      stateManagement: 'healthy' as 'healthy' | 'degraded' | 'critical',
      phaseTransitions: 'healthy' as 'healthy' | 'degraded' | 'critical',
      externalServices: {} as { [serviceName: string]: 'healthy' | 'degraded' | 'critical' },
      resources: {} as { [resourceType: string]: 'healthy' | 'degraded' | 'critical' }
    };

    let criticalCount = 0;
    let degradedCount = 0;

    for (const [name, breaker] of allBreakers) {
      const health = breaker.generateHealthReport();
      let componentHealth: 'healthy' | 'degraded' | 'critical';
      
      switch (health.health) {
        case 'healthy':
          componentHealth = 'healthy';
          break;
        case 'degraded':
          componentHealth = 'degraded';
          degradedCount++;
          break;
        case 'unhealthy':
          componentHealth = 'critical';
          criticalCount++;
          break;
      }

      if (name.startsWith('agent-')) {
        const agentName = name.substring(6);
        components.agents[agentName] = componentHealth;
      } else if (name === 'state-management') {
        components.stateManagement = componentHealth;
      } else if (name === 'phase-transition') {
        components.phaseTransitions = componentHealth;
      } else if (name.startsWith('external-')) {
        const serviceName = name.substring(9);
        components.externalServices[serviceName] = componentHealth;
      } else if (name.startsWith('resource-')) {
        const resourceType = name.substring(9);
        components.resources[resourceType] = componentHealth;
      }

      // Add specific recommendations
      if (health.health !== 'healthy') {
        recommendations.push(...health.recommendations.map(rec => `${name}: ${rec}`));
      }
    }

    let overall: 'healthy' | 'degraded' | 'critical';
    if (criticalCount > 0) {
      overall = 'critical';
      recommendations.unshift('Critical failures detected - immediate attention required');
    } else if (degradedCount > 0) {
      overall = 'degraded';
      recommendations.unshift('Performance degradation detected - monitor closely');
    } else {
      overall = 'healthy';
    }

    return {
      overall,
      components,
      recommendations
    };
  }

  /**
   * Reset all framework circuit breakers
   */
  resetAllCircuitBreakers(): void {
    circuitBreakerManager.resetAll();
    this.emit('allCircuitBreakersReset');
  }

  // Fallback implementations

  private agentFallback(agentName: string): any {
    this.emit('agentFallbackTriggered', { agentName });
    console.warn(`🔄 Agent '${agentName}' circuit breaker fallback triggered`);
    return {
      success: false,
      error: 'Agent temporarily unavailable',
      fallback: true,
      timestamp: new Date().toISOString()
    };
  }

  private stateManagementFallback(): any {
    this.emit('stateManagementFallbackTriggered');
    console.warn('🔄 State management circuit breaker fallback triggered');
    return {
      success: false,
      error: 'State management temporarily unavailable',
      fallback: true,
      timestamp: new Date().toISOString()
    };
  }

  private phaseTransitionFallback(): any {
    this.emit('phaseTransitionFallbackTriggered');
    console.warn('🔄 Phase transition circuit breaker fallback triggered');
    return {
      success: false,
      error: 'Phase transition temporarily unavailable',
      fallback: true,
      timestamp: new Date().toISOString()
    };
  }

  private externalServiceFallback(serviceName: string, ...args: any[]): any {
    this.emit('externalServiceFallbackTriggered', { serviceName, args });
    console.warn(`🔄 External service '${serviceName}' circuit breaker fallback triggered`);
    return {
      success: false,
      error: `External service '${serviceName}' temporarily unavailable`,
      fallback: true,
      timestamp: new Date().toISOString()
    };
  }

  private resourceFallback(resourceType: string): any {
    this.emit('resourceFallbackTriggered', { resourceType });
    console.warn(`🔄 Resource '${resourceType}' circuit breaker fallback triggered`);
    return {
      success: false,
      error: `Resource '${resourceType}' temporarily unavailable`,
      fallback: true,
      timestamp: new Date().toISOString()
    };
  }

  private setupGlobalEventHandlers(): void {
    // Forward important circuit breaker events
    circuitBreakerManager.on('circuitOpened', (event) => {
      console.error(`🚨 Circuit breaker '${event.name}' opened after ${event.failureCount} failures`);
      this.emit('circuitBreakerOpened', event);
    });

    circuitBreakerManager.on('circuitClosed', (event) => {
      console.log(`✅ Circuit breaker '${event.name}' closed after ${event.successCount} successes`);
      this.emit('circuitBreakerClosed', event);
    });

    circuitBreakerManager.on('breakerStateChanged', (event) => {
      console.log(`🔄 Circuit breaker '${event.name}' state changed: ${event.previousState} → ${event.newState}`);
      this.emit('circuitBreakerStateChanged', event);
    });
  }
}

// Export singleton instance for convenience
export const aeFrameworkCircuitBreakers = AEFrameworkCircuitBreakerIntegration.getInstance();

/**
 * Decorator for adding circuit breaker protection to methods
 */
export function WithCircuitBreaker(
  breakerName: string,
  options?: {
    failureThreshold?: number;
    successThreshold?: number;
    timeout?: number;
    expectedErrors?: Array<new (...args: any[]) => Error>;
    fallback?: (...args: any[]) => any;
  }
) {
  return function (target: any, propertyKey: string, descriptor: PropertyDescriptor) {
    const originalMethod = descriptor.value;
    
    descriptor.value = async function (...args: any[]) {
      const breaker = circuitBreakerManager.getCircuitBreaker(breakerName, options);
      
      return breaker.execute(async () => {
        return originalMethod.apply(this, args);
      });
    };
    
    return descriptor;
  };
}

/**
 * Utility functions for common circuit breaker patterns
 */
export class CircuitBreakerUtils {
  /**
   * Create a retry-with-circuit-breaker pattern
   */
  static async executeWithRetryAndCircuitBreaker<T>(
    operation: () => Promise<T>,
    circuitBreaker: CircuitBreaker,
    retryOptions: {
      maxRetries: number;
      delayMs: number;
      backoffMultiplier?: number;
    }
  ): Promise<T> {
    let lastError: Error;
    let delay = retryOptions.delayMs;

    for (let attempt = 0; attempt <= retryOptions.maxRetries; attempt++) {
      try {
        return await circuitBreaker.execute(operation);
      } catch (error) {
        lastError = error as Error;
        
        if (attempt === retryOptions.maxRetries) {
          break;
        }

        // Wait before retry
        await new Promise(resolve => setTimeout(resolve, delay));
        
        if (retryOptions.backoffMultiplier) {
          delay *= retryOptions.backoffMultiplier;
        }
      }
    }

    throw lastError!;
  }

  /**
   * Create a timeout-with-circuit-breaker pattern
   */
  static async executeWithTimeoutAndCircuitBreaker<T>(
    operation: () => Promise<T>,
    circuitBreaker: CircuitBreaker,
    timeoutMs: number
  ): Promise<T> {
    return circuitBreaker.execute(async () => {
      return Promise.race([
        operation(),
        new Promise<never>((_, reject) => {
          setTimeout(() => reject(new Error(`Operation timed out after ${timeoutMs}ms`)), timeoutMs);
        })
      ]);
    });
  }

  /**
   * Create a bulk operation with circuit breaker protection
   */
  static async executeBulkWithCircuitBreaker<T, R>(
    items: T[],
    operation: (item: T) => Promise<R>,
    circuitBreaker: CircuitBreaker,
    options: {
      concurrency?: number;
      failFast?: boolean;
    } = {}
  ): Promise<Array<{ item: T; result?: R; error?: Error }>> {
    const { concurrency = 3, failFast = false } = options;
    const results: Array<{ item: T; result?: R; error?: Error }> = [];
    
    for (let i = 0; i < items.length; i += concurrency) {
      const chunk = items.slice(i, i + concurrency);
      
      const chunkPromises = chunk.map(async (item) => {
        try {
          const result = await circuitBreaker.execute(() => operation(item));
          return { item, result };
        } catch (error) {
          if (failFast) {
            throw error;
          }
          return { item, error: error as Error };
        }
      });

      const chunkResults = await Promise.all(chunkPromises);
      results.push(...chunkResults);
    }

    return results;
  }
}