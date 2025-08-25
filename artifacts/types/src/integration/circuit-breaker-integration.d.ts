import { CircuitBreaker } from '../utils/circuit-breaker.js';
import { EventEmitter } from 'events';
/**
 * AE-Framework specific error types for circuit breaker filtering
 */
export declare class AgentCommunicationError extends Error {
    constructor(message: string);
}
export declare class StateManagementError extends Error {
    constructor(message: string);
}
export declare class PhaseTransitionError extends Error {
    constructor(message: string);
}
export declare class ExternalServiceError extends Error {
    constructor(message: string);
}
export declare class ResourceExhaustionError extends Error {
    constructor(message: string);
}
/**
 * Circuit Breaker Integration for AE-Framework Components
 */
export declare class AEFrameworkCircuitBreakerIntegration extends EventEmitter {
    private static instance;
    private constructor();
    /**
     * Get singleton instance
     */
    static getInstance(): AEFrameworkCircuitBreakerIntegration;
    /**
     * Get circuit breaker for agent communication
     */
    getAgentCircuitBreaker(agentName: string): CircuitBreaker;
    /**
     * Get circuit breaker for state management operations
     */
    getStateManagementCircuitBreaker(): CircuitBreaker;
    /**
     * Get circuit breaker for phase transitions
     */
    getPhaseTransitionCircuitBreaker(): CircuitBreaker;
    /**
     * Get circuit breaker for external service calls
     */
    getExternalServiceCircuitBreaker(serviceName: string): CircuitBreaker;
    /**
     * Get circuit breaker for resource-intensive operations
     */
    getResourceCircuitBreaker(resourceType: string): CircuitBreaker;
    /**
     * Execute agent operation with circuit breaker protection
     */
    executeAgentOperation<T>(agentName: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute state management operation with circuit breaker protection
     */
    executeStateOperation<T>(operationType: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute phase transition with circuit breaker protection
     */
    executePhaseTransition<T>(fromPhase: string, toPhase: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute external service call with circuit breaker protection
     */
    executeExternalServiceCall<T>(serviceName: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute resource-intensive operation with circuit breaker protection
     */
    executeResourceOperation<T>(resourceType: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Get comprehensive health status for all AE-Framework circuit breakers
     */
    getFrameworkHealthStatus(): {
        overall: 'healthy' | 'degraded' | 'critical';
        components: {
            agents: {
                [agentName: string]: 'healthy' | 'degraded' | 'critical';
            };
            stateManagement: 'healthy' | 'degraded' | 'critical';
            phaseTransitions: 'healthy' | 'degraded' | 'critical';
            externalServices: {
                [serviceName: string]: 'healthy' | 'degraded' | 'critical';
            };
            resources: {
                [resourceType: string]: 'healthy' | 'degraded' | 'critical';
            };
        };
        recommendations: string[];
    };
    /**
     * Reset all framework circuit breakers
     */
    resetAllCircuitBreakers(): void;
    private agentFallback;
    private stateManagementFallback;
    private phaseTransitionFallback;
    private externalServiceFallback;
    private resourceFallback;
    private setupGlobalEventHandlers;
}
export declare const aeFrameworkCircuitBreakers: AEFrameworkCircuitBreakerIntegration;
/**
 * Decorator for adding circuit breaker protection to methods
 */
export declare function WithCircuitBreaker(breakerName: string, options?: {
    failureThreshold?: number;
    successThreshold?: number;
    timeout?: number;
    expectedErrors?: Array<new (...args: any[]) => Error>;
    fallback?: (...args: any[]) => any;
}): (target: any, propertyKey: string, descriptor: PropertyDescriptor) => PropertyDescriptor;
/**
 * Utility functions for common circuit breaker patterns
 */
export declare class CircuitBreakerUtils {
    /**
     * Create a retry-with-circuit-breaker pattern
     */
    static executeWithRetryAndCircuitBreaker<T>(operation: () => Promise<T>, circuitBreaker: CircuitBreaker, retryOptions: {
        maxRetries: number;
        delayMs: number;
        backoffMultiplier?: number;
    }): Promise<T>;
    /**
     * Create a timeout-with-circuit-breaker pattern
     */
    static executeWithTimeoutAndCircuitBreaker<T>(operation: () => Promise<T>, circuitBreaker: CircuitBreaker, timeoutMs: number): Promise<T>;
    /**
     * Create a bulk operation with circuit breaker protection
     */
    static executeBulkWithCircuitBreaker<T, R>(items: T[], operation: (item: T) => Promise<R>, circuitBreaker: CircuitBreaker, options?: {
        concurrency?: number;
        failFast?: boolean;
    }): Promise<Array<{
        item: T;
        result?: R;
        error?: Error;
    }>>;
}
