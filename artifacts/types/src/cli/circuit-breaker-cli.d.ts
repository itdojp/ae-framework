#!/usr/bin/env node
import { Command } from 'commander';
/**
 * Circuit Breaker CLI
 * Provides command-line interface for circuit breaker management and monitoring
 */
export declare class CircuitBreakerCLI {
    private breakers;
    constructor();
    /**
     * Create a circuit breaker with configuration
     */
    createCircuitBreaker(options: {
        name: string;
        failureThreshold?: number;
        successThreshold?: number;
        timeout?: number;
        monitoringWindow?: number;
    }): Promise<void>;
    /**
     * List all circuit breakers and their states
     */
    listCircuitBreakers(): Promise<void>;
    /**
     * Show detailed statistics for a specific circuit breaker
     */
    showStats(breakerName: string): Promise<void>;
    /**
     * Generate comprehensive health report
     */
    generateHealthReport(): Promise<void>;
    /**
     * Test a circuit breaker with simulated operations
     */
    testCircuitBreaker(options: {
        name: string;
        operations: number;
        failureRate: number;
        delay: number;
    }): Promise<void>;
    /**
     * Reset a circuit breaker
     */
    resetCircuitBreaker(breakerName: string): Promise<void>;
    /**
     * Force open a circuit breaker
     */
    forceOpen(breakerName: string): Promise<void>;
    /**
     * Force close a circuit breaker
     */
    forceClose(breakerName: string): Promise<void>;
    /**
     * Watch circuit breaker state changes in real-time
     */
    watchCircuitBreakers(): Promise<void>;
    private setupEventListeners;
    private getStateIcon;
    private getHealthIcon;
    private formatDuration;
    private createHealthReport;
}
export declare function createCircuitBreakerCommand(): Command;
