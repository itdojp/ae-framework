/**
 * Conformance Verification Engine
 * Phase 2.2: Central orchestrator for runtime conformance verification
 */
import { EventEmitter } from 'events';
import { ConformanceRule, ConformanceConfig, RuntimeContext, ConformanceVerificationResult, ConformanceMonitor, ViolationHandler, ConformanceMetrics, ConformanceRuleCategory } from './types.js';
export declare class ConformanceVerificationEngine extends EventEmitter {
    private config;
    private ruleEngine;
    private monitors;
    private violationHandlers;
    private metrics;
    private isRunning;
    private verificationCount;
    private violationCount;
    constructor(config: ConformanceConfig);
    /**
     * Start the verification engine
     */
    start(): Promise<void>;
    /**
     * Stop the verification engine
     */
    stop(): Promise<void>;
    /**
     * Verify data against all applicable rules
     */
    verify(data: any, context: RuntimeContext, options?: {
        ruleIds?: string[];
        skipCategories?: ConformanceRuleCategory[];
        async?: boolean;
    }): Promise<ConformanceVerificationResult>;
    /**
     * Add a conformance rule
     */
    addRule(rule: ConformanceRule): Promise<void>;
    /**
     * Update a conformance rule
     */
    updateRule(rule: ConformanceRule): Promise<void>;
    /**
     * Remove a conformance rule
     */
    removeRule(ruleId: string): Promise<void>;
    /**
     * Get all rules
     */
    getRules(): ConformanceRule[];
    /**
     * Get rules by category
     */
    getRulesByCategory(category: ConformanceRuleCategory): ConformanceRule[];
    /**
     * Add a specialized monitor
     */
    addMonitor(monitor: ConformanceMonitor): void;
    /**
     * Remove a specialized monitor
     */
    removeMonitor(monitorId: string): void;
    /**
     * Add a violation handler
     */
    addViolationHandler(category: ConformanceRuleCategory, handler: ViolationHandler): void;
    /**
     * Remove a violation handler
     */
    removeViolationHandler(category: ConformanceRuleCategory, handler: ViolationHandler): void;
    /**
     * Get current metrics
     */
    getMetrics(): ConformanceMetrics;
    /**
     * Reset metrics
     */
    resetMetrics(): void;
    /**
     * Get engine configuration
     */
    getConfig(): ConformanceConfig;
    /**
     * Update engine configuration
     */
    updateConfig(newConfig: Partial<ConformanceConfig>): void;
    /**
     * Setup default monitors
     */
    private setupDefaultMonitors;
    /**
     * Run specialized monitors
     */
    private runSpecializedMonitors;
    /**
     * Merge results from different sources
     */
    private mergeResults;
    /**
     * Handle violations asynchronously
     */
    private handleViolationsAsync;
    /**
     * Handle violations synchronously
     */
    private handleViolationsSync;
    /**
     * Handle a single violation
     */
    private handleSingleViolation;
    /**
     * Calculate result summary
     */
    private calculateSummary;
    /**
     * Determine overall status from results
     */
    private determineOverallStatus;
    /**
     * Update metrics with verification result
     */
    private updateMetrics;
    /**
     * Initialize metrics structure
     */
    private initializeMetrics;
    /**
     * Start periodic metrics collection
     */
    private startMetricsCollection;
}
