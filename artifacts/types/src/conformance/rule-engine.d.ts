/**
 * Conformance Rule Engine
 * Phase 2.2: Core engine for executing conformance rules and detecting violations
 */
import { ConformanceRule, ConformanceConfig, RuntimeContext, VerificationResult, ConformanceVerificationResult, ConformanceRuleCategory } from './types.js';
export declare class ConformanceRuleEngine {
    private rules;
    private config;
    private executionCache;
    private metrics;
    constructor(config: ConformanceConfig);
    /**
     * Add a conformance rule to the engine
     */
    addRule(rule: ConformanceRule): Promise<void>;
    /**
     * Remove a rule from the engine
     */
    removeRule(ruleId: string): Promise<void>;
    /**
     * Update an existing rule
     */
    updateRule(rule: ConformanceRule): Promise<void>;
    /**
     * Get all loaded rules
     */
    getRules(): ConformanceRule[];
    /**
     * Get rules by category
     */
    getRulesByCategory(category: ConformanceRuleCategory): ConformanceRule[];
    /**
     * Verify data against all applicable rules
     */
    verifyConformance(data: any, context: RuntimeContext, ruleIds?: string[]): Promise<ConformanceVerificationResult>;
    /**
     * Verify a single rule
     */
    verifyRule(ruleId: string, data: any, context: RuntimeContext): Promise<VerificationResult>;
    /**
     * Execute a single conformance rule
     */
    private executeRule;
    /**
     * Evaluate rule condition against data
     */
    private evaluateRule;
    /**
     * Evaluate a condition expression
     */
    private evaluateCondition;
    /**
     * Safe expression evaluation (simplified)
     */
    private safeEvaluate;
    /**
     * Get nested property from object
     */
    private getNestedProperty;
    /**
     * Execute rules in parallel with concurrency limits
     */
    private executeRulesParallel;
    /**
     * Select rules to execute based on configuration
     */
    private selectRules;
    /**
     * Apply sampling configuration
     */
    private applySampling;
    /**
     * Helper methods
     */
    private executeWithTimeout;
    private createSkippedResult;
    private generateCacheKey;
    private isCacheValid;
    private clearRuleCache;
    private getMemoryUsage;
    private getValidatorHelpers;
    private getUtilityHelpers;
    private generateRemediationSuggestions;
    private mapSeverityToPriority;
    private determineOverallStatus;
    private generateSummary;
    private updateMetrics;
    private getRuleFailureRate;
    private shuffleArray;
    /**
     * Get engine metrics
     */
    getMetrics(): Record<string, number>;
    /**
     * Reset engine metrics
     */
    resetMetrics(): void;
}
