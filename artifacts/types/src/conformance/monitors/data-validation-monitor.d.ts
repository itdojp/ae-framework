/**
 * Data Validation Monitor
 * Phase 2.2: Runtime monitor for data validation conformance rules
 */
import { ConformanceMonitor, ConformanceRule, RuntimeContext, VerificationResult } from '../types.js';
export declare class DataValidationMonitor implements ConformanceMonitor {
    readonly id = "data-validation-monitor";
    readonly name = "Data Validation Monitor";
    private rules;
    private schemaCache;
    /**
     * Verify data against validation rules
     */
    verify(data: any, context: RuntimeContext): Promise<VerificationResult>;
    /**
     * Check if this monitor can verify a specific rule
     */
    canVerify(ruleId: string): boolean;
    /**
     * Get all rules managed by this monitor
     */
    getRules(): ConformanceRule[];
    /**
     * Update a rule
     */
    updateRule(rule: ConformanceRule): Promise<void>;
    /**
     * Remove a rule
     */
    removeRule(ruleId: string): Promise<void>;
    /**
     * Validate data against a specific rule
     */
    private validateAgainstRule;
    /**
     * Parse validation schema from rule condition
     */
    private parseValidationSchema;
    /**
     * Apply constraints to Zod schema
     */
    private applyConstraints;
    /**
     * Perform custom validation logic when schema parsing fails
     */
    private performCustomValidation;
    /**
     * Generate validation suggestions based on Zod errors
     */
    private generateValidationSuggestions;
    /**
     * Map severity to priority
     */
    private mapSeverityToPriority;
    /**
     * Get memory usage (if available)
     */
    private getMemoryUsage;
    /**
     * Create common validation rules
     */
    static createCommonRules(): ConformanceRule[];
}
