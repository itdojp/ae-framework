/**
 * API Contract Monitor
 * Phase 2.2: Runtime monitor for API contract conformance verification
 */
import { ConformanceMonitor, ConformanceRule, RuntimeContext, VerificationResult } from '../types.js';
interface APIContractSpec {
    method: string;
    path: string;
    requestSchema?: any;
    responseSchema?: any;
    headers?: Record<string, string>;
    statusCodes?: number[];
    timeout?: number;
    rateLimit?: {
        requests: number;
        window: number;
    };
}
export declare class APIContractMonitor implements ConformanceMonitor {
    readonly id = "api-contract-monitor";
    readonly name = "API Contract Monitor";
    private rules;
    private contractSpecs;
    private rateLimitTracker;
    /**
     * Verify API call against contract rules
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
     * Add API contract specification
     */
    addContractSpec(path: string, spec: APIContractSpec): void;
    /**
     * Remove API contract specification
     */
    removeContractSpec(path: string): void;
    /**
     * Validate API call against contract
     */
    private validateAPIContract;
    /**
     * Check if data is valid API call data
     */
    private isAPICallData;
    /**
     * Find matching contract specification
     */
    private findMatchingContract;
    /**
     * Check if path matches pattern (supports basic wildcards)
     */
    private matchesPathPattern;
    /**
     * Normalize path pattern for consistent storage
     */
    private normalizePathPattern;
    /**
     * Find missing required headers
     */
    private findMissingHeaders;
    /**
     * Check rate limiting
     */
    private checkRateLimit;
    /**
     * Validate data against schema
     */
    private validateSchema;
    /**
     * Validate path parameters
     */
    private validatePathParameters;
    /**
     * Create violation details
     */
    private createViolation;
    /**
     * Generate API-specific suggestions
     */
    private generateAPISuggestions;
    /**
     * Map severity to priority
     */
    private mapSeverityToPriority;
    /**
     * Get memory usage (if available)
     */
    private getMemoryUsage;
    /**
     * Create common API contract rules
     */
    static createCommonRules(): ConformanceRule[];
}
export {};
