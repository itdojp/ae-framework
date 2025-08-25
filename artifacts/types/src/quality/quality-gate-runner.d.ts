/**
 * Quality Gate Runner
 * Executes quality gates based on centralized policy configuration
 */
import { QualityPolicyLoader, QualityReport } from './policy-loader.js';
export interface QualityGateExecutionOptions {
    environment?: string;
    gates?: string[];
    parallel?: boolean;
    timeout?: number;
    dryRun?: boolean;
    verbose?: boolean;
    outputDir?: string;
}
export declare class QualityGateRunner {
    private policyLoader;
    private results;
    constructor(policyLoader?: QualityPolicyLoader);
    /**
     * Execute quality gates for environment
     */
    executeGates(options?: QualityGateExecutionOptions): Promise<QualityReport>;
    /**
     * Execute a single quality gate
     */
    private executeGate;
    /**
     * Execute a command with timeout
     */
    private executeCommand;
    /**
     * Parse command string into executable and arguments safely
     */
    private parseCommand;
    /**
     * Validate shell commands for security
     */
    private validateShellCommand;
    /**
     * Parse gate execution result
     */
    private parseGateResult;
    /**
     * Parse coverage results
     */
    private parseCoverageResult;
    /**
     * Parse linting results
     */
    private parseLintingResult;
    /**
     * Parse security results
     */
    private parseSecurityResult;
    /**
     * Parse performance results
     */
    private parsePerformanceResult;
    /**
     * Parse accessibility results
     */
    private parseAccessibilityResult;
    /**
     * Save quality report to file
     */
    private saveReport;
    /**
     * Generate empty report for when no gates are found
     */
    private generateEmptyReport;
    /**
     * Print execution summary
     */
    private printSummary;
}
export declare function runQualityGatesCLI(args: string[]): Promise<void>;
