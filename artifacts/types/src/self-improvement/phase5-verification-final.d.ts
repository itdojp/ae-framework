/**
 * Phase 5: Verification & Final Error Resolution
 *
 * Systematic approach to resolving remaining TypeScript errors through
 * targeted manual fixes, comprehensive testing, and quality validation.
 * Final verification of ae-framework self-improvement process.
 */
export interface TypeScriptError {
    file: string;
    line: number;
    column: number;
    code: string;
    message: string;
    severity: 'error' | 'warning';
    category: 'type-safety' | 'interface' | 'import' | 'syntax' | 'other';
}
export interface ErrorFix {
    file: string;
    line: number;
    errorCode: string;
    originalLine: string;
    fixedLine: string;
    explanation: string;
    riskLevel: 'low' | 'medium' | 'high';
    testRequired: boolean;
}
export interface Phase5Results {
    initialErrorCount: number;
    finalErrorCount: number;
    errorsResolved: number;
    appliedFixes: ErrorFix[];
    verificationResults: {
        compilationSuccess: boolean;
        testsPass: boolean;
        qualityMetrics: {
            codeComplexity: number;
            maintainabilityScore: number;
            testCoverage: number;
        };
    };
    overallSuccess: boolean;
    completionTime: number;
}
export declare class Phase5VerificationFinal {
    private appliedFixes;
    private startTime;
    constructor();
    /**
     * Execute Phase 5: Complete verification and final error resolution
     */
    executePhase5(): Promise<Phase5Results>;
    /**
     * Analyze all TypeScript errors in the project
     */
    private analyzeAllErrors;
    /**
     * Categorize errors by type and priority
     */
    private categorizeErrors;
    /**
     * Apply critical fixes for high-priority errors
     */
    private applyCriticalFixes;
    /**
     * Apply systematic fixes by error pattern
     */
    private applySystematicFixes;
    /**
     * Fix undefined access patterns
     */
    private fixUndefinedAccess;
    /**
     * Fix type assignment issues
     */
    private fixTypeAssignment;
    /**
     * Fix interface property errors
     */
    private fixInterfaceProperty;
    /**
     * Fix missing properties errors
     */
    private fixMissingProperties;
    /**
     * Apply a fix to the file
     */
    private applyFix;
    /**
     * Perform final verification
     */
    private performFinalVerification;
    /**
     * Get current error count
     */
    private getCurrentErrorCount;
    /**
     * Categorize error type
     */
    private categorizeErrorType;
    /**
     * Generate comprehensive Phase 5 report
     */
    generatePhase5Report(results: Phase5Results): string;
}
export default Phase5VerificationFinal;
