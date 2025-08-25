/**
 * Phase 4: Code Generation & Implementation
 *
 * Uses ae-framework's CodeGenerationAgent to systematically generate
 * fixes for TypeScript compilation errors based on formal specifications
 * and TDD guidance from Phase 3.
 */
export interface Phase4CodeFix {
    file: string;
    errorCode: string;
    errorLine: number;
    errorDescription: string;
    generatedFix: string;
    confidence: number;
    testCoverage: number;
    estimatedImpact: 'low' | 'medium' | 'high';
}
export interface Phase4Results {
    fixes: Phase4CodeFix[];
    errorsResolved: number;
    errorsRemaining: number;
    codeQualityImprovement: number;
    generatedTests: string[];
    overallSuccess: boolean;
}
export declare class Phase4CodeGeneration {
    private codeGenAgent;
    private appliedFixes;
    constructor();
    /**
     * Execute Phase 4: Systematic code generation for TypeScript error resolution
     */
    executePhase4(): Promise<Phase4Results>;
    /**
     * Analyze current TypeScript errors to identify patterns and priorities
     */
    private analyzeCurrentErrors;
    /**
     * Generate systematic fixes using CodeGenerationAgent
     */
    private generateSystematicFixes;
    /**
     * Generate fix for a specific TypeScript error
     */
    private generateFixForError;
    /**
     * Generate specific fix based on error type
     */
    private generateSpecificFix;
    /**
     * Generate null safety fix
     */
    private generateNullSafetyFix;
    /**
     * Generate type compatibility fix
     */
    private generateTypeCompatibilityFix;
    /**
     * Generate object literal fix
     */
    private generateObjectLiteralFix;
    /**
     * Generate undefined check fix
     */
    private generateUndefinedCheckFix;
    /**
     * Generate missing properties fix
     */
    private generateMissingPropertiesFix;
    /**
     * Apply high-confidence fixes
     */
    private applyHighConfidenceFixes;
    /**
     * Verify fixes with tests
     */
    private verifyFixesWithTests;
    /**
     * Get current TypeScript error count
     */
    private getCurrentErrorCount;
    /**
     * Categorize error severity
     */
    private categorizeErrorSeverity;
    /**
     * Estimate impact of fix
     */
    private estimateImpact;
    /**
     * Calculate quality improvement score
     */
    private calculateQualityImprovement;
    /**
     * Generate comprehensive Phase 4 report
     */
    generatePhase4Report(results: Phase4Results): string;
}
export default Phase4CodeGeneration;
