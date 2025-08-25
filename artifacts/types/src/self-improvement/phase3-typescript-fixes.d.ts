/**
 * Phase 3: Systematic TypeScript Error Resolution
 *
 * Uses the formal specifications and TDD guidance to systematically
 * resolve TypeScript compilation errors.
 */
export interface TypeScriptFix {
    file: string;
    line: number;
    errorCode: string;
    description: string;
    originalCode: string;
    fixedCode: string;
    confidence: 'high' | 'medium' | 'low';
    riskLevel: 'safe' | 'moderate' | 'risky';
}
export interface Phase3FixResults {
    fixesApplied: TypeScriptFix[];
    errorsRemaining: number;
    errorsFixed: number;
    testsCreated: string[];
    qualityScore: number;
}
export declare class Phase3TypeScriptFixer {
    private appliedFixes;
    /**
     * Execute systematic TypeScript error resolution
     */
    executeSystematicFixes(): Promise<Phase3FixResults>;
    /**
     * Fix Intent Agent undefined array access errors
     */
    private fixIntentAgentUndefinedAccess;
    /**
     * Fix Benchmark Runner type mismatch
     */
    private fixBenchmarkRunnerTypeMismatch;
    /**
     * Check if Enhanced State Manager needs fixing
     */
    private fixEnhancedStateManagerIfNeeded;
    /**
     * Count current TypeScript errors
     */
    private countCurrentErrors;
    /**
     * Calculate quality score based on fixes applied
     */
    private calculateQualityScore;
    /**
     * Generate comprehensive fix report
     */
    generateFixReport(results: Phase3FixResults): string;
}
export default Phase3TypeScriptFixer;
