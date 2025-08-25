/**
 * Phase 1: Codebase Analysis using NaturalLanguageTaskAdapter
 *
 * This module performs a comprehensive analysis of the ae-framework codebase
 * using the natural language processing capabilities to identify patterns,
 * issues, and improvement opportunities.
 */
export interface CodebaseAnalysisResult {
    summary: string;
    analysis: string;
    recommendations: string[];
    nextActions: string[];
    warnings: string[];
    shouldBlockProgress: boolean;
    typeScriptErrors: number;
    testCoverage: {
        files: number;
        coverage: number;
    };
    codeQuality: {
        score: number;
        issues: string[];
    };
}
export declare class CodebaseAnalyzer {
    private adapter;
    constructor();
    /**
     * Perform comprehensive analysis of the ae-framework codebase
     */
    analyzeCodebase(): Promise<CodebaseAnalysisResult>;
    /**
     * Count TypeScript compilation errors by running tsc
     */
    private countTypeScriptErrors;
    /**
     * Analyze test coverage by counting test files and estimating coverage
     */
    private analyzeTestCoverage;
    /**
     * Analyze code quality by identifying common issues
     */
    private analyzeCodeQuality;
    /**
     * Extract requirements-like statements from the codebase
     */
    private extractCodebaseRequirements;
    /**
     * Find all test files in the project
     */
    private findTestFiles;
    /**
     * Find all source files in the project
     */
    private findSourceFiles;
    /**
     * Generate detailed report from analysis results
     */
    generateReport(results: CodebaseAnalysisResult): string;
}
export default CodebaseAnalyzer;
