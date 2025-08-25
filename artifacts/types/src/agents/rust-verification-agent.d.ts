/**
 * Enhanced Rust Formal Verification Agent
 * Phase 2 of Issue #33: Advanced Rust formal verification with Prusti, Kani, and CBMC
 */
export interface RustVerificationRequest {
    projectPath: string;
    sourceFiles: RustSourceFile[];
    verificationTools: VerificationTool[];
    options: VerificationOptions;
}
export interface RustSourceFile {
    path: string;
    content: string;
    annotations?: RustAnnotation[];
}
export interface RustAnnotation {
    type: 'precondition' | 'postcondition' | 'invariant' | 'assert' | 'assume' | 'contract';
    line: number;
    content: string;
}
export type VerificationTool = 'prusti' | 'kani' | 'cbmc' | 'miri' | 'loom';
export interface VerificationOptions {
    timeout?: number;
    memoryLimit?: number;
    unwindLimit?: number;
    strictMode?: boolean;
    generateReport?: boolean;
    checkOverflow?: boolean;
    checkConcurrency?: boolean;
}
export interface RustVerificationResult {
    tool: VerificationTool;
    success: boolean;
    results: VerificationCheck[];
    performance: PerformanceMetrics;
    report?: VerificationReport;
    errors: VerificationError[];
    warnings: VerificationWarning[];
}
export interface VerificationCheck {
    type: 'safety' | 'liveness' | 'functional' | 'memory' | 'concurrency';
    description: string;
    status: 'passed' | 'failed' | 'timeout' | 'unknown';
    location?: SourceLocation;
    details?: string;
    counterexample?: string;
}
export interface PerformanceMetrics {
    executionTime: number;
    memoryUsage: number;
    codeSize: number;
    verificationComplexity: 'low' | 'medium' | 'high' | 'very-high';
}
export interface VerificationReport {
    summary: string;
    statistics: {
        totalChecks: number;
        passedChecks: number;
        failedChecks: number;
        coverage: number;
    };
    recommendations: string[];
    toolSpecificResults: Record<string, any>;
}
export interface VerificationError {
    tool: VerificationTool;
    type: string;
    message: string;
    location?: SourceLocation;
    severity: 'critical' | 'error' | 'warning';
}
export interface VerificationWarning {
    tool: VerificationTool;
    type: string;
    message: string;
    location?: SourceLocation;
    suggestion?: string;
}
export interface SourceLocation {
    file: string;
    line: number;
    column: number;
    function?: string;
}
export declare class RustVerificationAgent {
    private installedTools;
    constructor();
    /**
     * Main verification entry point - runs multiple verification tools
     */
    verifyRustProject(request: RustVerificationRequest): Promise<RustVerificationResult[]>;
    /**
     * Run Prusti verification (Rust ownership and borrowing verification)
     */
    private runPrustiVerification;
    /**
     * Run Kani verification (bounded model checking for Rust)
     */
    private runKaniVerification;
    /**
     * Run CBMC verification (bounded model checking)
     */
    private runCBMCVerification;
    /**
     * Run Miri verification (interpreter for unsafe Rust)
     */
    private runMiriVerification;
    /**
     * Detect installed verification tools
     */
    private detectInstalledTools;
    private runVerificationTool;
    private runLoomVerification;
    private validateProjectStructure;
    private prepareProjectForVerification;
    private addAnnotationsToFile;
    private formatAnnotation;
    private parsePrustiOutput;
    private parseKaniOutput;
    private parseCBMCOutput;
    private parseMiriOutput;
    private estimateMemoryUsage;
    private calculateCodeSize;
    private assessComplexity;
    private generateCombinedReport;
    private generateSummary;
    /**
     * Get list of available verification tools
     */
    getAvailableTools(): VerificationTool[];
    /**
     * Check if a specific tool is available
     */
    isToolAvailable(tool: VerificationTool): boolean;
}
