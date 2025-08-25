/**
 * Verify Agent
 * Phase 5 of ae-framework: Automated verification and quality assurance
 */
export interface VerificationRequest {
    codeFiles: CodeFile[];
    testFiles: TestFile[];
    specifications?: Specification[];
    verificationTypes: VerificationType[];
    strictMode?: boolean;
    containerConfig?: {
        enabled: boolean;
        preferredEngine?: 'docker' | 'podman';
        buildImages?: boolean;
        projectPath?: string;
    };
}
export interface CodeFile {
    path: string;
    content: string;
    language: string;
}
export interface TestFile {
    path: string;
    content: string;
    type: 'unit' | 'integration' | 'e2e' | 'property' | 'contract';
}
export interface Specification {
    type: 'openapi' | 'asyncapi' | 'graphql' | 'tla' | 'alloy';
    content: string;
    path: string;
}
export type VerificationType = 'tests' | 'coverage' | 'linting' | 'typechecking' | 'security' | 'performance' | 'accessibility' | 'contracts' | 'specifications' | 'mutations' | 'rust-verification' | 'container-verification';
export interface VerificationResult {
    passed: boolean;
    results: VerificationCheck[];
    coverage: CoverageReport;
    metrics: QualityMetrics;
    issues: Issue[];
    suggestions: string[];
    traceability: TraceabilityMatrix;
}
export interface VerificationCheck {
    type: VerificationType;
    passed: boolean;
    details: any;
    errors?: string[];
    warnings?: string[];
}
export interface TestResult {
    total: number;
    passed: number;
    failed: number;
    duration: number;
    failures: Array<{
        message: string;
        fullTitle?: string;
    }>;
}
export interface LintResult {
    errors: number;
    warnings: number;
    messages: Array<{
        severity: 'error' | 'warning';
        message: string;
        line?: number;
        column?: number;
    }>;
}
export interface BenchmarkResult {
    responseTime: number;
    throughput: number;
    errorRate: number;
    cpuUsage: number;
    memoryUsage: number;
}
export interface CoverageReport {
    line: number;
    branch: number;
    function: number;
    statement: number;
    uncoveredFiles: string[];
}
export interface QualityMetrics {
    complexity: number;
    maintainability: number;
    reliability: number;
    security: number;
    performance: number;
    testability: number;
}
export interface Issue {
    severity: 'critical' | 'high' | 'medium' | 'low';
    type: string;
    file: string;
    line?: number;
    message: string;
    fix?: string;
}
export interface TraceabilityMatrix {
    requirements: TraceItem[];
    specifications: TraceItem[];
    tests: TraceItem[];
    code: TraceItem[];
    coverage: number;
}
export interface TraceItem {
    id: string;
    description: string;
    linkedTo: string[];
    covered: boolean;
}
export declare class VerifyAgent {
    private rustVerificationAgent;
    private containerAgent?;
    constructor(options?: {
        enableContainers?: boolean;
        containerConfig?: any;
    });
    /**
     * Run comprehensive verification suite
     */
    runFullVerification(request: VerificationRequest): Promise<VerificationResult>;
    /**
     * Run specific verification type
     */
    private runVerification;
    /**
     * Run all tests
     */
    runTests(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Check code coverage
     */
    checkCoverage(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run linting checks
     */
    runLinting(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run type checking
     */
    runTypeChecking(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run security checks
     */
    runSecurityChecks(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run performance tests
     */
    runPerformanceTests(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Check accessibility
     */
    checkAccessibility(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Verify contracts
     */
    verifyContracts(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Verify specifications
     */
    verifySpecifications(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run mutation testing
     */
    runMutationTesting(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Generate coverage report
     */
    generateCoverageReport(request: VerificationRequest): Promise<CoverageReport>;
    /**
     * Calculate quality metrics
     */
    calculateQualityMetrics(request: VerificationRequest): Promise<QualityMetrics>;
    /**
     * Build traceability matrix
     */
    buildTraceabilityMatrix(request: VerificationRequest): Promise<TraceabilityMatrix>;
    /**
     * Run Rust formal verification
     */
    runRustVerification(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run container-based verification
     */
    private runContainerVerification;
    /**
     * Generate improvement suggestions
     */
    private generateSuggestions;
    private runTestFile;
    private lintFile;
    private checkTypes;
    private scanForVulnerabilities;
    private checkDependencies;
    private scanForSecrets;
    private runBenchmarks;
    private runContractTest;
    private validateSpecification;
    private generateMutants;
    private testMutant;
    private extractRequirements;
    private calculateTraceabilityCoverage;
    private findRustProjectPath;
    private findElixirProjectPath;
    private detectProjectLanguage;
    private selectVerificationTools;
}
