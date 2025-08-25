/**
 * MCP Server for Verify Agent
 * Exposes verification tools for Phase 5 of ae-framework
 */
interface VerifyServerOptions {
    name: string;
    version: string;
}
export declare class VerifyMCPServer {
    private server;
    private verifyAgent;
    constructor(options: VerifyServerOptions);
    private setupHandlers;
    private handleFullVerification;
    private handleRunTests;
    private handleCheckCoverage;
    private handleRunLinting;
    private handleRunTypeChecking;
    private handleRunSecurityScan;
    private handleRunPerformanceTests;
    private handleCheckAccessibility;
    private handleVerifyContracts;
    private handleVerifySpecifications;
    private handleRunMutationTests;
    private handleGenerateTraceabilityMatrix;
    private handleGetQualityMetrics;
    private buildVerificationRequest;
    private loadCodeFiles;
    private loadTestFiles;
    private loadSpecifications;
    private findFiles;
    private formatTraceabilityAsHTML;
    private formatTraceabilityAsCSV;
    run(): Promise<void>;
}
export {};
