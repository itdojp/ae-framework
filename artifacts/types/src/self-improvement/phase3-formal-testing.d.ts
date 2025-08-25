/**
 * Phase 3: Formal Specification & Testing Phase
 *
 * Uses ae-framework's FormalAgent and TDDAgent to create formal specifications
 * and automated tests for TypeScript error resolution and quality improvement.
 */
export interface Phase3Result {
    formalSpecifications: {
        typeScriptErrorResolution: any;
        codeQualityImprovement: any;
        testCoverageEnhancement: any;
    };
    generatedTests: {
        unitTests: string[];
        integrationTests: string[];
        typeValidationTests: string[];
    };
    validationResults: {
        specificationCompliance: boolean;
        testCoverage: number;
        qualityScore: number;
        errors: string[];
        warnings: string[];
    };
}
export declare class Phase3FormalTesting {
    private formalAgent;
    private tddAgent;
    private validationAdapter;
    constructor();
    /**
     * Execute Phase 3: Formal Specification and Testing
     */
    executePhase3(): Promise<Phase3Result>;
    /**
     * Generate formal specifications for TypeScript error resolution
     */
    private generateFormalSpecifications;
    /**
     * Generate automated tests using TDDAgent
     */
    private generateAutomatedTests;
    /**
     * Validate specifications and generated tests
     */
    private validateSpecificationsAndTests;
    /**
     * Calculate overall quality score
     */
    private calculateQualityScore;
    /**
     * Generate comprehensive report
     */
    generatePhase3Report(results: Phase3Result): string;
}
export default Phase3FormalTesting;
