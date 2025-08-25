/**
 * Evidence Validator for ae-framework
 * Validates AI suggestions with evidence from documentation and code
 */
export interface ValidationResult {
    isValid: boolean;
    evidence: Evidence[];
    confidence: number;
    suggestions?: string[];
}
export interface Evidence {
    type: 'documentation' | 'code' | 'test' | 'standard' | 'pattern';
    source: string;
    content: string;
    relevance: number;
    location?: {
        file?: string;
        line?: number;
        url?: string;
    };
}
export interface ValidationOptions {
    requireDocumentation?: boolean;
    requireTests?: boolean;
    minConfidence?: number;
    searchDepth?: number;
    includeExternalDocs?: boolean;
}
export declare class EvidenceValidator {
    private documentationCache;
    private patternDatabase;
    private readonly DEFAULT_MIN_CONFIDENCE;
    constructor();
    /**
     * Validate a claim or suggestion with evidence
     */
    validateClaim(claim: string, context: string, options?: ValidationOptions): Promise<ValidationResult>;
    /**
     * Validate code implementation against specifications
     */
    validateImplementation(code: string, specification: string): Promise<ValidationResult>;
    /**
     * Search official documentation for evidence
     */
    private searchOfficialDocs;
    /**
     * Find evidence in codebase
     */
    private findCodeEvidence;
    /**
     * Check test results for evidence
     */
    private checkTestResults;
    /**
     * Check against known patterns
     */
    private checkPatterns;
    /**
     * Check against coding standards
     */
    private checkStandards;
    /**
     * Calculate confidence score based on evidence
     */
    private calculateConfidence;
    /**
     * Check if evidence meets requirements
     */
    private meetsRequirements;
    /**
     * Generate suggestions when confidence is low
     */
    private generateSuggestions;
    /**
     * Sort evidence by relevance
     */
    private sortEvidenceByRelevance;
    /**
     * Extract keywords from claim
     */
    private extractKeywords;
    /**
     * Search local documentation
     */
    private searchLocalDocs;
    /**
     * Search package documentation
     */
    private searchPackageDocs;
    /**
     * Search codebase for patterns
     */
    private searchCodebase;
    /**
     * Find usage patterns in code
     */
    private findUsagePatterns;
    /**
     * Find test files
     */
    private findTestFiles;
    /**
     * Extract relevant tests from test file
     */
    private extractRelevantTests;
    /**
     * Run tests and get results
     */
    private runTests;
    /**
     * Find project standards file
     */
    private findStandardsFile;
    /**
     * Extract relevant standards
     */
    private extractRelevantStandards;
    /**
     * Check against common coding standards
     */
    private checkCommonStandards;
    /**
     * Match code against specification
     */
    private matchSpecification;
    /**
     * Validate against required patterns
     */
    private validatePatterns;
    /**
     * Detect anti-patterns in code
     */
    private detectAntiPatterns;
    /**
     * Check if claim matches a pattern
     */
    private matchesPattern;
    /**
     * Find keyword matches in content
     */
    private findKeywordMatches;
    /**
     * Scan directory for files
     */
    private scanDirectory;
    /**
     * Initialize pattern database with common patterns
     */
    private initializePatternDatabase;
    /**
     * Validate a solution with evidence
     */
    validateSolution(problem: string, solution: string, options?: ValidationOptions): Promise<ValidationResult>;
    /**
     * Get evidence summary
     */
    getEvidenceSummary(evidence: Evidence[]): string;
}
