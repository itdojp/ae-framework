/**
 * Quality Policy Configuration Types
 */
export interface QualityThresholds {
    lines?: number;
    functions?: number;
    branches?: number;
    statements?: number;
    critical?: number;
    serious?: number;
    moderate?: number;
    minor?: number;
    total_warnings?: number;
    errors?: number;
    warnings?: number;
    performance?: number;
    accessibility?: number;
    bestPractices?: number;
    seo?: number;
    pwa?: string;
    pixelDifference?: number;
    failureThreshold?: number;
    uiViolations?: number;
    designSystemViolations?: number;
    accessibilityViolations?: number;
    mutationScore?: number;
    survived?: number;
    testToCodeRatio?: number;
    redGreenCycleCompliance?: number;
    high?: number;
    low?: number;
}
export interface QualityGate {
    description: string;
    enforcement: 'strict' | 'warn' | 'off';
    thresholds: QualityThresholds;
    tools: string[];
    phases: string[];
    enabledFromPhase?: string;
    excludePatterns?: string[];
    config?: Record<string, any>;
    targetPaths?: string[];
}
export interface QualityPolicy {
    $schema?: string;
    $id?: string;
    title: string;
    description: string;
    version: string;
    lastUpdated: string;
    quality: Record<string, QualityGate>;
    environments: Record<string, {
        description: string;
        overrides: Record<string, any>;
    }>;
    reporting: {
        outputDirectory: string;
        formats: string[];
        retention: {
            days: number;
            artifacts: string[];
        };
    };
    notifications: {
        onFailure: Record<string, any>;
        onThresholdChange: {
            requireApproval: boolean;
            reviewers: string[];
        };
    };
}
/**
 * Get the current quality profile from environment variable or parameter
 * @param environment - Optional environment override
 * @returns Profile name ('development', 'ci', 'production')
 */
export declare const getQualityProfile: (environment?: string) => string;
/**
 * Loads the centralized quality policy configuration
 * @param environment - Optional environment to apply overrides ('development', 'ci', 'production')
 * @returns Parsed quality policy with environment overrides applied
 */
export declare const loadQualityPolicy: (environment?: string) => QualityPolicy;
/**
 * Get quality gate configuration for a specific gate type
 * @param gateType - The type of quality gate (e.g., 'accessibility', 'coverage', 'lighthouse')
 * @param environment - Optional environment for overrides
 * @returns Quality gate configuration
 */
export declare const getQualityGate: (gateType: string, environment?: string) => QualityGate;
/**
 * Check if a quality gate should be enforced for the current phase
 * @param gateType - The type of quality gate
 * @param currentPhase - Current development phase
 * @param environment - Optional environment for overrides
 * @returns True if the gate should be enforced
 */
export declare const shouldEnforceGate: (gateType: string, currentPhase: string, environment?: string) => boolean;
/**
 * Get threshold value for a specific quality gate and metric
 * @param gateType - The type of quality gate
 * @param metric - The specific metric name
 * @param environment - Optional environment for overrides
 * @returns The threshold value
 */
export declare const getThreshold: (gateType: string, metric: string, environment?: string) => number | string | undefined;
/**
 * Generate command line arguments for threshold-based tools
 * @param gateType - The type of quality gate
 * @param environment - Optional environment for overrides
 * @returns Array of command line arguments
 */
export declare const getThresholdArgs: (gateType: string, environment?: string) => string[];
/**
 * Validate quality gate results against policy thresholds
 * @param gateType - The type of quality gate
 * @param results - The results to validate
 * @param environment - Optional environment for overrides
 * @returns Validation result with pass/fail status and messages
 */
export declare const validateQualityResults: (gateType: string, results: Record<string, number>, environment?: string) => {
    passed: boolean;
    failures: string[];
    warnings: string[];
};
/**
 * Get current development phase from project state
 * @returns Current phase identifier
 */
export declare const getCurrentPhase: () => string;
/**
 * Export main function for backward compatibility and CLI usage
 */
export default loadQualityPolicy;
