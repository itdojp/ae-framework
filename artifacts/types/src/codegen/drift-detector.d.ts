/**
 * Drift Detection System
 * Monitors changes in generated code and specifications
 */
export interface DriftConfig {
    /** Directory containing generated code */
    codeDir: string;
    /** Path to AE-IR specification file */
    specPath: string;
    /** Path to codegen manifest */
    manifestPath?: string;
    /** Files to ignore during drift detection */
    ignorePatterns?: string[];
    /** Enable detailed reporting */
    verbose?: boolean;
    /** Auto-fix simple drift issues */
    autoFix?: boolean;
}
export interface FileChangeInfo {
    /** File path relative to codeDir */
    filePath: string;
    /** Change type */
    changeType: 'modified' | 'added' | 'deleted' | 'renamed';
    /** Previous hash (for modified files) */
    previousHash?: string;
    /** Current hash */
    currentHash?: string;
    /** Change timestamp */
    detectedAt: string;
    /** Lines changed (approximate) */
    linesChanged?: number;
    /** Confidence level of detection */
    confidence: 'high' | 'medium' | 'low';
}
export interface DriftReport {
    /** Overall drift status */
    status: 'no_drift' | 'minor_drift' | 'major_drift' | 'critical_drift';
    /** Summary statistics */
    summary: {
        totalFiles: number;
        changedFiles: number;
        addedFiles: number;
        deletedFiles: number;
        unchangedFiles: number;
    };
    /** Detailed change information */
    changes: FileChangeInfo[];
    /** Specification change detection */
    specificationChange: {
        hasChanged: boolean;
        previousHash?: string;
        currentHash?: string;
        changesSince?: string;
    };
    /** Recommendations */
    recommendations: string[];
    /** Generated at timestamp */
    generatedAt: string;
}
export declare class DriftDetector {
    private config;
    constructor(config: DriftConfig);
    /**
     * Perform comprehensive drift detection
     */
    detectDrift(): Promise<DriftReport>;
    /**
     * Detect changes in the specification file
     */
    private detectSpecificationChanges;
    /**
     * Scan for changes in existing files
     */
    private scanFileChanges;
    /**
     * Detect new files and structural changes
     */
    private detectStructuralChanges;
    /**
     * Calculate drift severity status
     */
    private calculateDriftStatus;
    /**
     * Generate actionable recommendations
     */
    private generateRecommendations;
    /**
     * Auto-fix minor drift issues
     */
    private autoFixMinorIssues;
    /**
     * Helper methods
     */
    private loadManifest;
    private calculateHash;
    private estimateLinesChanged;
    private calculateChangeConfidence;
    /**
     * Attempts to determine the original line count from the manifest or original file content.
     */
    private getOriginalLineCount;
    private isLikelyGeneratedFile;
    private generateSummary;
    private printReport;
}
