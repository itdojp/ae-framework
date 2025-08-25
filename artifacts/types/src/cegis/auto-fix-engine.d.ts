/**
 * Auto-Fix Engine
 * Phase 2.1: Core engine for analyzing failures and applying automated fixes
 */
import { FailureArtifact, FixStrategy, FixResult, AutoFixConfig, AutoFixOptions, FailurePattern, FailureCategory } from './types.js';
export type { AutoFixOptions };
import { RiskAssessmentService } from './risk-assessment-service.js';
export declare class AutoFixEngine {
    private strategies;
    private riskAssessment;
    private config;
    constructor(config?: Partial<AutoFixConfig>, riskAssessment?: RiskAssessmentService);
    /**
     * Execute automatic fixes for the given failure artifacts
     */
    executeFixes(failures: FailureArtifact[], options?: AutoFixOptions): Promise<FixResult>;
    /**
     * Add a custom fix strategy
     */
    addStrategy(strategy: FixStrategy): void;
    /**
     * Get available strategies for a category
     */
    getStrategies(category: FailureCategory): FixStrategy[];
    /**
     * Analyze failure patterns to identify common issues
     */
    analyzeFailurePatterns(failures: FailureArtifact[]): Promise<FailurePattern[]>;
    private initializeDefaultStrategies;
    private filterValidFailures;
    private selectStrategies;
    private applyFixes;
    private applySingleStrategy;
    private applyAction;
    private backupFile;
    private groupByCategory;
    private findCommonPatterns;
    private getSuggestedStrategies;
    private calculatePatternConfidence;
    private generateSummary;
    private generateRecommendations;
    private generateReport;
}
