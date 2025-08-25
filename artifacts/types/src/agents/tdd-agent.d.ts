/**
 * TDD Agent for Claude Code
 *
 * This agent provides intelligent TDD guidance and enforcement specifically
 * designed for Claude Code's Task tool and workflow integration.
 */
export interface TDDAgentConfig {
    strictMode: boolean;
    coverageThreshold: number;
    testFramework: 'vitest' | 'jest' | 'mocha';
    blockCodeWithoutTests: boolean;
    enableRealTimeGuidance: boolean;
}
export interface TDDContext {
    projectPath: string;
    currentPhase: string;
    feature?: string;
    lastAction?: string;
    testResults?: TestResults;
}
export interface TestResults {
    passed: number;
    failed: number;
    coverage: number;
    errors: string[];
}
export interface TDDTask {
    type: 'validate' | 'guide' | 'enforce' | 'analyze';
    description: string;
    priority: 'high' | 'medium' | 'low';
    action: string;
    expectedOutcome: string;
}
export declare class TDDAgent {
    private config;
    private context;
    constructor(config: TDDAgentConfig, context: TDDContext);
    /**
     * Main entry point for TDD guidance requests
     * Designed to be called by Claude Code's Task tool
     */
    provideTDDGuidance(request: string): Promise<{
        analysis: string;
        tasks: TDDTask[];
        nextSteps: string[];
        warnings: string[];
    }>;
    /**
     * Real-time TDD enforcement during development
     * Called when Claude Code detects code changes
     */
    enforceRealTimeTDD(event: {
        type: 'file_created' | 'file_modified' | 'test_run';
        file?: string;
        content?: string;
    }): Promise<{
        shouldBlock: boolean;
        message: string;
        correctionTasks: TDDTask[];
    }>;
    /**
     * Generate step-by-step TDD guidance for a specific feature
     */
    generateFeatureTDDPlan(feature: string): Promise<{
        phases: Array<{
            name: string;
            description: string;
            tasks: TDDTask[];
            validationCriteria: string[];
        }>;
        riskFactors: string[];
        estimatedEffort: string;
    }>;
    /**
     * Intelligent test suggestion based on code analysis
     */
    suggestTestsForCode(codeFile: string, codeContent: string): Promise<{
        testFile: string;
        testContent: string;
        testCases: Array<{
            name: string;
            description: string;
            importance: 'critical' | 'important' | 'nice-to-have';
            template: string;
        }>;
    }>;
    /**
     * Continuous TDD compliance monitoring
     */
    monitorTDDCompliance(): Promise<{
        complianceScore: number;
        violations: Array<{
            type: string;
            severity: 'error' | 'warning' | 'info';
            description: string;
            recommendation: string;
            autoFixAvailable: boolean;
        }>;
        trends: {
            improving: boolean;
            recentViolations: number;
            coverageTrend: 'up' | 'down' | 'stable';
        };
    }>;
    private analyzeCurrentState;
    private generateTDDTasks;
    private generateNextSteps;
    private identifyWarnings;
    private formatAnalysis;
    private handleFileCreation;
    private handleFileModification;
    private handleTestRun;
    private generateRedPhaseTasks;
    private generateGreenPhaseTasks;
    private generateRefactorPhaseTasks;
    private identifyRiskFactors;
    private estimateEffort;
    private analyzeCodeStructure;
    private generateTestFilePath;
    private generateTestCases;
    private generateTestFileContent;
    private checkForCorrespondingTest;
    private detectViolations;
    private calculateComplianceScore;
    private analyzeTrends;
}
