/**
 * Phase 2: Natural Language Requirements Analysis
 *
 * Uses the ae-framework's NaturalLanguageTaskAdapter to systematically
 * analyze requirements for TypeScript error resolution and framework improvement.
 */
import { ProcessedRequirements } from '../agents/natural-language-task-adapter.js';
export interface Phase2AnalysisResult {
    errorRequirements: ProcessedRequirements;
    frameworkRequirements: ProcessedRequirements;
    architecturalRequirements: ProcessedRequirements;
    prioritizedActions: {
        high: string[];
        medium: string[];
        low: string[];
    };
    systematicPlan: {
        phase: string;
        description: string;
        tasks: string[];
        expectedOutcome: string;
    }[];
}
export declare class Phase2RequirementsAnalyzer {
    private adapter;
    constructor();
    /**
     * Perform comprehensive Phase 2 requirements analysis
     */
    analyzeRequirements(): Promise<Phase2AnalysisResult>;
    /**
     * Analyze requirements for TypeScript error resolution
     */
    private analyzeTypeScriptErrorRequirements;
    /**
     * Analyze framework architectural requirements
     */
    private analyzeFrameworkRequirements;
    /**
     * Analyze architectural improvement requirements
     */
    private analyzeArchitecturalRequirements;
    /**
     * Prioritize actions based on requirements analysis
     */
    private prioritizeActions;
    /**
     * Create systematic improvement plan
     */
    private createSystematicPlan;
    /**
     * Generate comprehensive requirements report
     */
    generateReport(results: Phase2AnalysisResult): string;
}
export default Phase2RequirementsAnalyzer;
