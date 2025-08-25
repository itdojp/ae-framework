/**
 * Risk Assessment Service
 * Phase 2.1: Evaluates risks associated with automated fixes
 */
import { FixStrategy, RepairAction, RiskAssessment, FailureArtifact } from './types.js';
export declare class RiskAssessmentService {
    /**
     * Assess the risk level of applying a fix strategy
     */
    assess(strategy: FixStrategy): Promise<number>;
    /**
     * Assess risk of a specific repair action
     */
    assessAction(action: RepairAction): Promise<RiskAssessment>;
    /**
     * Assess cumulative risk of multiple actions
     */
    assessBatch(actions: RepairAction[]): Promise<RiskAssessment>;
    /**
     * Generate risk report for a set of failures and proposed fixes
     */
    generateRiskReport(failures: FailureArtifact[], proposedActions: RepairAction[]): Promise<string>;
    /**
     * Check if a combination of actions creates additional risks
     */
    private checkInteractionRisks;
    private groupActionsByType;
}
