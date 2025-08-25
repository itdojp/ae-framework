/**
 * Approval Service for managing phase approvals in ae-framework
 */
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { EventEmitter } from 'events';
export interface ApprovalRequest {
    phase: PhaseType;
    projectId: string;
    projectName?: string;
    requestedBy: string;
    requestedAt: Date;
    artifacts: string[];
    summary?: string;
    metadata?: Record<string, any>;
}
export interface ApprovalResponse {
    approved: boolean;
    approvedBy: string;
    approvedAt: Date;
    notes?: string;
    conditions?: string[];
}
export interface ApprovalPolicy {
    requireMultipleApprovers?: boolean;
    minApprovers?: number;
    approverRoles?: string[];
    autoApproveConditions?: ApprovalCondition[];
    timeoutHours?: number;
    escalationPath?: string[];
}
export interface ApprovalCondition {
    type: 'test-coverage' | 'code-review' | 'security-scan' | 'custom';
    threshold?: number;
    customCheck?: (artifacts: string[]) => Promise<boolean>;
}
export interface PendingApproval {
    request: ApprovalRequest;
    policy: ApprovalPolicy;
    status: 'pending' | 'approved' | 'rejected' | 'expired';
    responses: ApprovalResponse[];
    createdAt: Date;
    expiresAt?: Date;
}
export declare class ApprovalService extends EventEmitter {
    private phaseStateManager;
    private approvalsDir;
    private pendingApprovals;
    private policies;
    constructor(projectRoot?: string, phaseStateManager?: PhaseStateManager);
    /**
     * Initialize default approval policies
     */
    private initializeDefaultPolicies;
    /**
     * Set custom policy for a phase
     */
    setPolicy(phase: PhaseType, policy: ApprovalPolicy): void;
    /**
     * Request approval for a phase
     */
    requestApproval(phase: PhaseType, requestedBy: string, summary?: string): Promise<ApprovalRequest>;
    /**
     * Approve a phase
     */
    approve(phase: PhaseType, approvedBy: string, notes?: string, conditions?: string[]): Promise<void>;
    /**
     * Reject a phase approval
     */
    reject(phase: PhaseType, rejectedBy: string, reason: string): Promise<void>;
    /**
     * Get pending approvals
     */
    getPendingApprovals(): Promise<PendingApproval[]>;
    /**
     * Get approval history for a phase
     */
    getApprovalHistory(phase: PhaseType): Promise<PendingApproval[]>;
    /**
     * Check auto-approval conditions
     */
    private checkAutoApproval;
    /**
     * Evaluate a single approval condition
     */
    private evaluateCondition;
    /**
     * Check test coverage (placeholder implementation)
     */
    private checkTestCoverage;
    /**
     * Check code review status (placeholder implementation)
     */
    private checkCodeReview;
    /**
     * Check security scan results (placeholder implementation)
     */
    private checkSecurityScan;
    /**
     * Auto-approve a phase
     */
    private autoApprove;
    /**
     * Generate approval ID
     */
    private generateApprovalId;
    /**
     * Save pending approval to disk
     */
    private savePendingApproval;
    /**
     * Remove pending approval from disk
     */
    private removePendingApproval;
    /**
     * Load pending approvals from disk
     */
    private loadPendingApprovals;
    /**
     * Check for expired approvals
     */
    checkExpiredApprovals(): Promise<void>;
    /**
     * Get approval status for a phase
     */
    getApprovalStatus(phase: PhaseType): Promise<{
        required: boolean;
        status: 'not-required' | 'pending' | 'approved' | 'rejected' | 'expired';
        details?: PendingApproval;
    }>;
}
