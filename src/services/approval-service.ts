/**
 * Approval Service for managing phase approvals in ae-framework
 */

import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { EventEmitter } from 'events';
import * as fs from 'fs';
import * as path from 'path';

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

export class ApprovalService extends EventEmitter {
  private phaseStateManager: PhaseStateManager;
  private approvalsDir: string;
  private pendingApprovals: Map<string, PendingApproval> = new Map();
  private policies: Map<PhaseType, ApprovalPolicy> = new Map();

  constructor(projectRoot?: string, phaseStateManager?: PhaseStateManager) {
    super();
    const root = projectRoot || process.cwd();
    this.phaseStateManager = phaseStateManager || new PhaseStateManager(root);
    this.approvalsDir = path.join(root, '.ae', 'approvals');
    this.initializeDefaultPolicies();
  }

  /**
   * Initialize default approval policies
   */
  private initializeDefaultPolicies(): void {
    // Default policies for each phase
    this.policies.set('intent', {
      requireMultipleApprovers: false,
      minApprovers: 1,
      timeoutHours: 48,
    });

    this.policies.set('formal', {
      requireMultipleApprovers: false,
      minApprovers: 1,
      timeoutHours: 48,
    });

    this.policies.set('test', {
      requireMultipleApprovers: false,
      minApprovers: 1,
      autoApproveConditions: [
        { type: 'test-coverage', threshold: 80 }
      ],
      timeoutHours: 24,
    });

    this.policies.set('code', {
      requireMultipleApprovers: true,
      minApprovers: 2,
      autoApproveConditions: [
        { type: 'code-review' }
      ],
      timeoutHours: 48,
    });

    this.policies.set('verify', {
      requireMultipleApprovers: false,
      minApprovers: 1,
      autoApproveConditions: [
        { type: 'security-scan' }
      ],
      timeoutHours: 24,
    });

    this.policies.set('operate', {
      requireMultipleApprovers: true,
      minApprovers: 2,
      timeoutHours: 72,
    });
  }

  /**
   * Set custom policy for a phase
   */
  setPolicy(phase: PhaseType, policy: ApprovalPolicy): void {
    this.policies.set(phase, policy);
  }

  /**
   * Request approval for a phase
   */
  async requestApproval(
    phase: PhaseType,
    requestedBy: string,
    summary?: string
  ): Promise<ApprovalRequest> {
    const state = await this.phaseStateManager.getCurrentState();
    if (!state) {
      throw new Error('No project state found');
    }

    const phaseStatus = state.phaseStatus[phase];
    if (!phaseStatus.completed) {
      throw new Error(`Phase ${phase} must be completed before requesting approval`);
    }

    if (phaseStatus.approved) {
      throw new Error(`Phase ${phase} is already approved`);
    }

    const request: ApprovalRequest = {
      phase,
      projectId: state.projectId,
      projectName: state.projectName,
      requestedBy,
      requestedAt: new Date(),
      artifacts: phaseStatus.artifacts,
      summary,
      metadata: state.metadata,
    };

    // Check auto-approval conditions
    const policy = this.policies.get(phase) || {};
    const autoApproved = await this.checkAutoApproval(request, policy);

    if (autoApproved) {
      await this.autoApprove(phase, 'System (auto-approved)', 'All conditions met');
      this.emit('approval:auto', { phase, request });
      return request;
    }

    // Create pending approval
    const approvalId = this.generateApprovalId(phase, state.projectId);
    const expiresAt = policy.timeoutHours
      ? new Date(Date.now() + policy.timeoutHours * 60 * 60 * 1000)
      : undefined;

    const pendingApproval: PendingApproval = {
      request,
      policy,
      status: 'pending',
      responses: [],
      createdAt: new Date(),
      expiresAt,
    };

    this.pendingApprovals.set(approvalId, pendingApproval);
    await this.savePendingApproval(approvalId, pendingApproval);

    // Emit event for notification systems
    this.emit('approval:requested', { approvalId, request, policy });

    return request;
  }

  /**
   * Approve a phase
   */
  async approve(
    phase: PhaseType,
    approvedBy: string,
    notes?: string,
    conditions?: string[]
  ): Promise<void> {
    const state = await this.phaseStateManager.getCurrentState();
    if (!state) {
      throw new Error('No project state found');
    }

    const approvalId = this.generateApprovalId(phase, state.projectId);
    const pendingApproval = this.pendingApprovals.get(approvalId);

    if (pendingApproval) {
      const response: ApprovalResponse = {
        approved: true,
        approvedBy,
        approvedAt: new Date(),
        notes,
        conditions,
      };

      pendingApproval.responses.push(response);

      // Check if we have enough approvals
      const approvedCount = pendingApproval.responses.filter(r => r.approved).length;
      const requiredApprovals = pendingApproval.policy.minApprovers || 1;

      if (approvedCount >= requiredApprovals) {
        // Mark as approved
        pendingApproval.status = 'approved';
        await this.phaseStateManager.approvePhase(phase, approvedBy, notes);
        
        // Clean up
        this.pendingApprovals.delete(approvalId);
        await this.removePendingApproval(approvalId);

        this.emit('approval:completed', { phase, approvedBy, notes });
      } else {
        // Save partial approval
        await this.savePendingApproval(approvalId, pendingApproval);
        this.emit('approval:partial', { 
          phase, 
          approvedBy, 
          current: approvedCount, 
          required: requiredApprovals 
        });
      }
    } else {
      // Direct approval (no pending request)
      await this.phaseStateManager.approvePhase(phase, approvedBy, notes);
      this.emit('approval:completed', { phase, approvedBy, notes });
    }
  }

  /**
   * Reject a phase approval
   */
  async reject(
    phase: PhaseType,
    rejectedBy: string,
    reason: string
  ): Promise<void> {
    const state = await this.phaseStateManager.getCurrentState();
    if (!state) {
      throw new Error('No project state found');
    }

    const approvalId = this.generateApprovalId(phase, state.projectId);
    const pendingApproval = this.pendingApprovals.get(approvalId);

    if (pendingApproval) {
      pendingApproval.status = 'rejected';
      const response: ApprovalResponse = {
        approved: false,
        approvedBy: rejectedBy,
        approvedAt: new Date(),
        notes: reason,
      };
      pendingApproval.responses.push(response);

      // Clean up
      this.pendingApprovals.delete(approvalId);
      await this.removePendingApproval(approvalId);

      this.emit('approval:rejected', { phase, rejectedBy, reason });
    } else {
      throw new Error(`No pending approval found for phase ${phase}`);
    }
  }

  /**
   * Get pending approvals
   */
  async getPendingApprovals(): Promise<PendingApproval[]> {
    await this.loadPendingApprovals();
    return Array.from(this.pendingApprovals.values())
      .filter(a => a.status === 'pending');
  }

  /**
   * Get approval history for a phase
   */
  async getApprovalHistory(phase: PhaseType): Promise<PendingApproval[]> {
    const historyDir = path.join(this.approvalsDir, 'history');
    const history: PendingApproval[] = [];

    try {
      const files = await fs.promises.readdir(historyDir);
      for (const file of files) {
        if (file.includes(phase)) {
          const content = await fs.promises.readFile(
            path.join(historyDir, file),
            'utf-8'
          );
          history.push(JSON.parse(content));
        }
      }
    } catch (error) {
      // History directory might not exist
    }

    return history;
  }

  /**
   * Check auto-approval conditions
   */
  private async checkAutoApproval(
    request: ApprovalRequest,
    policy: ApprovalPolicy
  ): Promise<boolean> {
    if (!policy.autoApproveConditions || policy.autoApproveConditions.length === 0) {
      return false;
    }

    for (const condition of policy.autoApproveConditions) {
      const met = await this.evaluateCondition(condition, request.artifacts);
      if (!met) {
        return false;
      }
    }

    return true;
  }

  /**
   * Evaluate a single approval condition
   */
  private async evaluateCondition(
    condition: ApprovalCondition,
    artifacts: string[]
  ): Promise<boolean> {
    switch (condition.type) {
      case 'test-coverage':
        return await this.checkTestCoverage(artifacts, condition.threshold || 80);
      
      case 'code-review':
        return await this.checkCodeReview(artifacts);
      
      case 'security-scan':
        return await this.checkSecurityScan(artifacts);
      
      case 'custom':
        return condition.customCheck ? await condition.customCheck(artifacts) : false;
      
      default:
        return false;
    }
  }

  /**
   * Check test coverage (placeholder implementation)
   */
  private async checkTestCoverage(artifacts: string[], threshold: number): Promise<boolean> {
    // This would integrate with actual test coverage tools
    // For now, check if test artifacts exist
    const hasTests = artifacts.some(a => a.includes('test') || a.includes('spec'));
    return hasTests;
  }

  /**
   * Check code review status (placeholder implementation)
   */
  private async checkCodeReview(artifacts: string[]): Promise<boolean> {
    // This would integrate with code review systems (GitHub PRs, etc.)
    // For now, return false to require manual approval
    return false;
  }

  /**
   * Check security scan results (placeholder implementation)
   */
  private async checkSecurityScan(artifacts: string[]): Promise<boolean> {
    // This would integrate with security scanning tools
    // For now, check if security artifacts exist
    const hasSecurityCheck = artifacts.some(a => 
      a.includes('security') || a.includes('scan') || a.includes('audit')
    );
    return hasSecurityCheck;
  }

  /**
   * Auto-approve a phase
   */
  private async autoApprove(phase: PhaseType, approvedBy: string, notes: string): Promise<void> {
    await this.phaseStateManager.approvePhase(phase, approvedBy, notes);
  }

  /**
   * Generate approval ID
   */
  private generateApprovalId(phase: PhaseType, projectId: string): string {
    return `${projectId}-${phase}`;
  }

  /**
   * Save pending approval to disk
   */
  private async savePendingApproval(
    approvalId: string,
    approval: PendingApproval
  ): Promise<void> {
    await fs.promises.mkdir(this.approvalsDir, { recursive: true });
    const filePath = path.join(this.approvalsDir, `${approvalId}.json`);
    
    // Convert dates to strings for JSON serialization
    const serializable = JSON.parse(JSON.stringify(approval));
    
    await fs.promises.writeFile(filePath, JSON.stringify(serializable, null, 2), 'utf-8');
  }

  /**
   * Remove pending approval from disk
   */
  private async removePendingApproval(approvalId: string): Promise<void> {
    const filePath = path.join(this.approvalsDir, `${approvalId}.json`);
    
    // Move to history
    const historyDir = path.join(this.approvalsDir, 'history');
    await fs.promises.mkdir(historyDir, { recursive: true });
    
    const historyPath = path.join(
      historyDir,
      `${approvalId}-${Date.now()}.json`
    );
    
    try {
      const content = await fs.promises.readFile(filePath, 'utf-8');
      await fs.promises.writeFile(historyPath, content, 'utf-8');
      await fs.promises.unlink(filePath);
    } catch (error) {
      // File might not exist
    }
  }

  /**
   * Load pending approvals from disk
   */
  private async loadPendingApprovals(): Promise<void> {
    try {
      const files = await fs.promises.readdir(this.approvalsDir);
      
      for (const file of files) {
        if (file.endsWith('.json') && !file.includes('history')) {
          const filePath = path.join(this.approvalsDir, file);
          const content = await fs.promises.readFile(filePath, 'utf-8');
          const approval = JSON.parse(content);
          
          // Convert date strings back to Date objects
          approval.request.requestedAt = new Date(approval.request.requestedAt);
          approval.createdAt = new Date(approval.createdAt);
          if (approval.expiresAt) {
            approval.expiresAt = new Date(approval.expiresAt);
          }
          
          for (const response of approval.responses) {
            response.approvedAt = new Date(response.approvedAt);
          }
          
          const approvalId = file.replace('.json', '');
          this.pendingApprovals.set(approvalId, approval);
        }
      }
    } catch (error) {
      // Directory might not exist
    }
  }

  /**
   * Check for expired approvals
   */
  async checkExpiredApprovals(): Promise<void> {
    await this.loadPendingApprovals();
    const now = new Date();

    for (const [approvalId, approval] of this.pendingApprovals.entries()) {
      if (approval.expiresAt && approval.expiresAt < now && approval.status === 'pending') {
        approval.status = 'expired';
        await this.removePendingApproval(approvalId);
        this.pendingApprovals.delete(approvalId);
        
        this.emit('approval:expired', { 
          phase: approval.request.phase,
          requestedBy: approval.request.requestedBy,
          expiredAt: now
        });
      }
    }
  }

  /**
   * Get approval status for a phase
   */
  async getApprovalStatus(phase: PhaseType): Promise<{
    required: boolean;
    status: 'not-required' | 'pending' | 'approved' | 'rejected' | 'expired';
    details?: PendingApproval;
  }> {
    const state = await this.phaseStateManager.getCurrentState();
    if (!state) {
      return { required: false, status: 'not-required' };
    }

    if (!state.approvalsRequired) {
      return { required: false, status: 'not-required' };
    }

    const phaseStatus = state.phaseStatus[phase];
    if (phaseStatus.approved) {
      return { required: true, status: 'approved' };
    }

    const approvalId = this.generateApprovalId(phase, state.projectId);
    const pendingApproval = this.pendingApprovals.get(approvalId);

    if (!pendingApproval) {
      await this.loadPendingApprovals();
      const loaded = this.pendingApprovals.get(approvalId);
      if (loaded) {
        return { 
          required: true, 
          status: loaded.status as any,
          details: loaded 
        };
      }
    }

    if (pendingApproval) {
      return { 
        required: true, 
        status: pendingApproval.status as any,
        details: pendingApproval 
      };
    }

    return { required: true, status: 'pending' };
  }
}