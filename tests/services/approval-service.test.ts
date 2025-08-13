import { describe, test, expect, beforeEach, afterEach, vi } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import { ApprovalService } from '../../src/services/approval-service.js';
import { PhaseStateManager } from '../../src/utils/phase-state-manager.js';

describe('ApprovalService', () => {
  const testDir = path.join(process.cwd(), '.test-approval-service');
  let service: ApprovalService;
  let phaseStateManager: PhaseStateManager;

  beforeEach(async () => {
    // Create test directory
    await fs.promises.mkdir(testDir, { recursive: true });
    
    // Initialize services with shared phaseStateManager
    phaseStateManager = new PhaseStateManager(testDir);
    service = new ApprovalService(testDir, phaseStateManager);
    
    // Initialize project
    await phaseStateManager.initializeProject('Test Project', true);
  });

  afterEach(async () => {
    // Clean up test directory
    await fs.promises.rm(testDir, { recursive: true, force: true });
  });

  describe('requestApproval', () => {
    test('should request approval for completed phase', async () => {
      // Complete a phase first
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', ['requirements.md']);

      const request = await service.requestApproval('intent', 'John Doe', 'Ready for review');
      
      expect(request.phase).toBe('intent');
      expect(request.requestedBy).toBe('John Doe');
      expect(request.summary).toBe('Ready for review');
      expect(request.artifacts).toEqual(['requirements.md']);
    });

    test('should throw if phase not completed', async () => {
      await phaseStateManager.startPhase('intent');
      
      await expect(service.requestApproval('intent', 'John Doe'))
        .rejects.toThrow('must be completed before requesting approval');
    });

    test('should throw if phase already approved', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await phaseStateManager.approvePhase('intent', 'Admin');
      
      await expect(service.requestApproval('intent', 'John Doe'))
        .rejects.toThrow('already approved');
    });

    test('should emit approval:requested event', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);

      const eventSpy = vi.fn();
      service.on('approval:requested', eventSpy);

      await service.requestApproval('intent', 'John Doe');
      
      expect(eventSpy).toHaveBeenCalled();
      expect(eventSpy.mock.calls[0][0]).toHaveProperty('request');
      expect(eventSpy.mock.calls[0][0]).toHaveProperty('policy');
    });
  });

  describe('approve', () => {
    test('should approve a phase', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      
      await service.approve('intent', 'Manager', 'Looks good!');
      
      const state = await phaseStateManager.getCurrentState();
      expect(state?.phaseStatus.intent.approved).toBe(true);
      expect(state?.phaseStatus.intent.approvedBy).toBe('Manager');
    });

    test('should handle multiple approvers', async () => {
      // Set policy requiring 2 approvers
      service.setPolicy('code', {
        requireMultipleApprovers: true,
        minApprovers: 2,
      });

      // Complete code phase
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await phaseStateManager.approvePhase('intent', 'auto');
      
      await phaseStateManager.transitionToNextPhase(); // to formal
      await phaseStateManager.completePhase('formal', []);
      await phaseStateManager.approvePhase('formal', 'auto');
      
      await phaseStateManager.transitionToNextPhase(); // to test
      await phaseStateManager.completePhase('test', []);
      await phaseStateManager.approvePhase('test', 'auto');
      
      await phaseStateManager.transitionToNextPhase(); // to code
      await phaseStateManager.completePhase('code', ['code.ts']);

      // Request approval
      await service.requestApproval('code', 'Developer');

      // First approval
      const partialSpy = vi.fn();
      service.on('approval:partial', partialSpy);
      
      await service.approve('code', 'Reviewer1', 'LGTM');
      
      expect(partialSpy).toHaveBeenCalled();
      
      // Phase should not be approved yet
      let state = await phaseStateManager.getCurrentState();
      expect(state?.phaseStatus.code.approved).toBe(false);

      // Second approval
      const completeSpy = vi.fn();
      service.on('approval:completed', completeSpy);
      
      await service.approve('code', 'Reviewer2', 'Approved');
      
      expect(completeSpy).toHaveBeenCalled();
      
      // Now phase should be approved
      state = await phaseStateManager.getCurrentState();
      expect(state?.phaseStatus.code.approved).toBe(true);
    });

    test('should emit approval:completed event', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);

      const eventSpy = vi.fn();
      service.on('approval:completed', eventSpy);

      await service.approve('intent', 'Manager');
      
      expect(eventSpy).toHaveBeenCalled();
      expect(eventSpy.mock.calls[0][0]).toHaveProperty('phase', 'intent');
      expect(eventSpy.mock.calls[0][0]).toHaveProperty('approvedBy', 'Manager');
    });
  });

  describe('reject', () => {
    test('should reject approval request', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await service.requestApproval('intent', 'Developer');

      const eventSpy = vi.fn();
      service.on('approval:rejected', eventSpy);

      await service.reject('intent', 'Manager', 'Needs more work');
      
      expect(eventSpy).toHaveBeenCalled();
      expect(eventSpy.mock.calls[0][0]).toHaveProperty('phase', 'intent');
      expect(eventSpy.mock.calls[0][0]).toHaveProperty('reason', 'Needs more work');
    });

    test('should throw if no pending approval', async () => {
      await expect(service.reject('intent', 'Manager', 'Invalid'))
        .rejects.toThrow('No pending approval found');
    });
  });

  describe('auto-approval', () => {
    test('should auto-approve with test coverage condition', async () => {
      // Set auto-approval policy
      service.setPolicy('test', {
        autoApproveConditions: [
          { type: 'test-coverage', threshold: 80 }
        ],
      });

      // Complete test phase with test artifacts
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await phaseStateManager.approvePhase('intent', 'auto');
      
      await phaseStateManager.transitionToNextPhase(); // to formal
      await phaseStateManager.completePhase('formal', []);
      await phaseStateManager.approvePhase('formal', 'auto');
      
      await phaseStateManager.transitionToNextPhase(); // to test
      await phaseStateManager.completePhase('test', ['test-results.xml', 'coverage.json']);

      const autoSpy = vi.fn();
      service.on('approval:auto', autoSpy);

      await service.requestApproval('test', 'CI System');
      
      expect(autoSpy).toHaveBeenCalled();
      
      const state = await phaseStateManager.getCurrentState();
      expect(state?.phaseStatus.test.approved).toBe(true);
      expect(state?.phaseStatus.test.approvedBy).toContain('auto');
    });

    test('should not auto-approve without meeting conditions', async () => {
      service.setPolicy('test', {
        autoApproveConditions: [
          { type: 'test-coverage', threshold: 80 }
        ],
      });

      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await phaseStateManager.approvePhase('intent', 'auto');
      
      await phaseStateManager.transitionToNextPhase();
      await phaseStateManager.completePhase('formal', []);
      await phaseStateManager.approvePhase('formal', 'auto');
      
      await phaseStateManager.transitionToNextPhase();
      // Complete without test artifacts
      await phaseStateManager.completePhase('test', ['readme.md']);

      const autoSpy = vi.fn();
      service.on('approval:auto', autoSpy);

      await service.requestApproval('test', 'Developer');
      
      expect(autoSpy).not.toHaveBeenCalled();
      
      const state = await phaseStateManager.getCurrentState();
      expect(state?.phaseStatus.test.approved).toBe(false);
    });
  });

  describe('getPendingApprovals', () => {
    test('should return pending approvals', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await service.requestApproval('intent', 'Dev1');

      const pending = await service.getPendingApprovals();
      
      expect(pending).toHaveLength(1);
      expect(pending[0].request.phase).toBe('intent');
      expect(pending[0].status).toBe('pending');
    });

    test('should not return completed approvals', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await service.requestApproval('intent', 'Dev1');
      await service.approve('intent', 'Manager');

      const pending = await service.getPendingApprovals();
      
      expect(pending).toHaveLength(0);
    });
  });

  describe('getApprovalStatus', () => {
    test('should return not-required if approvals disabled', async () => {
      await phaseStateManager.initializeProject('Test', false); // No approvals
      
      const status = await service.getApprovalStatus('intent');
      
      expect(status.required).toBe(false);
      expect(status.status).toBe('not-required');
    });

    test('should return approved status', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await phaseStateManager.approvePhase('intent', 'Manager');
      
      const status = await service.getApprovalStatus('intent');
      
      expect(status.required).toBe(true);
      expect(status.status).toBe('approved');
    });

    test('should return pending status', async () => {
      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await service.requestApproval('intent', 'Developer');
      
      const status = await service.getApprovalStatus('intent');
      
      expect(status.required).toBe(true);
      expect(status.status).toBe('pending');
      expect(status.details).toBeDefined();
    });
  });

  describe('checkExpiredApprovals', () => {
    test('should expire old approvals', async () => {
      // Set short timeout
      service.setPolicy('intent', {
        timeoutHours: 0.0001, // Very short for testing (0.36 seconds)
      });

      await phaseStateManager.startPhase('intent');
      await phaseStateManager.completePhase('intent', []);
      await service.requestApproval('intent', 'Developer');

      // Wait for expiration
      await new Promise(resolve => setTimeout(resolve, 500)); // Wait 500ms to ensure expiration

      const expiredSpy = vi.fn();
      service.on('approval:expired', expiredSpy);

      await service.checkExpiredApprovals();
      
      expect(expiredSpy).toHaveBeenCalled();
      
      const pending = await service.getPendingApprovals();
      expect(pending).toHaveLength(0);
    });
  });
});