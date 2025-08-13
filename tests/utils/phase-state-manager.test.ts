import { describe, test, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import { PhaseStateManager } from '../../src/utils/phase-state-manager.js';

describe('PhaseStateManager', () => {
  const testDir = path.join(process.cwd(), '.test-phase-state');
  const stateFile = path.join(testDir, '.ae', 'phase-state.json');
  let manager: PhaseStateManager;

  beforeEach(async () => {
    // Create test directory
    await fs.promises.mkdir(path.dirname(stateFile), { recursive: true });
    manager = new PhaseStateManager(testDir);
  });

  afterEach(async () => {
    // Clean up test directory
    await fs.promises.rm(testDir, { recursive: true, force: true });
  });

  describe('initializeProject', () => {
    test('should initialize a new project', async () => {
      const state = await manager.initializeProject('Test Project', true);
      
      expect(state.projectName).toBe('Test Project');
      expect(state.approvalsRequired).toBe(true);
      expect(state.currentPhase).toBe('intent');
      expect(state.projectId).toBeDefined();
      expect(state.phaseStatus.intent.completed).toBe(false);
    });

    test('should create state file', async () => {
      await manager.initializeProject('Test Project');
      
      const fileExists = await fs.promises.access(stateFile)
        .then(() => true)
        .catch(() => false);
      
      expect(fileExists).toBe(true);
    });
  });

  describe('loadState', () => {
    test('should load existing state', async () => {
      const original = await manager.initializeProject('Test Project');
      
      const newManager = new PhaseStateManager(testDir);
      const loaded = await newManager.loadState();
      
      expect(loaded?.projectId).toBe(original.projectId);
      expect(loaded?.projectName).toBe('Test Project');
    });

    test('should return null if no state exists', async () => {
      const state = await manager.loadState();
      expect(state).toBeNull();
    });
  });

  describe('startPhase', () => {
    test('should start a phase', async () => {
      await manager.initializeProject('Test Project');
      await manager.startPhase('intent');
      
      const state = await manager.getCurrentState();
      expect(state?.phaseStatus.intent.startedAt).toBeDefined();
      expect(state?.currentPhase).toBe('intent');
    });

    test('should throw if phase already completed', async () => {
      await manager.initializeProject('Test Project');
      await manager.startPhase('intent');
      await manager.completePhase('intent', ['artifact.md']);
      
      await expect(manager.startPhase('intent')).rejects.toThrow('already completed');
    });
  });

  describe('completePhase', () => {
    test('should complete a phase with artifacts', async () => {
      await manager.initializeProject('Test Project');
      await manager.startPhase('intent');
      
      const artifacts = ['requirements.md', 'user-stories.md'];
      await manager.completePhase('intent', artifacts);
      
      const state = await manager.getCurrentState();
      expect(state?.phaseStatus.intent.completed).toBe(true);
      expect(state?.phaseStatus.intent.completedAt).toBeDefined();
      expect(state?.phaseStatus.intent.artifacts).toEqual(artifacts);
    });

    test('should auto-approve if approvals not required', async () => {
      await manager.initializeProject('Test Project', false);
      await manager.startPhase('intent');
      await manager.completePhase('intent', []);
      
      const state = await manager.getCurrentState();
      expect(state?.phaseStatus.intent.approved).toBe(true);
      expect(state?.phaseStatus.intent.approvedBy).toBe('auto');
    });
  });

  describe('approvePhase', () => {
    test('should approve a completed phase', async () => {
      await manager.initializeProject('Test Project', true);
      await manager.startPhase('intent');
      await manager.completePhase('intent', []);
      await manager.approvePhase('intent', 'John Doe', 'Looks good!');
      
      const state = await manager.getCurrentState();
      expect(state?.phaseStatus.intent.approved).toBe(true);
      expect(state?.phaseStatus.intent.approvedBy).toBe('John Doe');
      expect(state?.phaseStatus.intent.notes).toBe('Looks good!');
    });

    test('should throw if phase not completed', async () => {
      await manager.initializeProject('Test Project');
      await manager.startPhase('intent');
      
      await expect(manager.approvePhase('intent', 'John'))
        .rejects.toThrow('must be completed before approval');
    });
  });

  describe('canTransitionToNextPhase', () => {
    test('should return true if phase completed and approved', async () => {
      await manager.initializeProject('Test Project', true);
      await manager.startPhase('intent');
      await manager.completePhase('intent', []);
      await manager.approvePhase('intent', 'John');
      
      const canTransition = await manager.canTransitionToNextPhase();
      expect(canTransition).toBe(true);
    });

    test('should return false if phase not completed', async () => {
      await manager.initializeProject('Test Project');
      await manager.startPhase('intent');
      
      const canTransition = await manager.canTransitionToNextPhase();
      expect(canTransition).toBe(false);
    });

    test('should return false if approval required but not approved', async () => {
      await manager.initializeProject('Test Project', true);
      await manager.startPhase('intent');
      await manager.completePhase('intent', []);
      
      const canTransition = await manager.canTransitionToNextPhase();
      expect(canTransition).toBe(false);
    });
  });

  describe('transitionToNextPhase', () => {
    test('should transition to next phase', async () => {
      await manager.initializeProject('Test Project', false);
      await manager.startPhase('intent');
      await manager.completePhase('intent', []);
      
      const nextPhase = await manager.transitionToNextPhase();
      expect(nextPhase).toBe('formal');
      
      const state = await manager.getCurrentState();
      expect(state?.currentPhase).toBe('formal');
      expect(state?.phaseStatus.formal.startedAt).toBeDefined();
    });

    test('should return null at final phase', async () => {
      await manager.initializeProject('Test Project', false);
      
      // Start and complete intent phase
      await manager.startPhase('intent');
      await manager.completePhase('intent', []);
      
      // Transition through all phases
      const remainingPhases: any[] = ['formal', 'test', 'code', 'verify', 'operate'];
      for (const phase of remainingPhases.slice(0, -1)) {
        await manager.transitionToNextPhase();
        await manager.completePhase(phase, []);
      }
      
      // Transition to operate (final phase)
      await manager.transitionToNextPhase();
      await manager.completePhase('operate', []);
      
      const state = await manager.getCurrentState();
      expect(state?.currentPhase).toBe('operate');
      expect(state?.phaseStatus.operate.completed).toBe(true);
      
      // Try to transition from final phase - should return null
      const nextPhase = await manager.transitionToNextPhase();
      expect(nextPhase).toBeNull();
    });
  });

  describe('getProgressPercentage', () => {
    test('should calculate progress percentage', async () => {
      await manager.initializeProject('Test Project', false);
      
      expect(await manager.getProgressPercentage()).toBe(0);
      
      await manager.startPhase('intent');
      await manager.completePhase('intent', []);
      expect(await manager.getProgressPercentage()).toBe(17); // 1/6 ≈ 17%
      
      await manager.transitionToNextPhase();
      await manager.completePhase('formal', []);
      expect(await manager.getProgressPercentage()).toBe(33); // 2/6 ≈ 33%
    });
  });

  describe('getPhaseTimeline', () => {
    test('should return phase timeline', async () => {
      await manager.initializeProject('Test Project', false);
      await manager.startPhase('intent');
      
      // Add a small delay to ensure duration > 0
      await new Promise(resolve => setTimeout(resolve, 10));
      
      await manager.completePhase('intent', []);
      
      const timeline = await manager.getPhaseTimeline();
      
      expect(timeline).toHaveLength(6);
      expect(timeline[0].phase).toBe('intent');
      // When auto-approved, status is 'approved' not 'completed'
      expect(timeline[0].status).toBe('approved');
      expect(timeline[0].startedAt).toBeDefined();
      expect(timeline[0].completedAt).toBeDefined();
      expect(timeline[0].duration).toBeGreaterThanOrEqual(0);
      
      expect(timeline[1].phase).toBe('formal');
      expect(timeline[1].status).toBe('pending');
    });
  });

  describe('addMetadata', () => {
    test('should add metadata to state', async () => {
      await manager.initializeProject('Test Project');
      await manager.addMetadata('testKey', 'testValue');
      await manager.addMetadata('count', 42);
      
      const state = await manager.getCurrentState();
      expect(state?.metadata?.testKey).toBe('testValue');
      expect(state?.metadata?.count).toBe(42);
    });
  });

  describe('generateStatusReport', () => {
    test('should generate status report', async () => {
      await manager.initializeProject('Test Project', true);
      await manager.startPhase('intent');
      await manager.completePhase('intent', ['req.md']);
      
      const report = await manager.generateStatusReport();
      
      expect(report).toContain('Project Status Report');
      expect(report).toContain('Test Project');
      expect(report).toContain('intent');
      expect(report).toContain('17%'); // Progress
      expect(report).toContain('Get approval for phase: intent');
    });
  });

  describe('resetPhase', () => {
    test('should reset a phase', async () => {
      await manager.initializeProject('Test Project');
      await manager.startPhase('intent');
      await manager.completePhase('intent', ['artifact.md']);
      
      await manager.resetPhase('intent');
      
      const state = await manager.getCurrentState();
      expect(state?.phaseStatus.intent.completed).toBe(false);
      expect(state?.phaseStatus.intent.startedAt).toBeUndefined();
      expect(state?.phaseStatus.intent.artifacts).toEqual([]);
    });
  });

  describe('hasProject', () => {
    test('should return true if project exists', async () => {
      await manager.initializeProject('Test Project');
      const hasProject = await manager.hasProject();
      expect(hasProject).toBe(true);
    });

    test('should return false if no project', async () => {
      const hasProject = await manager.hasProject();
      expect(hasProject).toBe(false);
    });
  });
});