import * as fs from 'fs';
import * as path from 'path';
import { v4 as uuidv4 } from 'uuid';

/**
 * Phase status for tracking completion and approval
 */
export interface PhaseStatus {
  completed: boolean;
  approved: boolean;
  startedAt?: Date;
  completedAt?: Date;
  approvedAt?: Date;
  approvedBy?: string;
  artifacts: string[];
  notes?: string;
}

/**
 * Project phase state
 */
export interface PhaseState {
  projectId: string;
  projectName?: string;
  createdAt: Date;
  updatedAt: Date;
  currentPhase: PhaseType;
  phaseStatus: {
    intent: PhaseStatus;
    formal: PhaseStatus;
    test: PhaseStatus;
    code: PhaseStatus;
    verify: PhaseStatus;
    operate: PhaseStatus;
  };
  approvalsRequired: boolean;
  metadata?: Record<string, any>;
}

/**
 * Phase types in ae-framework
 */
export type PhaseType = 'intent' | 'formal' | 'test' | 'code' | 'verify' | 'operate';

/**
 * Phase transition rules
 */
const PHASE_TRANSITIONS: Record<PhaseType, PhaseType | null> = {
  intent: 'formal',
  formal: 'test',
  test: 'code',
  code: 'verify',
  verify: 'operate',
  operate: null,
};

/**
 * PhaseStateManager manages the state of project phases
 */
export class PhaseStateManager {
  private stateFilePath: string;
  private state: PhaseState | null = null;

  constructor(projectRoot?: string) {
    const envFile = process.env.AE_PHASE_STATE_FILE;
    if (envFile && envFile.trim().length > 0) {
      this.stateFilePath = path.resolve(envFile);
      return;
    }

    const configuredRoot = projectRoot ?? process.env.AE_PHASE_STATE_ROOT;
    const root = configuredRoot ? path.resolve(configuredRoot) : process.cwd();
    this.stateFilePath = path.join(root, '.ae', 'phase-state.json');
  }

  /**
   * Initialize a new project state
   */
  async initializeProject(projectName?: string, approvalsRequired: boolean = true): Promise<PhaseState> {
    const newState: PhaseState = {
      projectId: uuidv4(),
      ...(projectName !== undefined ? { projectName } : {}),
      createdAt: new Date(),
      updatedAt: new Date(),
      currentPhase: 'intent',
      phaseStatus: {
        intent: this.createEmptyPhaseStatus(),
        formal: this.createEmptyPhaseStatus(),
        test: this.createEmptyPhaseStatus(),
        code: this.createEmptyPhaseStatus(),
        verify: this.createEmptyPhaseStatus(),
        operate: this.createEmptyPhaseStatus(),
      },
      approvalsRequired,
    };

    await this.saveState(newState);
    this.state = newState;
    return newState;
  }

  /**
   * Load existing project state
   */
  async loadState(): Promise<PhaseState | null> {
    try {
      const data = await fs.promises.readFile(this.stateFilePath, 'utf-8');
      const state = JSON.parse(data);
      
      // Convert date strings back to Date objects
      state.createdAt = new Date(state.createdAt);
      state.updatedAt = new Date(state.updatedAt);
      
      for (const phase of Object.values(state.phaseStatus) as PhaseStatus[]) {
        if (phase.startedAt) phase.startedAt = new Date(phase.startedAt);
        if (phase.completedAt) phase.completedAt = new Date(phase.completedAt);
        if (phase.approvedAt) phase.approvedAt = new Date(phase.approvedAt);
      }
      
      this.state = state;
      return state;
    } catch (error) {
      return null;
    }
  }

  /**
   * Save state to file
   */
  private async saveState(state: PhaseState): Promise<void> {
    const dir = path.dirname(this.stateFilePath);
    await fs.promises.mkdir(dir, { recursive: true });
    
    state.updatedAt = new Date();
    await fs.promises.writeFile(
      this.stateFilePath,
      JSON.stringify(state, null, 2),
      'utf-8'
    );
  }

  /**
   * Get current state
   */
  async getCurrentState(): Promise<PhaseState | null> {
    if (!this.state) {
      await this.loadState();
    }
    return this.state;
  }

  /**
   * Start a phase
   */
  async startPhase(phase: PhaseType): Promise<void> {
    const state = await this.getCurrentState();
    if (!state) {
      throw new Error('No project state found. Initialize a project first.');
    }

    const phaseStatus = state.phaseStatus[phase];
    if (phaseStatus.completed) {
      throw new Error(`Phase ${phase} is already completed.`);
    }

    phaseStatus.startedAt = new Date();
    state.currentPhase = phase;
    
    // Save state only once after all modifications
    await this.saveState(state);
  }

  /**
   * Complete a phase
   */
  async completePhase(phase: PhaseType, artifacts: string[]): Promise<void> {
    const state = await this.getCurrentState();
    if (!state) {
      throw new Error('No project state found. Initialize a project first.');
    }

    const phaseStatus = state.phaseStatus[phase];
    
    if (phaseStatus.completed) {
      throw new Error(`Phase ${phase} is already completed.`);
    }

    phaseStatus.completed = true;
    phaseStatus.completedAt = new Date();
    phaseStatus.artifacts = artifacts;

    // If approvals not required, auto-approve
    if (!state.approvalsRequired) {
      phaseStatus.approved = true;
      phaseStatus.approvedAt = new Date();
      phaseStatus.approvedBy = 'auto';
    }

    await this.saveState(state);
  }

  /**
   * Approve a phase
   */
  async approvePhase(phase: PhaseType, approvedBy: string, notes?: string): Promise<void> {
    const state = await this.getCurrentState();
    if (!state) {
      throw new Error('No project state found. Initialize a project first.');
    }

    const phaseStatus = state.phaseStatus[phase];
    
    if (!phaseStatus.completed) {
      throw new Error(`Phase ${phase} must be completed before approval.`);
    }

    if (phaseStatus.approved) {
      throw new Error(`Phase ${phase} is already approved.`);
    }

    phaseStatus.approved = true;
    phaseStatus.approvedAt = new Date();
    phaseStatus.approvedBy = approvedBy;
    if (notes) {
      phaseStatus.notes = notes;
    }

    await this.saveState(state);
  }

  /**
   * Check if can transition to next phase
   */
  async canTransitionToNextPhase(): Promise<boolean> {
    const state = await this.getCurrentState();
    if (!state) return false;

    const currentPhaseStatus = state.phaseStatus[state.currentPhase];
    
    // Must be completed
    if (!currentPhaseStatus.completed) return false;
    
    // If approvals required, must be approved
    if (state.approvalsRequired && !currentPhaseStatus.approved) return false;
    
    // Check if there's a next phase
    const nextPhase = PHASE_TRANSITIONS[state.currentPhase];
    return nextPhase !== null;
  }

  /**
   * Transition to next phase
   */
  async transitionToNextPhase(): Promise<PhaseType | null> {
    const state = await this.getCurrentState();
    if (!state) {
      throw new Error('No project state found.');
    }

    const nextPhase = PHASE_TRANSITIONS[state.currentPhase];
    if (!nextPhase) {
      // Already at final phase - check if it's completed
      const currentPhaseStatus = state.phaseStatus[state.currentPhase];
      if (currentPhaseStatus.completed) {
        return null; // Final phase is completed, no more phases
      }
      throw new Error('Cannot transition: no next phase available.');
    }

    const canTransition = await this.canTransitionToNextPhase();
    if (!canTransition) {
      throw new Error('Cannot transition to next phase. Current phase not completed/approved.');
    }

    state.currentPhase = nextPhase;
    await this.startPhase(nextPhase);
    
    return nextPhase;
  }

  /**
   * Get next phase
   */
  getNextPhase(currentPhase: PhaseType): PhaseType | null {
    return PHASE_TRANSITIONS[currentPhase];
  }

  /**
   * Get phase progress percentage
   */
  async getProgressPercentage(): Promise<number> {
    const state = await this.getCurrentState();
    if (!state) return 0;

    const phases: PhaseType[] = ['intent', 'formal', 'test', 'code', 'verify', 'operate'];
    let completedCount = 0;

    for (const phase of phases) {
      if (state.phaseStatus[phase].completed) {
        completedCount++;
      }
    }

    return Math.round((completedCount / phases.length) * 100);
  }

  /**
   * Get phase timeline
   */
  async getPhaseTimeline(): Promise<Array<{
    phase: PhaseType;
    startedAt?: Date;
    completedAt?: Date;
    duration?: number; // in milliseconds
    status: 'pending' | 'in-progress' | 'completed' | 'approved';
  }>> {
    const state = await this.getCurrentState();
    if (!state) return [];

    const phases: PhaseType[] = ['intent', 'formal', 'test', 'code', 'verify', 'operate'];
    const timeline = [];

    for (const phase of phases) {
      const phaseStatus = state.phaseStatus[phase];
      let status: 'pending' | 'in-progress' | 'completed' | 'approved' = 'pending';
      
      if (phaseStatus.approved) {
        status = 'approved';
      } else if (phaseStatus.completed) {
        status = 'completed';
      } else if (phaseStatus.startedAt) {
        status = 'in-progress';
      }

      const entry: any = {
        phase,
        status,
      };

      if (phaseStatus.startedAt) {
        entry.startedAt = phaseStatus.startedAt;
      }

      if (phaseStatus.completedAt) {
        entry.completedAt = phaseStatus.completedAt;
        
        if (phaseStatus.startedAt) {
          entry.duration = phaseStatus.completedAt.getTime() - phaseStatus.startedAt.getTime();
        }
      }

      timeline.push(entry);
    }

    return timeline;
  }

  /**
   * Add metadata to state
   */
  async addMetadata(key: string, value: any): Promise<void> {
    const state = await this.getCurrentState();
    if (!state) {
      throw new Error('No project state found.');
    }

    if (!state.metadata) {
      state.metadata = {};
    }

    state.metadata[key] = value;
    await this.saveState(state);
  }

  /**
   * Get artifacts for a phase
   */
  async getPhaseArtifacts(phase: PhaseType): Promise<string[]> {
    const state = await this.getCurrentState();
    if (!state) return [];

    return state.phaseStatus[phase].artifacts || [];
  }

  /**
   * Generate status report
   */
  async generateStatusReport(): Promise<string> {
    const state = await this.getCurrentState();
    if (!state) {
      return 'No project state found.';
    }

    const progress = await this.getProgressPercentage();
    const timeline = await this.getPhaseTimeline();

    let report = `# Project Status Report\n\n`;
    report += `**Project ID**: ${state.projectId}\n`;
    if (state.projectName) {
      report += `**Project Name**: ${state.projectName}\n`;
    }
    report += `**Created**: ${state.createdAt.toISOString()}\n`;
    report += `**Last Updated**: ${state.updatedAt.toISOString()}\n`;
    report += `**Current Phase**: ${state.currentPhase}\n`;
    report += `**Overall Progress**: ${progress}%\n`;
    report += `**Approvals Required**: ${state.approvalsRequired ? 'Yes' : 'No'}\n\n`;

    report += `## Phase Status\n\n`;
    report += `| Phase | Status | Started | Completed | Approved | Artifacts |\n`;
    report += `|-------|--------|---------|-----------|----------|----------|\n`;

    for (const item of timeline) {
      const phaseStatus = state.phaseStatus[item.phase];
      const started = item.startedAt ? item.startedAt.toISOString().split('T')[0] : '-';
      const completed = item.completedAt ? item.completedAt.toISOString().split('T')[0] : '-';
      const approved = phaseStatus.approved ? '✅' : (phaseStatus.completed ? '⏳' : '-');
      const artifactCount = phaseStatus.artifacts.length;
      
      report += `| ${item.phase} | ${item.status} | ${started} | ${completed} | ${approved} | ${artifactCount} |\n`;
    }

    report += `\n## Next Steps\n`;
    const nextPhase = this.getNextPhase(state.currentPhase);
    if (nextPhase) {
      const currentStatus = state.phaseStatus[state.currentPhase];
      if (!currentStatus.completed) {
        report += `- Complete current phase: ${state.currentPhase}\n`;
      } else if (state.approvalsRequired && !currentStatus.approved) {
        report += `- Get approval for phase: ${state.currentPhase}\n`;
      } else {
        report += `- Start next phase: ${nextPhase}\n`;
      }
    } else {
      report += `- Project completed! All phases done.\n`;
    }

    return report;
  }

  /**
   * Reset phase (for testing or rollback)
   */
  async resetPhase(phase: PhaseType): Promise<void> {
    const state = await this.getCurrentState();
    if (!state) {
      throw new Error('No project state found.');
    }

    state.phaseStatus[phase] = this.createEmptyPhaseStatus();
    await this.saveState(state);
  }

  /**
   * Create empty phase status
   */
  private createEmptyPhaseStatus(): PhaseStatus {
    return {
      completed: false,
      approved: false,
      artifacts: [],
    };
  }

  /**
   * Check if project exists
   */
  async hasProject(): Promise<boolean> {
    try {
      await fs.promises.access(this.stateFilePath);
      return true;
    } catch {
      return false;
    }
  }
}
