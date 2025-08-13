/**
 * Base Agent class for all ae-framework agents
 * Provides common functionality for phase state management and steering documents
 */

import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { SteeringLoader } from '../utils/steering-loader.js';

export abstract class BaseAgent {
  protected phaseStateManager: PhaseStateManager;
  protected steeringLoader: SteeringLoader;
  protected phaseName: PhaseType;

  constructor(phaseName: PhaseType) {
    this.phaseName = phaseName;
    this.phaseStateManager = new PhaseStateManager();
    this.steeringLoader = new SteeringLoader();
  }

  /**
   * Initialize phase if not already started
   */
  protected async initializePhase(): Promise<void> {
    const state = await this.phaseStateManager.getCurrentState();
    
    if (!state) {
      // Initialize new project if no state exists
      await this.phaseStateManager.initializeProject();
      await this.phaseStateManager.startPhase(this.phaseName);
    } else if (!state.phaseStatus[this.phaseName].startedAt) {
      // Start phase if not already started
      await this.phaseStateManager.startPhase(this.phaseName);
    }
  }

  /**
   * Check if can proceed with current phase
   */
  protected async canProceed(): Promise<{
    canProceed: boolean;
    reason?: string;
  }> {
    const state = await this.phaseStateManager.getCurrentState();
    
    if (!state) {
      return {
        canProceed: false,
        reason: 'No project state found. Initialize project first.',
      };
    }

    // Check if we're at the right phase
    if (state.currentPhase !== this.phaseName) {
      // Check if we can skip to this phase (all previous phases completed)
      const phases: PhaseType[] = ['intent', 'formal', 'test', 'code', 'verify', 'operate'];
      const currentIndex = phases.indexOf(state.currentPhase);
      const targetIndex = phases.indexOf(this.phaseName);

      if (targetIndex < currentIndex) {
        return {
          canProceed: false,
          reason: `Phase ${this.phaseName} has already been completed.`,
        };
      }

      // Check if all previous phases are completed and approved
      for (let i = currentIndex; i < targetIndex; i++) {
        const phase = phases[i];
        const phaseStatus = state.phaseStatus[phase];
        
        if (!phaseStatus.completed) {
          return {
            canProceed: false,
            reason: `Previous phase ${phase} must be completed first.`,
          };
        }

        if (state.approvalsRequired && !phaseStatus.approved) {
          return {
            canProceed: false,
            reason: `Previous phase ${phase} must be approved first.`,
          };
        }
      }
    }

    // Check if current phase is already completed
    if (state.phaseStatus[this.phaseName].completed) {
      return {
        canProceed: false,
        reason: `Phase ${this.phaseName} is already completed.`,
      };
    }

    return { canProceed: true };
  }

  /**
   * Complete current phase with artifacts
   */
  protected async completePhase(artifacts: string[]): Promise<void> {
    await this.phaseStateManager.completePhase(this.phaseName, artifacts);
  }

  /**
   * Get steering context for the agent
   */
  protected async getSteeringContext(): Promise<string> {
    return await this.steeringLoader.getSteeringContext();
  }

  /**
   * Get steering documents
   */
  protected async getSteeringDocuments(): Promise<Record<string, string>> {
    return await this.steeringLoader.loadAllDocuments();
  }

  /**
   * Log phase activity
   */
  protected async logActivity(activity: string, metadata?: any): Promise<void> {
    const key = `${this.phaseName}_activity_${Date.now()}`;
    const value = {
      activity,
      timestamp: new Date().toISOString(),
      ...metadata,
    };
    
    await this.phaseStateManager.addMetadata(key, value);
  }

  /**
   * Get artifacts from previous phase
   */
  protected async getPreviousPhaseArtifacts(): Promise<string[]> {
    const phases: PhaseType[] = ['intent', 'formal', 'test', 'code', 'verify', 'operate'];
    const currentIndex = phases.indexOf(this.phaseName);
    
    if (currentIndex === 0) {
      return []; // No previous phase for intent
    }

    const previousPhase = phases[currentIndex - 1];
    return await this.phaseStateManager.getPhaseArtifacts(previousPhase);
  }

  /**
   * Check if approvals are required
   */
  protected async requiresApproval(): Promise<boolean> {
    const state = await this.phaseStateManager.getCurrentState();
    return state?.approvalsRequired || false;
  }

  /**
   * Generate phase report
   */
  protected async generatePhaseReport(): Promise<string> {
    const state = await this.phaseStateManager.getCurrentState();
    if (!state) {
      return 'No project state found.';
    }

    const phaseStatus = state.phaseStatus[this.phaseName];
    
    let report = `# ${this.phaseName.toUpperCase()} Phase Report\n\n`;
    report += `**Status**: ${phaseStatus.completed ? 'Completed' : phaseStatus.startedAt ? 'In Progress' : 'Not Started'}\n`;
    
    if (phaseStatus.startedAt) {
      report += `**Started**: ${phaseStatus.startedAt.toISOString()}\n`;
    }
    
    if (phaseStatus.completedAt) {
      report += `**Completed**: ${phaseStatus.completedAt.toISOString()}\n`;
    }
    
    if (phaseStatus.approved) {
      report += `**Approved**: Yes (by ${phaseStatus.approvedBy} at ${phaseStatus.approvedAt?.toISOString()})\n`;
    } else if (phaseStatus.completed && state.approvalsRequired) {
      report += `**Approved**: Pending approval\n`;
    }
    
    if (phaseStatus.artifacts.length > 0) {
      report += `\n## Artifacts\n`;
      for (const artifact of phaseStatus.artifacts) {
        report += `- ${artifact}\n`;
      }
    }
    
    if (phaseStatus.notes) {
      report += `\n## Notes\n${phaseStatus.notes}\n`;
    }
    
    return report;
  }
}