/**
 * UI/UX Agent Adapter
 * Standardized UI/UX generation phase backed by UIUXTaskAdapter.
 */

import { UIUXTaskAdapter } from '../ui-ux-task-adapter.js';
import type {
  AgentCapabilities,
  AgentError,
  PhaseMetadata,
  PhaseResult,
  ProcessingContext,
  StandardAEAgent,
  UIUXInput,
  UIUXOutput,
  ValidationResult,
} from '../interfaces/standard-interfaces.js';

export class UIUXAgentAdapter implements StandardAEAgent<UIUXInput, UIUXOutput> {
  readonly agentName = 'UIUXAgentAdapter';
  readonly version = '1.1.0';
  readonly supportedPhase = 'ui-ux-generation' as const;

  private uiuxTaskAdapter: UIUXTaskAdapter;

  constructor() {
    this.uiuxTaskAdapter = new UIUXTaskAdapter();
  }

  async process(input: UIUXInput, context?: ProcessingContext): Promise<PhaseResult<UIUXOutput>> {
    const startTime = new Date();

    try {
      const standardOutput = await this.uiuxTaskAdapter.generateUIUXArtifacts(input);
      const endTime = new Date();
      const metadata: PhaseMetadata = {
        phase: 'ui-ux-generation',
        agentName: this.agentName,
        startTime,
        endTime,
        duration: endTime.getTime() - startTime.getTime(),
        version: this.version,
        confidence: Number((standardOutput.qualityScore / 100).toFixed(2)),
      };

      return {
        success: true,
        data: standardOutput.output,
        metadata,
        errors: [],
        warnings: standardOutput.warnings,
        phase: 'ui-ux-generation',
      };
    } catch (error) {
      return this.buildErrorResult(error, startTime, input, context);
    }
  }

  validateInput(input: UIUXInput): ValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];

    if (!input.domainModel) {
      errors.push('Domain model is required for UI/UX generation');
    }
    if (!input.userStories) {
      errors.push('User stories are required for UI/UX generation');
    }
    if (!input.stakeholders || input.stakeholders.length === 0) {
      warnings.push('No stakeholders provided, using default personas');
    }
    if (input.userStories && input.userStories.stories.length === 0) {
      warnings.push('No user stories provided, output may be generic');
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings,
    };
  }

  getCapabilities(): AgentCapabilities {
    return {
      supportedInputTypes: ['DomainModelingOutput', 'UserStoriesOutput', 'Stakeholder[]'],
      outputSchema: 'UIUXOutput',
      requiredContext: ['domainModel', 'userStories'],
      optionalContext: ['stakeholders', 'designPreferences', 'brandGuidelines'],
      maxInputSize: 50000,
      estimatedProcessingTime: 8000,
    };
  }

  private buildErrorResult(
    error: unknown,
    startTime: Date,
    input: UIUXInput,
    context?: ProcessingContext,
  ): PhaseResult<UIUXOutput> {
    const endTime = new Date();
    const agentError: AgentError = {
      code: 'UI_UX_GENERATION_ERROR',
      message: error instanceof Error ? error.message : 'Unknown UI/UX generation error',
      phase: 'ui-ux-generation',
      severity: 'error',
      context: { input, context },
      stack: error instanceof Error && error.stack ? error.stack : '',
    };

    const metadata: PhaseMetadata = {
      phase: 'ui-ux-generation',
      agentName: this.agentName,
      startTime,
      endTime,
      duration: endTime.getTime() - startTime.getTime(),
      version: this.version,
    };

    return {
      success: false,
      data: {} as UIUXOutput,
      metadata,
      errors: [agentError],
      phase: 'ui-ux-generation',
    };
  }
}
