/**
 * Task Agent Adapters
 * Adapts existing task adapters to standardized AE Framework interface
 */

import { NaturalLanguageTaskAdapter } from '../natural-language-task-adapter.js';
import { UserStoriesTaskAdapter } from '../user-stories-task-adapter.js';
import { ValidationTaskAdapter } from '../validation-task-adapter.js';
import { DomainModelingTaskAdapter } from '../domain-modeling-task-adapter.js';

import {
  StandardAEAgent,
  ProcessingContext,
  PhaseResult,
  ValidationResult,
  AgentCapabilities,
  PhaseMetadata,
  AgentError,
  RequirementsInput,
  RequirementsOutput,
  UserStoriesInput,
  UserStoriesOutput,
  ValidationInput,
  ValidationOutput,
  DomainModelingInput,
  DomainModelingOutput
} from '../interfaces/standard-interfaces.js';

/**
 * Natural Language Requirements Adapter
 */
export class RequirementsAgentAdapter implements StandardAEAgent<RequirementsInput, RequirementsOutput> {
  private nlpAgent: NaturalLanguageTaskAdapter;
  
  readonly agentName = 'RequirementsAgentAdapter';
  readonly version = '1.0.0';
  readonly supportedPhase = 'requirements' as const;

  constructor() {
    this.nlpAgent = new NaturalLanguageTaskAdapter();
  }

  async process(input: RequirementsInput, context?: ProcessingContext): Promise<PhaseResult<RequirementsOutput>> {
    const startTime = new Date();
    
    try {
      // Transform input for NLP adapter
      const nlpInput = this.buildNaturalLanguageInput(input);
      
      // Process requirements
      const result = await this.nlpAgent.processNaturalLanguageRequirements(nlpInput);
      
      const endTime = new Date();
      const duration = endTime.getTime() - startTime.getTime();

      // Transform to standard output
      const standardOutput: RequirementsOutput = {
        structured: this.extractStructuredRequirements(result, input.intentAnalysis.requirements),
        summary: result.summary || 'Requirements processed successfully',
        gaps: result.gaps || [],
        processedRequirements: result.summary || 'Requirements processed', // Map to string
        naturalLanguageRequirements: nlpInput // Use input text
      };

      const metadata: PhaseMetadata = {
        phase: 'requirements',
        agentName: this.agentName,
        startTime,
        endTime,
        duration,
        version: this.version,
        confidence: this.calculateConfidence(standardOutput)
      };

      return {
        success: true,
        data: standardOutput,
        metadata,
        errors: [],
        warnings: this.generateWarnings(standardOutput),
        phase: 'requirements'
      };

    } catch (error) {
      return this.buildErrorResult(error, startTime, input, context);
    }
  }

  validateInput(input: RequirementsInput): ValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];

    if (!input.intentAnalysis) {
      errors.push('Intent analysis result is required');
    } else {
      if (!input.intentAnalysis.requirements || input.intentAnalysis.requirements.length === 0) {
        warnings.push('No requirements found in intent analysis');
      }
    }

    return { valid: errors.length === 0, errors, warnings };
  }

  getCapabilities(): AgentCapabilities {
    return {
      supportedInputTypes: ['IntentOutput', 'string'],
      outputSchema: 'RequirementsOutput',
      requiredContext: ['intentAnalysis'],
      optionalContext: ['additionalRequirements'],
      estimatedProcessingTime: 3000
    };
  }

  private buildNaturalLanguageInput(input: RequirementsInput): string {
    let nlInput = input.intentAnalysis.primaryIntent + '\n\n';
    
    // Add requirements
    nlInput += 'Requirements:\n';
    input.intentAnalysis.requirements.forEach(req => {
      nlInput += `- ${req.priority.toUpperCase()}: ${req.description}\n`;
    });

    // Add additional requirements if provided
    if (input.additionalRequirements) {
      nlInput += '\nAdditional Requirements:\n' + input.additionalRequirements;
    }

    // Add constraints
    if (input.intentAnalysis.constraints.length > 0) {
      nlInput += '\nConstraints:\n';
      input.intentAnalysis.constraints.forEach(constraint => {
        nlInput += `- ${constraint.type}: ${constraint.description}\n`;
      });
    }

    return nlInput;
  }

  private extractStructuredRequirements(result: any, originalReqs: any[]): any[] {
    // Convert original requirements to structured format
    return originalReqs.map((req, index) => ({
      ...req,
      category: this.categorizeRequirement(req.description),
      dependencies: [],
      risks: []
    }));
  }

  private categorizeRequirement(description: string): string {
    const lower = description.toLowerCase();
    if (lower.includes('user') || lower.includes('interface')) return 'user-interface';
    if (lower.includes('security') || lower.includes('auth')) return 'security';
    if (lower.includes('performance') || lower.includes('speed')) return 'performance';
    if (lower.includes('data') || lower.includes('storage')) return 'data';
    return 'functional';
  }

  private calculateConfidence(output: RequirementsOutput): number {
    let confidence = 0.7; // Base confidence
    
    if (output.structured.length > 3) confidence += 0.1;
    if (output.gaps.length === 0) confidence += 0.1;
    if (output.summary.length > 100) confidence += 0.1;
    
    return Math.min(confidence, 1.0);
  }

  private generateWarnings(output: RequirementsOutput): string[] {
    const warnings: string[] = [];
    
    if (output.gaps.length > 0) {
      warnings.push(`${output.gaps.length} requirement gaps identified`);
    }
    
    if (output.structured.length < 3) {
      warnings.push('Very few structured requirements extracted');
    }

    return warnings;
  }

  private buildErrorResult(error: unknown, startTime: Date, input: any, context: any): PhaseResult<RequirementsOutput> {
    const endTime = new Date();
    const agentError: AgentError = {
      code: 'REQUIREMENTS_PROCESSING_ERROR',
      message: error instanceof Error ? error.message : 'Unknown requirements processing error',
      phase: 'requirements',
      severity: 'error',
      context: { input, context }
    };

    return {
      success: false,
      data: {} as RequirementsOutput,
      metadata: {
        phase: 'requirements',
        agentName: this.agentName,
        startTime,
        endTime,
        duration: endTime.getTime() - startTime.getTime(),
        version: this.version
      },
      errors: [agentError],
      phase: 'requirements'
    };
  }
}

/**
 * User Stories Agent Adapter
 */
export class UserStoriesAgentAdapter implements StandardAEAgent<UserStoriesInput, UserStoriesOutput> {
  private storiesAgent: UserStoriesTaskAdapter;
  
  readonly agentName = 'UserStoriesAgentAdapter';
  readonly version = '1.0.0';
  readonly supportedPhase = 'user-stories' as const;

  constructor() {
    this.storiesAgent = new UserStoriesTaskAdapter();
  }

  async process(input: UserStoriesInput, context?: ProcessingContext): Promise<PhaseResult<UserStoriesOutput>> {
    const startTime = new Date();
    
    try {
      const storiesInput = this.buildStoriesInput(input);
      const result = await this.storiesAgent.generateUserStories(storiesInput);
      
      const endTime = new Date();
      const standardOutput: UserStoriesOutput = {
        stories: this.transformStories(result.stories || []),
        acceptanceCriteria: this.extractAcceptanceCriteria(result.stories || []),
        traceabilityMatrix: this.buildTraceabilityMatrix(result.stories || [], input.requirements.structured),
        success: (result.stories && result.stories.length > 0) // Determine success from stories
      };

      return {
        success: standardOutput.success,
        data: standardOutput,
        metadata: {
          phase: 'user-stories',
          agentName: this.agentName,
          startTime,
          endTime,
          duration: endTime.getTime() - startTime.getTime(),
          version: this.version
        },
        errors: [],
        phase: 'user-stories'
      };

    } catch (error) {
      return this.buildErrorResult(error, startTime);
    }
  }

  validateInput(input: UserStoriesInput): ValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];

    if (!input.requirements) {
      errors.push('Requirements data is required');
    }

    if (!input.stakeholders || input.stakeholders.length === 0) {
      warnings.push('No stakeholders provided, using default personas');
    }

    return { valid: errors.length === 0, errors, warnings };
  }

  getCapabilities(): AgentCapabilities {
    return {
      supportedInputTypes: ['RequirementsOutput'],
      outputSchema: 'UserStoriesOutput',
      requiredContext: ['requirements'],
      optionalContext: ['stakeholders'],
      estimatedProcessingTime: 4000
    };
  }

  private buildStoriesInput(input: UserStoriesInput): string {
    let storiesInput = 'Requirements for User Story Generation:\n\n';
    
    // Add structured requirements
    input.requirements.structured.forEach(req => {
      storiesInput += `- ${req.description} (Priority: ${req.priority})\n`;
    });

    // Add stakeholder context
    if (input.stakeholders && input.stakeholders.length > 0) {
      storiesInput += '\nStakeholders:\n';
      input.stakeholders.forEach(stakeholder => {
        storiesInput += `- ${stakeholder.name} (${stakeholder.role}): ${stakeholder.concerns.join(', ')}\n`;
      });
    }

    return storiesInput;
  }

  private transformStories(stories: any[]): any[] {
    return stories.map((story, index) => ({
      id: story.id || `US-${String(index + 1).padStart(3, '0')}`,
      title: story.title || story.name || `User Story ${index + 1}`,
      description: story.description || story.story || '',
      asA: story.asA || story.persona || 'user',
      iWant: story.iWant || story.goal || story.description,
      soThat: story.soThat || story.benefit || 'I can achieve my goals',
      acceptanceCriteria: story.acceptanceCriteria || story.criteria || [],
      priority: story.priority || 'medium',
      storyPoints: story.storyPoints || story.effort,
      tags: story.tags || []
    }));
  }

  private extractAcceptanceCriteria(stories: any[]): any[] {
    return stories.map(story => ({
      storyId: story.id,
      criteria: story.acceptanceCriteria || [],
      testScenarios: this.generateTestScenarios(story.acceptanceCriteria || [])
    }));
  }

  private generateTestScenarios(criteria: string[]): any[] {
    return criteria.map((criterion, index) => ({
      given: `Given the user is in the system`,
      when: `When the user performs the action described in criterion ${index + 1}`,
      then: `Then ${criterion.toLowerCase()}`
    }));
  }

  private buildTraceabilityMatrix(stories: any[], requirements: any[]): any {
    const matrix: Record<string, string[]> = {};
    let coveredReqs = 0;

    requirements.forEach(req => {
      const relatedStories = stories
        .filter(story => 
          story.description?.toLowerCase().includes(req.description.toLowerCase().split(' ')[0]) ||
          story.iWant?.toLowerCase().includes(req.description.toLowerCase().split(' ')[0])
        )
        .map(story => story.id);
      
      matrix[req.id] = relatedStories;
      if (relatedStories.length > 0) coveredReqs++;
    });

    return {
      requirements: matrix,
      coverage: requirements.length > 0 ? coveredReqs / requirements.length : 0,
      gaps: requirements.filter(req => matrix[req.id]?.length === 0).map(req => req.id)
    };
  }

  private buildErrorResult(error: unknown, startTime: Date): PhaseResult<UserStoriesOutput> {
    return {
      success: false,
      data: {} as UserStoriesOutput,
      metadata: {
        phase: 'user-stories',
        agentName: this.agentName,
        startTime,
        endTime: new Date(),
        duration: new Date().getTime() - startTime.getTime(),
        version: this.version
      },
      errors: [{
        code: 'USER_STORIES_ERROR',
        message: error instanceof Error ? error.message : 'Unknown user stories error',
        phase: 'user-stories',
        severity: 'error'
      }],
      phase: 'user-stories'
    };
  }
}

/**
 * Validation Agent Adapter
 */
export class ValidationAgentAdapter implements StandardAEAgent<ValidationInput, ValidationOutput> {
  private validationAgent: ValidationTaskAdapter;
  
  readonly agentName = 'ValidationAgentAdapter';
  readonly version = '1.0.0';
  readonly supportedPhase = 'validation' as const;

  constructor() {
    this.validationAgent = new ValidationTaskAdapter();
  }

  async process(input: ValidationInput, context?: ProcessingContext): Promise<PhaseResult<ValidationOutput>> {
    const startTime = new Date();
    
    try {
      const result = await this.validationAgent.validateUserStories(input.userStories);
      
      const standardOutput: ValidationOutput = {
        validatedStories: result.validatedStories || input.userStories.stories,
        validationReport: this.buildValidationReport(result, input.userStories.stories),
        conflicts: result.conflicts || [],
        recommendations: result.recommendations || []
      };

      return {
        success: true,
        data: standardOutput,
        metadata: {
          phase: 'validation',
          agentName: this.agentName,
          startTime,
          endTime: new Date(),
          duration: new Date().getTime() - startTime.getTime(),
          version: this.version
        },
        errors: [],
        phase: 'validation'
      };

    } catch (error) {
      return this.buildErrorResult(error, startTime);
    }
  }

  validateInput(input: ValidationInput): ValidationResult {
    const errors: string[] = [];
    if (!input.userStories || !input.userStories.stories) {
      errors.push('User stories are required for validation');
    }
    return { valid: errors.length === 0, errors, warnings: [] };
  }

  getCapabilities(): AgentCapabilities {
    return {
      supportedInputTypes: ['UserStoriesOutput'],
      outputSchema: 'ValidationOutput',
      requiredContext: ['userStories'],
      optionalContext: ['requirements', 'constraints'],
      estimatedProcessingTime: 2000
    };
  }

  private buildValidationReport(result: any, stories: any[]): any {
    return {
      totalStories: stories.length,
      validatedStories: result.validatedStories?.length || stories.length,
      conflicts: result.conflicts?.length || 0,
      coverage: stories.length > 0 ? (result.validatedStories?.length || stories.length) / stories.length : 0,
      quality_score: this.calculateQualityScore(result, stories)
    };
  }

  private calculateQualityScore(result: any, stories: any[]): number {
    let score = 0.8; // Base score
    if (result.conflicts?.length === 0) score += 0.1;
    if (stories.every((s: any) => s.acceptanceCriteria?.length > 0)) score += 0.1;
    return Math.min(score, 1.0);
  }

  private buildErrorResult(error: unknown, startTime: Date): PhaseResult<ValidationOutput> {
    return {
      success: false,
      data: {} as ValidationOutput,
      metadata: {
        phase: 'validation',
        agentName: this.agentName,
        startTime,
        endTime: new Date(),
        duration: new Date().getTime() - startTime.getTime(),
        version: this.version
      },
      errors: [{
        code: 'VALIDATION_ERROR',
        message: error instanceof Error ? error.message : 'Unknown validation error',
        phase: 'validation',
        severity: 'error'
      }],
      phase: 'validation'
    };
  }
}

/**
 * Domain Modeling Agent Adapter
 */
export class DomainModelingAgentAdapter implements StandardAEAgent<DomainModelingInput, DomainModelingOutput> {
  private domainAgent: DomainModelingTaskAdapter;
  
  readonly agentName = 'DomainModelingAgentAdapter';
  readonly version = '1.0.0';
  readonly supportedPhase = 'domain-modeling' as const;

  constructor() {
    this.domainAgent = new DomainModelingTaskAdapter();
  }

  async process(input: DomainModelingInput, context?: ProcessingContext): Promise<PhaseResult<DomainModelingOutput>> {
    const startTime = new Date();
    
    try {
      const domainTask = {
        description: `Create domain model for ${input.businessContext.domain}`,
        prompt: this.buildDomainPrompt(input),
        subagent_type: 'general-purpose', // Required field
        context: {
          previousPhaseResults: input,
          domain: input.businessContext.domain,
          projectScope: input.businessContext.businessModel
        }
      };

      const result = await this.domainAgent.handleDomainModelingTask(domainTask);
      
      const standardOutput: DomainModelingOutput = this.transformDomainResult(result);

      return {
        success: true,
        data: standardOutput,
        metadata: {
          phase: 'domain-modeling',
          agentName: this.agentName,
          startTime,
          endTime: new Date(),
          duration: new Date().getTime() - startTime.getTime(),
          version: this.version
        },
        errors: [],
        phase: 'domain-modeling'
      };

    } catch (error) {
      return this.buildErrorResult(error, startTime);
    }
  }

  validateInput(input: DomainModelingInput): ValidationResult {
    const errors: string[] = [];
    if (!input.validatedUserStories) errors.push('Validated user stories are required');
    if (!input.businessContext) errors.push('Business context is required');
    return { valid: errors.length === 0, errors, warnings: [] };
  }

  getCapabilities(): AgentCapabilities {
    return {
      supportedInputTypes: ['ValidationOutput', 'RequirementsOutput', 'BusinessContext'],
      outputSchema: 'DomainModelingOutput',
      requiredContext: ['validatedUserStories', 'businessContext'],
      optionalContext: ['requirements'],
      estimatedProcessingTime: 6000
    };
  }

  private buildDomainPrompt(input: DomainModelingInput): string {
    let prompt = `Domain: ${input.businessContext.domain}\n\n`;
    
    prompt += 'User Stories:\n';
    input.validatedUserStories.validatedStories.forEach(story => {
      prompt += `- ${story.title}: ${story.description}\n`;
    });

    prompt += '\nBusiness Processes:\n';
    input.businessContext.keyProcesses.forEach(process => {
      prompt += `- ${process}\n`;
    });

    return prompt;
  }

  private transformDomainResult(result: any): DomainModelingOutput {
    return {
      entities: result.entities || [],
      relationships: result.relationships || [],
      valueObjects: result.valueObjects || [],
      aggregates: result.aggregates || [],
      services: result.services || [],
      boundedContexts: result.boundedContexts || []
    };
  }

  private buildErrorResult(error: unknown, startTime: Date): PhaseResult<DomainModelingOutput> {
    return {
      success: false,
      data: {} as DomainModelingOutput,
      metadata: {
        phase: 'domain-modeling',
        agentName: this.agentName,
        startTime,
        endTime: new Date(),
        duration: new Date().getTime() - startTime.getTime(),
        version: this.version
      },
      errors: [{
        code: 'DOMAIN_MODELING_ERROR',
        message: error instanceof Error ? error.message : 'Unknown domain modeling error',
        phase: 'domain-modeling',
        severity: 'error'
      }],
      phase: 'domain-modeling'
    };
  }
}