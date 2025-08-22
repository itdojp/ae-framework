/**
 * Intent Agent Adapter
 * Adapts the existing IntentAgent to the standardized AE Framework interface
 */

import { IntentAgent } from '../intent-agent.js';
import {
  StandardAEAgent,
  ProcessingContext,
  PhaseResult,
  ValidationResult,
  AgentCapabilities,
  IntentInput,
  IntentOutput,
  PhaseMetadata,
  AgentError
} from '../interfaces/standard-interfaces.js';

/**
 * Adapter that wraps IntentAgent to conform to standard interface
 */
export class IntentAgentAdapter implements StandardAEAgent<IntentInput, IntentOutput> {
  private intentAgent: IntentAgent;
  
  readonly agentName = 'IntentAgentAdapter';
  readonly version = '1.0.0';
  readonly supportedPhase = 'intent' as const;

  constructor() {
    this.intentAgent = new IntentAgent();
  }

  /**
   * Standardized processing method
   */
  async process(input: IntentInput, context?: ProcessingContext): Promise<PhaseResult<IntentOutput>> {
    const startTime = new Date();
    
    try {
      // Transform standard input to IntentAgent format
      const intentRequest = {
        sources: input.sources.map(source => ({
          ...source,
          type: source.type === 'specification' ? 'text' : source.type // Map incompatible types
        })),
        context: input.context || {},
        analysisDepth: 'comprehensive' as const,
        includeStakeholders: true,
        includeConstraints: true,
        includeGlossary: true
      };

      // Call the original IntentAgent
      const analysisResult = await this.intentAgent.analyzeIntent(intentRequest);
      
      const endTime = new Date();
      const duration = endTime.getTime() - startTime.getTime();

      // Transform result to standard output format
      const standardOutput: IntentOutput = {
        primaryIntent: (analysisResult as any).primaryIntent || analysisResult.intent || 'Intent analysis completed',
        requirements: (analysisResult.requirements || []).map(req => ({
          ...req,
          acceptance_criteria: req.acceptance_criteria || []  // Add missing property
        })),
        stakeholders: (analysisResult as any).stakeholders || [],
        constraints: analysisResult.constraints || [],
        businessContext: {
          domain: input.context?.domain || 'general',
          businessModel: this.extractBusinessModel(analysisResult),
          keyProcesses: this.extractKeyProcesses(analysisResult),
          success_metrics: this.extractSuccessMetrics(analysisResult),
          assumptions: this.extractAssumptions(analysisResult)
        },
        confidenceScore: this.calculateConfidenceScore(analysisResult)
      };

      const metadata: PhaseMetadata = {
        phase: 'intent',
        agentName: this.agentName,
        startTime,
        endTime,
        duration,
        version: this.version,
        inputHash: this.generateInputHash(input),
        confidence: standardOutput.confidenceScore
      };

      return {
        success: true,
        data: standardOutput,
        metadata,
        errors: [],
        warnings: this.generateWarnings(analysisResult),
        phase: 'intent'
      };

    } catch (error) {
      const endTime = new Date();
      const duration = endTime.getTime() - startTime.getTime();

      const agentError: AgentError = {
        code: 'INTENT_ANALYSIS_ERROR',
        message: error instanceof Error ? error.message : 'Unknown intent analysis error',
        phase: 'intent',
        severity: 'error',
        context: { input, context },
        stack: error instanceof Error ? error.stack : undefined
      };

      const metadata: PhaseMetadata = {
        phase: 'intent',
        agentName: this.agentName,
        startTime,
        endTime,
        duration,
        version: this.version
      };

      return {
        success: false,
        data: {} as IntentOutput,
        metadata,
        errors: [agentError],
        phase: 'intent'
      };
    }
  }

  /**
   * Validate input according to standard interface
   */
  validateInput(input: IntentInput): ValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];

    // Validate required fields
    if (!input.sources || !Array.isArray(input.sources) || input.sources.length === 0) {
      errors.push('Input must contain at least one requirement source');
    }

    // Validate source structure
    input.sources?.forEach((source, index) => {
      if (!source.type || !source.content) {
        errors.push(`Source at index ${index} missing required type or content`);
      }

      if (source.content && source.content.length < 10) {
        warnings.push(`Source at index ${index} has very short content (${source.content.length} characters)`);
      }

      if (source.content && source.content.length > 100000) {
        warnings.push(`Source at index ${index} has very long content (${source.content.length} characters), may affect performance`);
      }
    });

    // Validate context if provided
    if (input.context) {
      if (!input.context.domain) {
        warnings.push('No domain specified in context, using generic analysis');
      }

      if (input.context.stakeholders && input.context.stakeholders.length === 0) {
        warnings.push('Empty stakeholders list provided');
      }
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings
    };
  }

  /**
   * Get agent capabilities
   */
  getCapabilities(): AgentCapabilities {
    return {
      supportedInputTypes: ['text', 'document', 'specification', 'conversation'],
      outputSchema: 'IntentOutput',
      requiredContext: ['sources'],
      optionalContext: ['domain', 'stakeholders', 'constraints', 'glossary'],
      maxInputSize: 100000,
      estimatedProcessingTime: 5000 // 5 seconds
    };
  }

  // Private helper methods
  private extractBusinessModel(analysisResult: any): string {
    // Extract business model from analysis result
    if (analysisResult.businessContext?.businessModel) {
      return analysisResult.businessContext.businessModel;
    }
    
    // Try to infer from requirements
    const requirements = analysisResult.requirements || [];
    const businessKeywords = requirements
      .filter((req: any) => req.description?.toLowerCase().includes('business'))
      .map((req: any) => req.description);
    
    if (businessKeywords.length > 0) {
      return 'Inferred from requirements analysis';
    }

    return 'Generic business model';
  }

  private extractKeyProcesses(analysisResult: any): string[] {
    const processes: string[] = [];
    
    // Extract from requirements that mention processes
    const requirements = analysisResult.requirements || [];
    requirements.forEach((req: any) => {
      const desc = req.description?.toLowerCase() || '';
      if (desc.includes('process') || desc.includes('workflow') || desc.includes('procedure')) {
        processes.push(req.description);
      }
    });

    return processes.length > 0 ? processes : ['Primary business process'];
  }

  private extractSuccessMetrics(analysisResult: any): string[] {
    const metrics: string[] = [];
    
    // Extract from requirements that mention metrics, performance, or success
    const requirements = analysisResult.requirements || [];
    requirements.forEach((req: any) => {
      const desc = req.description?.toLowerCase() || '';
      if (desc.includes('metric') || desc.includes('measure') || desc.includes('performance') || desc.includes('success')) {
        metrics.push(req.description);
      }
    });

    return metrics.length > 0 ? metrics : ['System adoption', 'User satisfaction'];
  }

  private extractAssumptions(analysisResult: any): string[] {
    const assumptions: string[] = [];
    
    // Extract assumptions from context or infer from requirements
    if (analysisResult.assumptions) {
      return analysisResult.assumptions;
    }

    // Infer common assumptions
    assumptions.push('Users have basic technical literacy');
    assumptions.push('System will be available 24/7');
    assumptions.push('Requirements are complete and accurate');

    return assumptions;
  }

  private calculateConfidenceScore(analysisResult: any): number {
    let confidence = 0.5; // Base confidence
    
    // Increase confidence based on available data
    if (analysisResult.requirements && analysisResult.requirements.length > 0) {
      confidence += 0.2;
    }
    
    if (analysisResult.stakeholders && analysisResult.stakeholders.length > 0) {
      confidence += 0.1;
    }
    
    if (analysisResult.constraints && analysisResult.constraints.length > 0) {
      confidence += 0.1;
    }
    
    if (analysisResult.primaryIntent && analysisResult.primaryIntent.length > 50) {
      confidence += 0.1;
    }

    return Math.min(confidence, 1.0);
  }

  private generateWarnings(analysisResult: any): string[] {
    const warnings: string[] = [];
    
    if (!analysisResult.requirements || analysisResult.requirements.length === 0) {
      warnings.push('No requirements extracted from input sources');
    }
    
    if (!analysisResult.stakeholders || analysisResult.stakeholders.length === 0) {
      warnings.push('No stakeholders identified in analysis');
    }
    
    if (!analysisResult.constraints || analysisResult.constraints.length === 0) {
      warnings.push('No constraints identified in analysis');
    }

    return warnings;
  }

  private generateInputHash(input: IntentInput): string {
    // Simple hash generation for tracking input changes
    const inputString = JSON.stringify({
      sourcesCount: input.sources.length,
      sourcesContent: input.sources.map(s => s.content.substring(0, 100)).join(''),
      domain: input.context?.domain
    });
    
    // Simple hash function
    let hash = 0;
    for (let i = 0; i < inputString.length; i++) {
      const char = inputString.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    
    return hash.toString(16);
  }
}