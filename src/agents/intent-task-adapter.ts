/**
 * Intent Task Adapter for Claude Code
 * 
 * This adapter integrates Intent Agent with Claude Code's Task tool,
 * enabling seamless Phase 1 Intent workflow integration and proactive assistance.
 */

import { IntentAgent, IntentAnalysisRequest, RequirementSource, ProjectContext, Requirement } from './intent-agent.js';

export interface TaskRequest {
  description: string;
  prompt: string;
  subagent_type: string;
}

export interface TaskResponse {
  summary: string;
  analysis: string;
  recommendations: string[];
  nextActions: string[];
  warnings: string[];
  shouldBlockProgress: boolean;
}

export class IntentTaskAdapter {
  private agent: IntentAgent;

  constructor() {
    this.agent = new IntentAgent();
  }

  /**
   * Main handler for Intent-related tasks from Claude Code
   */
  async handleIntentTask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    
    switch (taskType) {
      case 'analyze-requirements':
        return this.handleRequirementsAnalysis(request);
      
      case 'extract-natural-language':
        return this.handleNaturalLanguageExtraction(request);
      
      case 'create-user-stories':
        return this.handleUserStoryCreation(request);
      
      case 'validate-completeness':
        return this.handleCompletenessValidation(request);
      
      case 'domain-modeling':
        return this.handleDomainModeling(request);
      
      default:
        return this.handleGenericIntentGuidance(request);
    }
  }

  /**
   * Proactive Intent suggestions for Claude Code's autonomous operation
   */
  async provideProactiveGuidance(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    shouldIntervene: boolean;
    intervention: {
      type: 'warning' | 'suggestion' | 'block';
      message: string;
      recommendedActions: string[];
    };
  }> {
    // Analyze context to determine if Intent intervention is needed
    const analysis = await this.analyzeRecentActivity(context);
    
    if (analysis.hasIntentGaps) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'warning',
          message: 'Requirements analysis gaps detected in recent development',
          recommendedActions: analysis.correctionActions,
        },
      };
    }

    if (analysis.missedIntentOpportunity) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'suggestion',
          message: 'Consider analyzing requirements more thoroughly for better project foundation',
          recommendedActions: analysis.intentSuggestions,
        },
      };
    }

    return {
      shouldIntervene: false,
      intervention: {
        type: 'suggestion',
        message: 'Requirements analysis looks comprehensive',
        recommendedActions: [],
      },
    };
  }

  private async handleRequirementsAnalysis(request: TaskRequest): Promise<TaskResponse> {
    const sources = this.extractRequirementSources(request.prompt);
    const context = this.extractProjectContext(request.prompt);
    
    const analysisRequest: IntentAnalysisRequest = {
      sources,
      context,
      analysisDepth: 'comprehensive',
      outputFormat: 'both'
    };

    try {
      const result = await this.agent.analyzeIntent(analysisRequest);
      
      return {
        summary: `Intent Analysis Complete - ${result.requirements.length} requirements identified`,
        analysis: this.formatIntentAnalysis(result),
        recommendations: this.generateIntentRecommendations(result),
        nextActions: [
          'Review identified requirements for completeness',
          'Validate stakeholder concerns coverage',
          'Proceed to Phase 2 (Formal Specification)',
          'Create domain model from requirements'
        ],
        warnings: this.identifyIntentWarnings(result),
        shouldBlockProgress: result.requirements.length < 5, // Simple completeness check
      };
    } catch (error) {
      return {
        summary: 'Intent analysis failed',
        analysis: `Error during intent analysis: ${error}`,
        recommendations: ['Check requirement sources format', 'Verify project context'],
        nextActions: ['Fix requirement sources and retry analysis'],
        warnings: ['Intent analysis must complete before proceeding to next phase'],
        shouldBlockProgress: true,
      };
    }
  }

  private async handleNaturalLanguageExtraction(request: TaskRequest): Promise<TaskResponse> {
    const text = this.extractTextContent(request.prompt);
    
    try {
      const requirements = await this.agent.extractFromNaturalLanguage(text);
      
      return {
        summary: `Extracted ${requirements.length} requirements from natural language`,
        analysis: this.formatExtractedRequirements(requirements),
        recommendations: [
          'Review extracted requirements for accuracy',
          'Add missing requirement details',
          'Categorize requirements by type',
        ],
        nextActions: [
          'Validate extracted requirements with stakeholders',
          'Complete requirement analysis',
          'Create formal specifications',
        ],
        warnings: requirements.length === 0 ? ['No clear requirements found in text'] : [],
        shouldBlockProgress: false,
      };
    } catch (error) {
      return {
        summary: 'Natural language extraction failed',
        analysis: `Error extracting requirements: ${error}`,
        recommendations: ['Provide clearer requirement text', 'Check text format'],
        nextActions: ['Revise input text and retry extraction'],
        warnings: ['Natural language extraction should succeed for proper analysis'],
        shouldBlockProgress: false,
      };
    }
  }

  private async handleUserStoryCreation(request: TaskRequest): Promise<TaskResponse> {
    const requirements = this.extractRequirementsList(request.prompt);
    
    try {
      const userStories = await this.agent.createUserStories(requirements);
      
      return {
        summary: `Generated ${userStories.length} user stories from requirements`,
        analysis: this.formatUserStories(userStories),
        recommendations: [
          'Review user stories for completeness',
          'Add acceptance criteria to stories',
          'Prioritize stories by business value',
        ],
        nextActions: [
          'Validate user stories with stakeholders',
          'Create acceptance criteria',
          'Estimate user story complexity',
        ],
        warnings: userStories.length === 0 ? ['No user stories could be generated'] : [],
        shouldBlockProgress: false,
      };
    } catch (error) {
      return {
        summary: 'User story creation failed',
        analysis: `Error creating user stories: ${error}`,
        recommendations: ['Check requirements format', 'Provide more detailed requirements'],
        nextActions: ['Fix requirements format and retry'],
        warnings: ['User stories help bridge requirements and implementation'],
        shouldBlockProgress: false,
      };
    }
  }

  private async handleCompletenessValidation(request: TaskRequest): Promise<TaskResponse> {
    const requirements = this.extractRequirementsList(request.prompt);
    
    try {
      const validation = await this.agent.validateCompleteness(requirements);
      
      return {
        summary: `Completeness Score: ${Math.round(validation.coverage * 100)}%`,
        analysis: this.formatCompletenessValidation(validation),
        recommendations: validation.missing.map(area => `Add ${area} requirements`),
        nextActions: validation.missing.map(gap => `Address gap: ${gap}`),
        warnings: validation.coverage < 0.8 ? ['Low completeness score - requirements may be incomplete'] : [],
        shouldBlockProgress: validation.coverage < 0.6,
      };
    } catch (error) {
      return {
        summary: 'Completeness validation failed',
        analysis: `Error validating completeness: ${error}`,
        recommendations: ['Check requirement sources', 'Ensure proper formatting'],
        nextActions: ['Fix sources and retry validation'],
        warnings: ['Completeness validation ensures comprehensive requirements'],
        shouldBlockProgress: false,
      };
    }
  }

  private async handleDomainModeling(request: TaskRequest): Promise<TaskResponse> {
    const requirements = this.extractRequirementsList(request.prompt);
    const context = this.extractProjectContext(request.prompt);
    
    try {
      const domainModel = await this.agent.buildDomainModelFromRequirements(requirements, context);
      
      return {
        summary: `Domain model created with ${domainModel.entities.length} entities`,
        analysis: this.formatDomainModel(domainModel),
        recommendations: [
          'Review domain entities for completeness',
          'Validate relationships between entities',
          'Consider domain boundaries',
        ],
        nextActions: [
          'Refine domain model based on feedback',
          'Create formal specifications from model',
          'Design system architecture',
        ],
        warnings: domainModel.entities.length === 0 ? ['No domain entities identified'] : [],
        shouldBlockProgress: false,
      };
    } catch (error) {
      return {
        summary: 'Domain modeling failed',
        analysis: `Error creating domain model: ${error}`,
        recommendations: ['Check requirements quality', 'Provide more domain context'],
        nextActions: ['Improve requirements and retry modeling'],
        warnings: ['Domain model helps understand problem space'],
        shouldBlockProgress: false,
      };
    }
  }

  private async handleGenericIntentGuidance(request: TaskRequest): Promise<TaskResponse> {
    return {
      summary: 'Intent Phase Guidance',
      analysis: `
# Intent Analysis Guidance

**Current Request**: ${request.description}

## Intent Phase Overview
Phase 1 focuses on understanding and analyzing requirements to establish clear project intent.

## Available Capabilities
- **Requirements Analysis**: Extract and categorize requirements from multiple sources
- **Natural Language Processing**: Convert informal descriptions to structured requirements
- **User Story Creation**: Transform requirements into actionable user stories
- **Domain Modeling**: Build conceptual models from requirements
- **Completeness Validation**: Ensure requirements coverage

## Recommended Approach
1. Start with requirements analysis using available sources
2. Extract clear requirements from natural language
3. Create user stories for development guidance
4. Build domain model for system understanding
5. Validate completeness before proceeding
      `.trim(),
      recommendations: [
        'Begin with comprehensive requirements analysis',
        'Use natural language extraction for informal sources',
        'Create user stories to guide development',
        'Build domain model for better understanding',
      ],
      nextActions: [
        'Gather all requirement sources',
        'Run intent analysis on sources',
        'Review and validate results',
        'Proceed to Phase 2 (Formal Specification)',
      ],
      warnings: [],
      shouldBlockProgress: false,
    };
  }

  private classifyTask(description: string, prompt: string): string {
    const combined = (description + ' ' + prompt).toLowerCase();
    
    if (combined.includes('analyze') && (combined.includes('requirement') || combined.includes('intent'))) {
      return 'analyze-requirements';
    }
    
    if (combined.includes('extract') && combined.includes('natural')) {
      return 'extract-natural-language';
    }
    
    if (combined.includes('user') && combined.includes('stor')) {
      return 'create-user-stories';
    }
    
    if (combined.includes('complete') || combined.includes('validat')) {
      return 'validate-completeness';
    }
    
    if (combined.includes('domain') && combined.includes('model')) {
      return 'domain-modeling';
    }
    
    return 'generic-guidance';
  }

  private extractRequirementSources(prompt: string): RequirementSource[] {
    // Extract requirement sources from prompt
    // This is a simplified implementation - in practice would use more sophisticated parsing
    return [{
      type: 'text',
      content: prompt,
      metadata: {
        author: 'User',
        date: new Date(),
        priority: 'medium',
        tags: ['extracted'],
      }
    }];
  }

  private extractProjectContext(prompt: string): ProjectContext | undefined {
    // Extract project context from prompt
    // This would be enhanced with better parsing logic
    return {
      domain: 'Software Development',
      existingSystem: false,
      constraints: [],
      stakeholders: [],
      glossary: [],
    };
  }

  private extractTextContent(prompt: string): string {
    // Extract main text content for natural language processing
    return prompt;
  }

  private extractRequirementsList(prompt: string): Requirement[] {
    // Extract requirements list from prompt
    // Simplified implementation - convert text to basic requirements
    return [{
      id: 'req-1',
      type: 'functional' as const,
      category: 'general',
      description: prompt,
      priority: 'should' as const,
      acceptance: [],
      source: 'user-input',
      status: 'draft' as const,
    }];
  }

  private formatIntentAnalysis(result: any): string {
    return `
# Intent Analysis Results

**Requirements Identified**: ${result.requirements.length}
**Functional Requirements**: ${result.requirements.filter((r: any) => r.type === 'functional').length}
**Non-Functional Requirements**: ${result.requirements.filter((r: any) => r.type === 'non-functional').length}

## Completeness Score
${Math.round(result.completeness.score * 100)}% complete

## Domain Understanding
${result.domainModel ? `Domain model created with ${result.domainModel.entities.length} entities` : 'Domain model not available'}
    `.trim();
  }

  private formatExtractedRequirements(requirements: any[]): string {
    return `
# Extracted Requirements

**Total Requirements**: ${requirements.length}

${requirements.map((req, i) => `
## Requirement ${i + 1}
- **Type**: ${req.type}
- **Category**: ${req.category}
- **Description**: ${req.description}
- **Priority**: ${req.priority}
`).join('\n')}
    `.trim();
  }

  private formatUserStories(userStories: any[]): string {
    return `
# Generated User Stories

**Total Stories**: ${userStories.length}

${userStories.map((story, i) => `
## Story ${i + 1}: ${story.title}
**As a** ${story.asA}
**I want** ${story.iWant}
**So that** ${story.soThat}

**Acceptance Criteria**:
${story.acceptanceCriteria.map((criteria: string) => `- ${criteria}`).join('\n')}

**Priority**: ${story.priority}
`).join('\n')}
    `.trim();
  }

  private formatCompletenessValidation(validation: any): string {
    return `
# Completeness Validation Results

**Overall Score**: ${Math.round(validation.coverage * 100)}%
**Complete**: ${validation.complete ? 'Yes' : 'No'}

## Missing Areas
${validation.missing.map((area: string) => `- ${area}`).join('\n')}
    `.trim();
  }

  private formatDomainModel(domainModel: any): string {
    return `
# Domain Model

**Entities**: ${domainModel.entities.length}
**Relationships**: ${domainModel.relationships.length}

## Entities
${domainModel.entities.map((entity: any) => `
### ${entity.name}
- **Type**: ${entity.type}
- **Attributes**: ${entity.attributes.length}
- **Responsibilities**: ${entity.responsibilities.join(', ')}
`).join('\n')}

## Relationships
${domainModel.relationships.map((rel: any) => `- ${rel.from} ${rel.type} ${rel.to}`).join('\n')}
    `.trim();
  }

  private generateIntentRecommendations(result: any): string[] {
    const recommendations = [];
    
    if (result.requirements.length < 5) {
      recommendations.push('Consider gathering more detailed requirements');
    }
    
    if (result.userStories && result.userStories.length === 0) {
      recommendations.push('Create user stories from requirements');
    }
    
    if (result.constraints && result.constraints.length === 0) {
      recommendations.push('Identify and document constraints');
    }
    
    recommendations.push('Validate requirements with stakeholders');
    recommendations.push('Create acceptance criteria for key requirements');
    
    return recommendations;
  }

  private identifyIntentWarnings(result: any): string[] {
    const warnings = [];
    
    if (result.requirements.length < 3) {
      warnings.push('⚠️ Very few requirements identified - consider more detailed analysis');
    }
    
    if (result.ambiguities && result.ambiguities.length > 0) {
      warnings.push(`⚠️ ${result.ambiguities.length} ambiguities found in requirements`);
    }
    
    if (result.risks && result.risks.length > 5) {
      warnings.push(`⚠️ ${result.risks.length} risks identified - consider mitigation strategies`);
    }
    
    return warnings;
  }

  private async analyzeRecentActivity(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    hasIntentGaps: boolean;
    missedIntentOpportunity: boolean;
    correctionActions: string[];
    intentSuggestions: string[];
  }> {
    // Analyze if Intent phase is needed or incomplete
    const hasSpecFiles = context.recentFiles.some(f => f.includes('spec') || f.includes('requirement'));
    const hasIntentAnalysis = context.recentActions.some(a => a.toLowerCase().includes('intent') || a.toLowerCase().includes('requirement'));
    
    const hasIntentGaps = !hasSpecFiles && !hasIntentAnalysis && context.userIntent.toLowerCase().includes('implement');
    const missedIntentOpportunity = !hasIntentAnalysis && context.userIntent.toLowerCase().includes('project');
    
    return {
      hasIntentGaps,
      missedIntentOpportunity,
      correctionActions: hasIntentGaps ? [
        'Start with Phase 1 Intent analysis',
        'Gather and analyze requirements',
        'Create specifications before implementation',
      ] : [],
      intentSuggestions: missedIntentOpportunity ? [
        'Consider starting with requirements analysis',
        'Define project intent and scope clearly',
        'Establish stakeholder requirements',
      ] : [],
    };
  }
}

// Export for Claude Code Task tool integration
export const createIntentTaskHandler = () => {
  const adapter = new IntentTaskAdapter();
  
  return {
    handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
      return adapter.handleIntentTask(request);
    },
    
    provideProactiveGuidance: async (context: any): Promise<any> => {
      return adapter.provideProactiveGuidance(context);
    },
  };
};