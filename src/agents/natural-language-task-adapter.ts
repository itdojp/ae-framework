/**
 * Natural Language Requirements Task Adapter for Claude Code
 * 
 * This adapter integrates Phase 2 (Natural Language Requirements) processing
 * with Claude Code's Task tool, enabling seamless requirements analysis and
 * natural language processing workflows.
 */

import { FormalAgent, FormalAgentConfig } from './formal-agent.js';
import { TaskRequest, TaskResponse, ProactiveGuidanceContext, ProactiveGuidanceResult } from './task-types.js';

export interface RequirementDocument {
  title: string;
  content: string;
  source: string;
  type: 'functional' | 'non-functional' | 'business' | 'technical';
  priority: 'high' | 'medium' | 'low';
  stakeholder?: string;
}

export interface ProcessedRequirements {
  structured: RequirementDocument[];
  summary: string;
  gaps: string[];
  conflicts: string[];
  ambiguities: string[];
  clarificationNeeded: string[];
}

// Business entity interface for better type safety (addressing review comment)
interface BusinessEntity {
  name: string;
  type: 'core' | 'supporting';
  description: string;
  relationships?: string[];
}

// Completeness validation result interface
interface CompletenessValidationResult {
  score: number;
  missingCategories: string[];
  coverage: {
    functional: number;
    nonFunctional: number;
    businessRules: number;
    userInterface: number;
    data: number;
  };
  missingElements: string[];
  recommendations: string[];
}

export class NaturalLanguageTaskAdapter {
  private agent: FormalAgent;
  
  // Constants for better maintainability (addressing review comment)
  private static readonly MAX_REQUIREMENTS_BEFORE_CONFLICTS = 10;

  constructor() {
    const config: FormalAgentConfig = {
      outputFormat: 'openapi',
      validationLevel: 'comprehensive',
      generateDiagrams: true,
      enableModelChecking: true,
    };

    this.agent = new FormalAgent(config);
  }

  /**
   * Main handler for Natural Language Requirements tasks from Claude Code
   */
  async handleNaturalLanguageTask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    
    switch (taskType) {
      case 'analyze-requirements':
        return this.handleRequirementsAnalysis(request);
      
      case 'extract-entities':
        return this.handleEntityExtraction(request);
      
      case 'validate-completeness':
        return this.handleCompletenessValidation(request);
      
      case 'resolve-ambiguity':
        return this.handleAmbiguityResolution(request);
      
      case 'structure-requirements':
        return this.handleRequirementsStructuring(request);
      
      case 'identify-gaps':
        return this.handleGapIdentification(request);
      
      default:
        return this.handleGenericNLProcessing(request);
    }
  }

  /**
   * Proactive natural language processing guidance for Claude Code
   */
  async provideProactiveGuidance(context: ProactiveGuidanceContext): Promise<ProactiveGuidanceResult> {
    const analysis = await this.analyzeRecentActivity(context);
    
    if (analysis.hasIncompleteRequirements) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'warning',
          message: 'Incomplete requirements detected - consider thorough analysis before proceeding',
          recommendedActions: analysis.completionActions,
        },
      };
    }

    if (analysis.hasAmbiguousRequirements) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'suggestion',
          message: 'Ambiguous requirements found - clarification recommended',
          recommendedActions: analysis.clarificationActions,
        },
      };
    }

    return {
      shouldIntervene: false,
      intervention: {
        type: 'suggestion',
        message: 'Requirements processing looks comprehensive',
        recommendedActions: [],
      },
    };
  }

  private async handleRequirementsAnalysis(request: TaskRequest): Promise<TaskResponse> {
    const requirementsText = this.extractRequirementsText(request.prompt);
    const processed = await this.processNaturalLanguageRequirements(requirementsText);
    
    return {
      summary: `Natural Language Requirements Analysis - ${processed.structured.length} requirements identified`,
      analysis: `
# Requirements Analysis Report

**Total Requirements**: ${processed.structured.length}
**Functional Requirements**: ${processed.structured.filter(r => r.type === 'functional').length}
**Non-Functional Requirements**: ${processed.structured.filter(r => r.type === 'non-functional').length}
**Business Requirements**: ${processed.structured.filter(r => r.type === 'business').length}

## Summary
${processed.summary}

## Identified Gaps
${processed.gaps.map(gap => `• ${gap}`).join('\n')}

## Conflicts Found
${processed.conflicts.map(conflict => `• ${conflict}`).join('\n')}

## Ambiguities
${processed.ambiguities.map(ambiguity => `• ${ambiguity}`).join('\n')}
      `.trim(),
      recommendations: [
        'Review identified gaps for completeness',
        'Clarify ambiguous requirements with stakeholders',
        'Resolve conflicts between requirements',
        'Prioritize requirements by business value',
      ],
      nextActions: [
        'Create structured requirement documents',
        'Generate clarification questions for stakeholders',
        'Proceed to formal specification phase',
      ],
      warnings: processed.gaps.length > 0 ? ['Requirements gaps detected - may affect completeness'] : [],
      shouldBlockProgress: processed.conflicts.length > 3,
    };
  }

  private async handleEntityExtraction(request: TaskRequest): Promise<TaskResponse> {
    const text = this.extractRequirementsText(request.prompt);
    const entities = await this.extractBusinessEntities(text);
    
    return {
      summary: `Entity Extraction Complete - ${entities.length} entities identified`,
      analysis: `
# Business Entity Analysis

**Total Entities**: ${entities.length}

## Core Entities
${entities.filter(e => e.type === 'core').map(e => `• **${e.name}**: ${e.description}`).join('\n')}

## Supporting Entities
${entities.filter(e => e.type === 'supporting').map(e => `• **${e.name}**: ${e.description}`).join('\n')}

## Relationships
${entities.flatMap(e => e.relationships || []).map(r => `• ${r}`).join('\n')}
      `.trim(),
      recommendations: [
        'Review entity relationships for completeness',
        'Validate entity definitions with domain experts',
        'Consider data model implications',
      ],
      nextActions: [
        'Create formal entity specifications',
        'Define entity relationships and constraints',
        'Proceed to data modeling phase',
      ],
      warnings: entities.length < 3 ? ['Few entities identified - may indicate incomplete analysis'] : [],
      shouldBlockProgress: false,
    };
  }

  private async handleCompletenessValidation(request: TaskRequest): Promise<TaskResponse> {
    const text = this.extractRequirementsText(request.prompt);
    const validation = await this.validateRequirementsCompleteness(text);
    
    return {
      summary: `Completeness Validation - ${validation.score}% complete`,
      analysis: `
# Requirements Completeness Report

**Completeness Score**: ${validation.score}%
**Missing Categories**: ${validation.missingCategories.join(', ')}

## Coverage Analysis
- **Functional Requirements**: ${validation.coverage.functional}%
- **Non-Functional Requirements**: ${validation.coverage.nonFunctional}%
- **Business Rules**: ${validation.coverage.businessRules}%
- **User Interface**: ${validation.coverage.userInterface}%
- **Data Requirements**: ${validation.coverage.data}%

## Missing Elements
${validation.missingElements.map((element: string) => `• ${element}`).join('\n')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Address missing requirement categories',
        'Gather additional stakeholder input',
        'Complete requirement specification',
      ],
      warnings: validation.score < 70 ? ['Low completeness score - significant gaps detected'] : [],
      shouldBlockProgress: validation.score < 50,
    };
  }

  private async handleAmbiguityResolution(request: TaskRequest): Promise<TaskResponse> {
    const text = this.extractRequirementsText(request.prompt);
    const ambiguities = await this.identifyAmbiguities(text);
    
    return {
      summary: `Ambiguity Analysis - ${ambiguities.length} ambiguous statements found`,
      analysis: `
# Ambiguity Resolution Report

**Total Ambiguities**: ${ambiguities.length}

## Critical Ambiguities
${ambiguities.filter(a => a.severity === 'high').map(a => `• **${a.text}** - ${a.reason}`).join('\n')}

## Suggested Clarifications
${ambiguities.map(a => `• Replace "${a.text}" with "${a.suggestion}"`).join('\n')}
      `.trim(),
      recommendations: [
        'Prioritize resolution of high-severity ambiguities',
        'Prepare clarification questions for stakeholders',
        'Update requirements with clearer language',
      ],
      nextActions: [
        'Create stakeholder clarification questions',
        'Revise ambiguous requirement statements',
        'Validate clarifications with domain experts',
      ],
      warnings: ambiguities.filter(a => a.severity === 'high').length > 0 ? ['High-severity ambiguities require immediate attention'] : [],
      shouldBlockProgress: false,
    };
  }

  private async handleRequirementsStructuring(request: TaskRequest): Promise<TaskResponse> {
    const text = this.extractRequirementsText(request.prompt);
    const structured = await this.structureRequirements(text);
    
    return {
      summary: `Requirements Structuring Complete - organized into ${structured.categories.length} categories`,
      analysis: `
# Structured Requirements Report

**Categories**: ${structured.categories.length}
**Total Requirements**: ${structured.requirements.length}

## Category Breakdown
${structured.categories.map((cat: any) => `• **${cat.name}**: ${cat.requirements.length} requirements`).join('\n')}

## Priority Distribution
- **High Priority**: ${structured.requirements.filter((r: any) => r.priority === 'high').length}
- **Medium Priority**: ${structured.requirements.filter((r: any) => r.priority === 'medium').length}
- **Low Priority**: ${structured.requirements.filter((r: any) => r.priority === 'low').length}
      `.trim(),
      recommendations: [
        'Review category organization for logical grouping',
        'Validate priority assignments with stakeholders',
        'Ensure traceability between related requirements',
      ],
      nextActions: [
        'Create formal requirement specifications',
        'Generate requirement traceability matrix',
        'Proceed to user story creation phase',
      ],
      warnings: [],
      shouldBlockProgress: false,
    };
  }

  private async handleGapIdentification(request: TaskRequest): Promise<TaskResponse> {
    const text = this.extractRequirementsText(request.prompt);
    const gaps = await this.identifyRequirementGaps(text);
    
    return {
      summary: `Gap Analysis Complete - ${gaps.length} gaps identified`,
      analysis: `
# Requirements Gap Analysis

**Total Gaps**: ${gaps.length}

## Critical Gaps
${gaps.filter(g => g.impact === 'high').map(g => `• **${g.category}**: ${g.description}`).join('\n')}

## Recommended Additional Requirements
${gaps.map(g => `• ${g.suggestedRequirement}`).join('\n')}
      `.trim(),
      recommendations: [
        'Address critical gaps before proceeding',
        'Engage stakeholders for missing requirements',
        'Consider impact on project timeline',
      ],
      nextActions: [
        'Gather additional requirements for identified gaps',
        'Update requirement specifications',
        'Re-validate completeness after gap resolution',
      ],
      warnings: gaps.filter(g => g.impact === 'high').length > 0 ? ['Critical gaps may affect project success'] : [],
      shouldBlockProgress: gaps.filter(g => g.impact === 'high').length > 2,
    };
  }

  private async handleGenericNLProcessing(request: TaskRequest): Promise<TaskResponse> {
    const text = this.extractRequirementsText(request.prompt);
    const analysis = await this.performGenericNLAnalysis(text);
    
    return {
      summary: 'General Natural Language Processing Analysis',
      analysis: analysis.report,
      recommendations: analysis.recommendations,
      nextActions: analysis.nextActions,
      warnings: analysis.warnings,
      shouldBlockProgress: false,
    };
  }

  private classifyTask(description: string, prompt: string): string {
    const combined = (description + ' ' + prompt).toLowerCase();
    
    if (combined.includes('analyze') || combined.includes('process requirements')) {
      return 'analyze-requirements';
    }
    
    if (combined.includes('extract') || combined.includes('entities') || combined.includes('identify objects')) {
      return 'extract-entities';
    }
    
    if (combined.includes('complete') || combined.includes('validate') || combined.includes('check coverage')) {
      return 'validate-completeness';
    }
    
    if (combined.includes('ambig') || combined.includes('clarify') || combined.includes('unclear')) {
      return 'resolve-ambiguity';
    }
    
    if (combined.includes('structure') || combined.includes('organize') || combined.includes('categorize')) {
      return 'structure-requirements';
    }
    
    if (combined.includes('gap') || combined.includes('missing') || combined.includes('incomplete')) {
      return 'identify-gaps';
    }
    
    return 'generic-processing';
  }

  private extractRequirementsText(prompt: string): string {
    // More robust extraction: handle bullet points, numbered lists, and common requirement patterns
    const lines = prompt.split('\n');
    const requirementPatterns = [
      /^\s*[-*+]\s+(.+)/,                // Markdown/ASCII bullet points
      /^\s*\d+[\.\)]\s+(.+)/,            // Numbered lists (1. or 1) )
      /^\s*•\s+(.+)/,                    // Unicode bullet
      /^\s*Requirement\s*\d*[:\-\.]?\s*(.+)/i, // "Requirement 1: ..." etc.
      /^\s*(The system|System|It|Software|Application)\s+(shall|must|should|will)\b(.+)/i, // Common requirement phrasing
    ];

    const extracted: string[] = [];

    for (const line of lines) {
      const trimmed = line.trim();
      if (!trimmed || trimmed.startsWith('#') || trimmed.startsWith('//')) continue;
      let matched = false;
      for (const pattern of requirementPatterns) {
        const match = trimmed.match(pattern);
        if (match) {
          // Use the first capturing group if available, else the whole match
          extracted.push(match[1] ? match[1].trim() : trimmed);
          matched = true;
          break;
        }
      }
      // If not matched, but the line is long enough and ends with a period, treat as a possible requirement
      if (!matched && trimmed.length > 20 && /[\.!?]$/.test(trimmed)) {
        extracted.push(trimmed);
      }
    }

    return extracted.join('\n');
  }

  async processNaturalLanguageRequirements(text: string): Promise<ProcessedRequirements> {
    // Mock implementation - in real scenario, this would use NLP libraries
    const sentences = text.split(/[.!?]+/).filter(s => s.trim());
    
    const structured: RequirementDocument[] = sentences.map((sentence: string, index: number) => ({
      title: `Requirement ${index + 1}`,
      content: sentence.trim(),
      source: 'natural-language-input',
      type: this.inferRequirementType(sentence),
      priority: this.inferPriority(sentence),
    }));

    return {
      structured,
      summary: `Processed ${sentences.length} requirement statements from natural language input`,
      gaps: this.identifyStructuralGaps(structured),
      conflicts: this.detectConflicts(structured),
      ambiguities: this.detectAmbiguousLanguage(structured),
      clarificationNeeded: this.generateClarificationQuestions(structured),
    };
  }

  private inferRequirementType(sentence: string): 'functional' | 'non-functional' | 'business' | 'technical' {
    const lower = sentence.toLowerCase();
    
    if (lower.includes('performance') || lower.includes('speed') || lower.includes('security')) {
      return 'non-functional';
    }
    
    if (lower.includes('business') || lower.includes('revenue') || lower.includes('profit')) {
      return 'business';
    }
    
    if (lower.includes('system') || lower.includes('architecture') || lower.includes('database')) {
      return 'technical';
    }
    
    return 'functional';
  }

  private inferPriority(sentence: string): 'high' | 'medium' | 'low' {
    const lower = sentence.toLowerCase();
    
    if (lower.includes('must') || lower.includes('critical') || lower.includes('essential')) {
      return 'high';
    }
    
    if (lower.includes('should') || lower.includes('important') || lower.includes('preferred')) {
      return 'medium';
    }
    
    return 'low';
  }

  private identifyStructuralGaps(requirements: RequirementDocument[]): string[] {
    const gaps: string[] = [];
    
    const hasFunctional = requirements.some(r => r.type === 'functional');
    const hasNonFunctional = requirements.some(r => r.type === 'non-functional');
    const hasBusiness = requirements.some(r => r.type === 'business');
    
    if (!hasFunctional) gaps.push('No functional requirements identified');
    if (!hasNonFunctional) gaps.push('No non-functional requirements specified');
    if (!hasBusiness) gaps.push('Business requirements not clearly defined');
    
    return gaps;
  }

  private detectConflicts(requirements: RequirementDocument[]): string[] {
    // Initialize conflicts array to ensure it's properly initialized (addressing review comment)
    const conflicts: string[] = [];
    
    // Early return if no requirements to check
    if (!requirements || requirements.length === 0) {
      return conflicts;
    }
    
    // TODO: Implement more sophisticated conflict detection logic.
    // This basic implementation flags requirements with identical content but different types or priorities.
    for (let i = 0; i < requirements.length; i++) {
      for (let j = i + 1; j < requirements.length; j++) {
        if (
          requirements[i]?.content === requirements[j]?.content &&
          (requirements[i]?.type !== requirements[j]?.type || requirements[i]?.priority !== requirements[j]?.priority)
        ) {
          conflicts.push(
            `Conflict: Requirement "${requirements[i]?.content}" has differing type or priority (${requirements[i]?.type}/${requirements[i]?.priority} vs ${requirements[j]?.type}/${requirements[j]?.priority})`
          );
        }
      }
    }
    
    // Add complexity warning for large sets
    if (requirements.length > NaturalLanguageTaskAdapter.MAX_REQUIREMENTS_BEFORE_CONFLICTS) {
      conflicts.push('Potential conflicts between requirements due to complexity');
    }
    
    return conflicts;
  }

  private detectAmbiguousLanguage(requirements: RequirementDocument[]): string[] {
    const ambiguous = requirements.filter(r => 
      r.content.includes('should') || 
      r.content.includes('might') ||
      r.content.includes('possibly')
    );
    
    return ambiguous.map((r: RequirementDocument) => `Ambiguous language in: "${r.content}"`);
  }

  private generateClarificationQuestions(requirements: RequirementDocument[]): string[] {
    return requirements
      .filter((r: RequirementDocument) => r.priority === 'high' && this.detectAmbiguousLanguage([r]).length > 0)
      .map((r: RequirementDocument) => `Clarify specific behavior for: "${r.content}"`);
  }

  // Additional helper methods would be implemented here...
  private async extractBusinessEntities(text: string): Promise<BusinessEntity[]> {
    // Mock implementation
    return [
      { name: 'User', type: 'core', description: 'System user entity', relationships: ['has Profile'] },
      { name: 'Profile', type: 'supporting', description: 'User profile information' },
    ];
  }

  private async validateRequirementsCompleteness(text: string): Promise<CompletenessValidationResult> {
    // Mock implementation
    return {
      score: 75,
      missingCategories: ['performance', 'security'],
      coverage: {
        functional: 80,
        nonFunctional: 60,
        businessRules: 70,
        userInterface: 50,
        data: 65,
      },
      missingElements: ['Error handling requirements', 'Performance benchmarks'],
      recommendations: ['Add performance requirements', 'Specify security constraints'],
    };
  }

  private async identifyAmbiguities(text: string): Promise<any[]> {
    // Mock implementation
    return [
      {
        text: 'system should be fast',
        reason: 'Undefined performance criteria',
        suggestion: 'system should respond within 2 seconds',
        severity: 'high',
      },
    ];
  }

  private async structureRequirements(text: string): Promise<any> {
    // Mock implementation
    return {
      categories: [
        { name: 'User Management', requirements: [] },
        { name: 'Data Processing', requirements: [] },
      ],
      requirements: [],
    };
  }

  private async identifyRequirementGaps(text: string): Promise<any[]> {
    // Mock implementation
    return [
      {
        category: 'Security',
        description: 'Authentication requirements missing',
        impact: 'high',
        suggestedRequirement: 'System must authenticate users via secure login',
      },
    ];
  }

  private async performGenericNLAnalysis(text: string): Promise<any> {
    // Mock implementation
    return {
      report: 'General natural language analysis completed',
      recommendations: ['Consider more specific requirements'],
      nextActions: ['Proceed to formal specification'],
      warnings: [],
    };
  }

  private async analyzeRecentActivity(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    hasIncompleteRequirements: boolean;
    hasAmbiguousRequirements: boolean;
    completionActions: string[];
    clarificationActions: string[];
  }> {
    const requirementFiles = context.recentFiles.filter((f: string) => 
      f.includes('requirement') || f.includes('spec') || f.endsWith('.md')
    );
    
    const hasIncompleteRequirements = requirementFiles.length === 0 && 
      context.userIntent.toLowerCase().includes('implement');
    
    const hasAmbiguousRequirements = context.userIntent.includes('should') || 
      context.userIntent.includes('might');
    
    return {
      hasIncompleteRequirements,
      hasAmbiguousRequirements,
      completionActions: hasIncompleteRequirements ? [
        'Create comprehensive requirements specification',
        'Analyze stakeholder needs thoroughly',
        'Document functional and non-functional requirements',
      ] : [],
      clarificationActions: hasAmbiguousRequirements ? [
        'Clarify ambiguous requirement statements',
        'Define specific acceptance criteria',
        'Validate understanding with stakeholders',
      ] : [],
    };
  }
}


// Export for Claude Code Task tool integration
export const createNaturalLanguageTaskHandler = () => {
  const adapter = new NaturalLanguageTaskAdapter();
  
  return {
    handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
      return adapter.handleNaturalLanguageTask(request);
    },
    
    provideProactiveGuidance: async (context: ProactiveGuidanceContext): Promise<ProactiveGuidanceResult> => {
      return adapter.provideProactiveGuidance(context);
    },
  };
};