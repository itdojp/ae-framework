/**
 * Validation Task Adapter for Claude Code
 * 
 * This adapter integrates Phase 4 (Validation) processing with Claude Code's
 * Task tool, enabling seamless validation workflows for requirements,
 * user stories, specifications, and code quality.
 */

import { VerifyAgent } from './verify-agent.js';
import type { TaskRequest, TaskResponse } from './task-types.js';

export interface ValidationResult {
  isValid: boolean;
  score: number;
  issues: ValidationIssue[];
  recommendations: string[];
  coverageReport: CoverageReport;
}

export interface ValidationIssue {
  id: string;
  type: 'error' | 'warning' | 'info';
  severity: 'critical' | 'high' | 'medium' | 'low';
  category: string;
  description: string;
  location?: string;
  suggestion?: string;
}

export interface CoverageReport {
  functional: number;
  nonFunctional: number;
  business: number;
  technical: number;
  overall: number;
}

export class ValidationTaskAdapter {
  private agent: VerifyAgent;

  constructor() {
    // VerifyAgent doesn't use config pattern like FormalAgent
    this.agent = new VerifyAgent();
  }

  /**
   * Main handler for Validation tasks from Claude Code
   */
  async handleValidationTask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    
    switch (taskType) {
      case 'validate-requirements':
        return this.handleRequirementsValidation(request);
      
      case 'validate-user-stories':
        return this.handleUserStoriesValidation(request);
      
      case 'validate-specifications':
        return this.handleSpecificationValidation(request);
      
      case 'validate-traceability':
        return this.handleTraceabilityValidation(request);
      
      case 'validate-completeness':
        return this.handleCompletenessValidation(request);
      
      case 'validate-consistency':
        return this.handleConsistencyValidation(request);
      
      case 'validate-feasibility':
        return this.handleFeasibilityValidation(request);
      
      case 'cross-validate':
        return this.handleCrossValidation(request);
      
      default:
        return this.handleGenericValidation(request);
    }
  }

  /**
   * Proactive validation guidance for Claude Code
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
    const analysis = await this.analyzeRecentActivity(context);
    
    if (analysis.hasCriticalValidationIssues) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'block',
          message: 'Critical validation issues detected - must be resolved before proceeding',
          recommendedActions: analysis.criticalActions,
        },
      };
    }

    if (analysis.hasValidationGaps) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'warning',
          message: 'Validation gaps detected - recommend comprehensive validation',
          recommendedActions: analysis.validationActions,
        },
      };
    }

    if (analysis.shouldValidateChanges) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'suggestion',
          message: 'Recent changes should be validated for consistency',
          recommendedActions: analysis.changeValidationActions,
        },
      };
    }

    return {
      shouldIntervene: false,
      intervention: {
        type: 'suggestion',
        message: 'Validation status looks good',
        recommendedActions: [],
      },
    };
  }

  private async handleRequirementsValidation(request: TaskRequest): Promise<TaskResponse> {
    const requirementsInput = this.extractRequirementsInput(request.prompt);
    const validation = await this.validateRequirements(requirementsInput);
    
    return {
      summary: `Requirements Validation Complete - ${validation.score}% valid (${validation.issues.filter(i => i.type === 'error').length} errors, ${validation.issues.filter(i => i.type === 'warning').length} warnings)`,
      analysis: `
# Requirements Validation Report

**Validation Score**: ${validation.score}%
**Total Issues**: ${validation.issues.length}
**Critical Issues**: ${validation.issues.filter(i => i.severity === 'critical').length}

## Coverage Analysis
- **Functional Requirements**: ${validation.coverageReport.functional}%
- **Non-Functional Requirements**: ${validation.coverageReport.nonFunctional}%
- **Business Requirements**: ${validation.coverageReport.business}%
- **Technical Requirements**: ${validation.coverageReport.technical}%

## Critical Issues
${validation.issues
  .filter((i: ValidationIssue) => i.severity === 'critical')
  .map((i: ValidationIssue) => `• **${i.category}**: ${i.description}`)
  .join('\n')}

## High Priority Issues
${validation.issues
  .filter((i: ValidationIssue) => i.severity === 'high')
  .map((i: ValidationIssue) => `• **${i.category}**: ${i.description}`)
  .join('\n')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Address critical validation issues immediately',
        'Improve requirements coverage in weak areas',
        'Validate requirements with stakeholders',
        'Update requirements documentation',
      ],
      warnings: validation.issues
        .filter((i: ValidationIssue) => i.severity === 'critical' || i.severity === 'high')
        .map((i: ValidationIssue) => i.description),
      shouldBlockProgress: validation.issues.filter((i: ValidationIssue) => i.severity === 'critical').length > 0,
    };
  }

  private async handleUserStoriesValidation(request: TaskRequest): Promise<TaskResponse> {
    const storiesInput = this.extractStoriesInput(request.prompt);
    const validation = await this.validateUserStories(storiesInput);
    
    return {
      summary: `User Stories Validation Complete - ${validation.score}% compliant`,
      analysis: `
# User Stories Validation Report

**Validation Score**: ${validation.score}%
**Stories Analyzed**: ${validation.totalStories}
**Valid Stories**: ${validation.validStories}

## Quality Metrics
- **Proper Format (As a... I want... So that...)**: ${validation.qualityMetrics.formatCompliance}%
- **Clear Acceptance Criteria**: ${validation.qualityMetrics.acceptanceCriteria}%
- **Testable Stories**: ${validation.qualityMetrics.testability}%
- **Independent Stories**: ${validation.qualityMetrics.independence}%
- **Estimable Stories**: ${validation.qualityMetrics.estimability}%

## Common Issues
${validation.commonIssues.map((issue: any) => `• ${issue.description} (${issue.frequency} occurrences)`).join('\n')}

## Story-Specific Issues
${validation.storyIssues.map((issue: any) => `• **${issue.storyId}**: ${issue.description}`).join('\n')}
      `.trim(),
      recommendations: [
        'Fix stories with format compliance issues',
        'Add missing acceptance criteria',
        'Break down complex stories for better testability',
        'Ensure story independence',
      ],
      nextActions: [
        'Review and fix identified story issues',
        'Validate story acceptance criteria',
        'Ensure all stories are properly estimated',
        'Check story dependencies',
      ],
      warnings: validation.blockingIssues.map((issue: any) => issue.description),
      shouldBlockProgress: validation.blockingIssues.length > 0,
    };
  }

  private async handleSpecificationValidation(request: TaskRequest): Promise<TaskResponse> {
    const specInput = this.extractSpecificationInput(request.prompt);
    const validation = await this.validateSpecifications(specInput);
    
    return {
      summary: `Specification Validation Complete - ${validation.score}% compliant`,
      analysis: `
# Specification Validation Report

**Overall Compliance**: ${validation.score}%
**Specifications Analyzed**: ${validation.totalSpecs}

## Compliance Breakdown
- **Formal Notation**: ${validation.compliance.formalNotation}%
- **Completeness**: ${validation.compliance.completeness}%
- **Consistency**: ${validation.compliance.consistency}%
- **Clarity**: ${validation.compliance.clarity}%
- **Testability**: ${validation.compliance.testability}%

## Validation Issues by Category
${Object.entries(validation.issuesByCategory).map(([category, count]: [string, any]) => 
  `• **${category}**: ${count} issues`
).join('\n')}

## Critical Specification Gaps
${validation.criticalGaps.map((gap: any) => `• ${gap.description} (Impact: ${gap.impact})`).join('\n')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Address critical specification gaps',
        'Improve formal notation compliance',
        'Enhance specification clarity',
        'Validate specifications with domain experts',
      ],
      warnings: validation.criticalGaps.map((gap: any) => gap.description),
      shouldBlockProgress: validation.criticalGaps.length > 2,
    };
  }

  private async handleTraceabilityValidation(request: TaskRequest): Promise<TaskResponse> {
    const traceabilityInput = this.extractTraceabilityInput(request.prompt);
    const validation = await this.validateTraceability(traceabilityInput);
    
    return {
      summary: `Traceability Validation Complete - ${validation.coveragePercentage}% traceability coverage`,
      analysis: `
# Traceability Validation Report

**Traceability Coverage**: ${validation.coveragePercentage}%
**Total Trace Links**: ${validation.totalLinks}
**Broken Links**: ${validation.brokenLinks.length}

## Traceability Matrix
${validation.matrix.map((row: any) => 
  `• ${row.source} → ${row.targets.join(', ')} (${row.coverage}% coverage)`
).join('\n')}

## Missing Trace Links
${validation.missingLinks.map((link: any) => 
  `• ${link.from} → ${link.to} (${link.reason})`
).join('\n')}

## Orphaned Artifacts
${validation.orphanedArtifacts.map((artifact: any) => 
  `• **${artifact.type}**: ${artifact.name} (no traceability)`
).join('\n')}
      `.trim(),
      recommendations: [
        'Establish missing trace links',
        'Fix broken traceability relationships',
        'Address orphaned artifacts',
        'Maintain traceability during changes',
      ],
      nextActions: [
        'Create traceability matrix',
        'Establish missing links',
        'Validate existing trace relationships',
        'Set up automated traceability checking',
      ],
      warnings: validation.brokenLinks.map((link: any) => `Broken link: ${link.from} → ${link.to}`),
      shouldBlockProgress: validation.coveragePercentage < 70,
    };
  }

  private async handleCompletenessValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractCompletenessInput(request.prompt);
    const validation = await this.validateCompleteness(input);
    
    return {
      summary: `Completeness Validation Complete - ${validation.completenessScore}% complete`,
      analysis: `
# Completeness Validation Report

**Overall Completeness**: ${validation.completenessScore}%

## Category Completeness
${validation.categoryScores.map((cat: any) => 
  `• **${cat.name}**: ${cat.score}% (${cat.missing} missing items)`
).join('\n')}

## Missing Components
${validation.missingComponents.map((comp: any) => 
  `• **${comp.category}**: ${comp.description} (Priority: ${comp.priority})`
).join('\n')}

## Completeness Trends
- **Improving Areas**: ${validation.trends.improving.join(', ')}
- **Declining Areas**: ${validation.trends.declining.join(', ')}
- **Stable Areas**: ${validation.trends.stable.join(', ')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Address high-priority missing components',
        'Focus on declining completeness areas',
        'Validate completeness with stakeholders',
      ],
      warnings: validation.criticalGaps.map((gap: any) => gap.description),
      shouldBlockProgress: validation.completenessScore < 60,
    };
  }

  private async handleConsistencyValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractConsistencyInput(request.prompt);
    const validation = await this.validateConsistency(input);
    
    return {
      summary: `Consistency Validation Complete - ${validation.consistencyScore}% consistent`,
      analysis: `
# Consistency Validation Report

**Overall Consistency**: ${validation.consistencyScore}%
**Inconsistencies Found**: ${validation.inconsistencies.length}

## Consistency by Type
- **Terminology**: ${validation.terminologyConsistency}%
- **Format**: ${validation.formatConsistency}%
- **Business Rules**: ${validation.businessRuleConsistency}%
- **Technical Constraints**: ${validation.technicalConsistency}%

## Major Inconsistencies
${validation.majorInconsistencies.map((inc: any) => 
  `• **${inc.type}**: ${inc.description} (Location: ${inc.location})`
).join('\n')}

## Terminology Conflicts
${validation.terminologyConflicts.map((conflict: any) => 
  `• "${conflict.term}": ${conflict.definitions.join(' vs ')}`
).join('\n')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Resolve major inconsistencies',
        'Standardize terminology usage',
        'Create consistency guidelines',
        'Implement consistency checking',
      ],
      warnings: validation.majorInconsistencies.map((inc: any) => inc.description),
      shouldBlockProgress: validation.majorInconsistencies.length > 3,
    };
  }

  private async handleFeasibilityValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractFeasibilityInput(request.prompt);
    const validation = await this.validateFeasibility(input);
    
    return {
      summary: `Feasibility Validation Complete - ${validation.feasibilityScore}% feasible`,
      analysis: `
# Feasibility Validation Report

**Overall Feasibility**: ${validation.feasibilityScore}%

## Feasibility by Dimension
- **Technical Feasibility**: ${validation.technical}%
- **Economic Feasibility**: ${validation.economic}%
- **Operational Feasibility**: ${validation.operational}%
- **Schedule Feasibility**: ${validation.schedule}%

## Risk Factors
${validation.riskFactors.map((risk: any) => 
  `• **${risk.category}**: ${risk.description} (Impact: ${risk.impact}, Probability: ${risk.probability})`
).join('\n')}

## Infeasible Requirements
${validation.infeasibleRequirements.map((req: any) => 
  `• **${req.id}**: ${req.reason} (Suggested: ${req.alternative})`
).join('\n')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Address infeasible requirements',
        'Mitigate high-risk factors',
        'Validate technical constraints',
        'Review resource requirements',
      ],
      warnings: validation.highRiskFactors.map((risk: any) => risk.description),
      shouldBlockProgress: validation.infeasibleRequirements.length > 0,
    };
  }

  private async handleCrossValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractCrossValidationInput(request.prompt);
    const validation = await this.performCrossValidation(input);
    
    return {
      summary: `Cross-Validation Complete - ${validation.overallScore}% alignment across phases`,
      analysis: `
# Cross-Phase Validation Report

**Overall Alignment**: ${validation.overallScore}%

## Phase Alignment Matrix
${validation.phaseAlignment.map((phase: any) => 
  `• **${phase.name}**: ${phase.score}% aligned with other phases`
).join('\n')}

## Cross-Phase Issues
${validation.crossPhaseIssues.map((issue: any) => 
  `• **${issue.phases.join(' ↔ ')}**: ${issue.description} (Severity: ${issue.severity})`
).join('\n')}

## Alignment Gaps
${validation.alignmentGaps.map((gap: any) => 
  `• ${gap.description} (Between: ${gap.phases.join(' and ')})`
).join('\n')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Resolve cross-phase inconsistencies',
        'Improve phase alignment',
        'Validate phase transitions',
        'Establish cross-phase review process',
      ],
      warnings: validation.criticalIssues.map((issue: any) => issue.description),
      shouldBlockProgress: validation.criticalIssues.length > 0,
    };
  }

  private async handleGenericValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractGenericInput(request.prompt);
    const validation = await this.performGenericValidation(input);
    
    return {
      summary: 'General Validation Analysis',
      analysis: validation.report,
      recommendations: validation.recommendations,
      nextActions: validation.nextActions,
      warnings: validation.warnings,
      shouldBlockProgress: validation.hasBlockingIssues,
    };
  }

  private classifyTask(description: string, prompt: string): string {
    const combined = (description + ' ' + prompt).toLowerCase();
    
    if (combined.includes('requirements') && combined.includes('validate')) {
      return 'validate-requirements';
    }
    
    if (combined.includes('user stories') || combined.includes('stories')) {
      return 'validate-user-stories';
    }
    
    if (combined.includes('specification') || combined.includes('specs')) {
      return 'validate-specifications';
    }
    
    if (combined.includes('traceability') || combined.includes('trace')) {
      return 'validate-traceability';
    }
    
    if (combined.includes('completeness') || combined.includes('complete')) {
      return 'validate-completeness';
    }
    
    if (combined.includes('consistency') || combined.includes('consistent')) {
      return 'validate-consistency';
    }
    
    if (combined.includes('feasibility') || combined.includes('feasible')) {
      return 'validate-feasibility';
    }
    
    if (combined.includes('cross') || combined.includes('alignment')) {
      return 'cross-validate';
    }
    
    return 'generic-validation';
  }

  // Input extraction methods (simplified)
  private extractRequirementsInput(prompt: string): any { return {}; }
  private extractStoriesInput(prompt: string): any { return {}; }
  private extractSpecificationInput(prompt: string): any { return {}; }
  private extractTraceabilityInput(prompt: string): any { return {}; }
  private extractCompletenessInput(prompt: string): any { return {}; }
  private extractConsistencyInput(prompt: string): any { return {}; }
  private extractFeasibilityInput(prompt: string): any { return {}; }
  private extractCrossValidationInput(prompt: string): any { return {}; }
  private extractGenericInput(prompt: string): any { return {}; }

  // Mock validation methods (to be implemented with actual validation logic)
  private async validateRequirements(input: any): Promise<ValidationResult> {
    return {
      isValid: true,
      score: 85,
      issues: [
        {
          id: 'REQ001',
          type: 'warning',
          severity: 'medium',
          category: 'Clarity',
          description: 'Requirement statement could be more specific',
          suggestion: 'Add quantifiable acceptance criteria',
        },
      ],
      recommendations: ['Improve requirement specificity'],
      coverageReport: {
        functional: 90,
        nonFunctional: 70,
        business: 80,
        technical: 75,
        overall: 85,
      },
    };
  }

  async validateUserStories(input: any): Promise<any> {
    return {
      score: 80,
      totalStories: 10,
      validStories: 8,
      qualityMetrics: {
        formatCompliance: 90,
        acceptanceCriteria: 70,
        testability: 85,
        independence: 80,
        estimability: 75,
      },
      commonIssues: [
        { description: 'Missing acceptance criteria', frequency: 3 },
      ],
      storyIssues: [],
      blockingIssues: [],
    };
  }

  private async validateSpecifications(input: any): Promise<any> {
    return {
      score: 75,
      totalSpecs: 5,
      compliance: {
        formalNotation: 80,
        completeness: 70,
        consistency: 85,
        clarity: 75,
        testability: 80,
      },
      issuesByCategory: {
        'Formal Notation': 2,
        'Completeness': 3,
      },
      criticalGaps: [],
      recommendations: ['Improve formal notation usage'],
    };
  }

  private async validateTraceability(input: any): Promise<any> {
    return {
      coveragePercentage: 80,
      totalLinks: 50,
      brokenLinks: [],
      matrix: [
        { source: 'Requirements', targets: ['User Stories'], coverage: 85 },
      ],
      missingLinks: [],
      orphanedArtifacts: [],
    };
  }

  private async validateCompleteness(input: any): Promise<any> {
    return {
      completenessScore: 75,
      categoryScores: [
        { name: 'Requirements', score: 80, missing: 2 },
      ],
      missingComponents: [],
      trends: { improving: [], declining: [], stable: [] },
      recommendations: ['Address missing components'],
      criticalGaps: [],
    };
  }

  private async validateConsistency(input: any): Promise<any> {
    return {
      consistencyScore: 85,
      inconsistencies: [],
      terminologyConsistency: 90,
      formatConsistency: 80,
      businessRuleConsistency: 85,
      technicalConsistency: 80,
      majorInconsistencies: [],
      terminologyConflicts: [],
      recommendations: ['Standardize terminology'],
    };
  }

  private async validateFeasibility(input: any): Promise<any> {
    return {
      feasibilityScore: 80,
      technical: 85,
      economic: 75,
      operational: 80,
      schedule: 70,
      riskFactors: [],
      infeasibleRequirements: [],
      highRiskFactors: [],
      recommendations: ['Review schedule constraints'],
    };
  }

  private async performCrossValidation(input: any): Promise<any> {
    return {
      overallScore: 85,
      phaseAlignment: [
        { name: 'Requirements-Stories', score: 90 },
      ],
      crossPhaseIssues: [],
      alignmentGaps: [],
      criticalIssues: [],
      recommendations: ['Maintain cross-phase consistency'],
    };
  }

  private async performGenericValidation(input: any): Promise<any> {
    return {
      report: 'General validation completed',
      recommendations: ['Continue with validation best practices'],
      nextActions: ['Proceed to next phase'],
      warnings: [],
      hasBlockingIssues: false,
    };
  }

  private async analyzeRecentActivity(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    hasCriticalValidationIssues: boolean;
    hasValidationGaps: boolean;
    shouldValidateChanges: boolean;
    criticalActions: string[];
    validationActions: string[];
    changeValidationActions: string[];
  }> {
    const hasRequirementChanges = context.recentFiles.some((f: string) => 
      f.includes('requirement') || f.includes('spec')
    );
    
    const hasCodeChanges = context.recentFiles.some((f: string) => 
      f.endsWith('.ts') || f.endsWith('.js')
    );
    
    return {
      hasCriticalValidationIssues: false,
      hasValidationGaps: hasRequirementChanges && !context.recentActions.includes('validate'),
      shouldValidateChanges: hasCodeChanges || hasRequirementChanges,
      criticalActions: [],
      validationActions: hasRequirementChanges ? [
        'Validate updated requirements',
        'Check consistency with existing specifications',
        'Verify traceability links',
      ] : [],
      changeValidationActions: [
        'Validate recent changes for consistency',
        'Check impact on existing requirements',
        'Update validation documentation',
      ],
    };
  }
}

// Export for Claude Code Task tool integration
export const createValidationTaskHandler = () => {
  const adapter = new ValidationTaskAdapter();
  
  return {
    handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
      return adapter.handleValidationTask(request);
    },
    
    provideProactiveGuidance: async (context: any): Promise<any> => {
      return adapter.provideProactiveGuidance(context);
    },
  };
};
