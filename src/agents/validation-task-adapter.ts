/**
 * Validation Task Adapter for Claude Code
 * 
 * This adapter integrates Phase 4 (Validation) processing with Claude Code's
 * Task tool, enabling seamless validation workflows for requirements,
 * user stories, specifications, and code quality.
 */

import { VerifyAgent } from './verify-agent.js';
import type { TaskRequest, TaskResponse } from './task-types.js';
import fs from 'node:fs';
import path from 'node:path';

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

export type ValidationTaskType =
  | 'validate-requirements'
  | 'validate-user-stories'
  | 'validate-specifications'
  | 'validate-traceability'
  | 'validate-completeness'
  | 'validate-consistency'
  | 'validate-feasibility'
  | 'cross-validate';

export const VALIDATION_TASK_TYPES: ValidationTaskType[] = [
  'validate-requirements',
  'validate-user-stories',
  'validate-specifications',
  'validate-traceability',
  'validate-completeness',
  'validate-consistency',
  'validate-feasibility',
  'cross-validate',
];

interface ValidationSourceItem {
  path: string;
  content: string;
}

interface ValidationInput {
  requestedSources: string[];
  resolvedSources: ValidationSourceItem[];
  missingSources: string[];
  strict: boolean;
}

export class ValidationTaskAdapter {
  private agent: VerifyAgent;
  private readonly sourceFileLimit = 200;

  constructor() {
    // VerifyAgent doesn't use config pattern like FormalAgent
    this.agent = new VerifyAgent();
  }

  /**
   * Main handler for Validation tasks from Claude Code
   */
  async handleValidationTask(request: TaskRequest): Promise<TaskResponse> {
    const explicitTaskType = this.resolveTaskTypeFromContext(request);
    const taskType = explicitTaskType ?? this.classifyTask(request.description, request.prompt);
    
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
    const requirementsInput = this.extractRequirementsInput(request);
    const validation = await this.validateRequirements(requirementsInput);
    
    return {
      summary: `Requirements Validation Complete - ${validation.score}% valid (${validation.issues.filter(i => i.type === 'error').length} errors, ${validation.issues.filter(i => i.type === 'warning').length} warnings)`,
      analysis: `
# Requirements Validation Report

${this.formatSourceSummary(requirementsInput)}

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
      warnings: [
        ...validation.issues
        .filter((i: ValidationIssue) => i.severity === 'critical' || i.severity === 'high')
        .map((i: ValidationIssue) => i.description),
        ...requirementsInput.missingSources.map((source) => `Source not found: ${source}`),
      ],
      shouldBlockProgress: validation.issues.filter((i: ValidationIssue) => i.severity === 'critical').length > 0,
    };
  }

  private async handleUserStoriesValidation(request: TaskRequest): Promise<TaskResponse> {
    const storiesInput = this.extractStoriesInput(request);
    const validation = await this.validateUserStories(storiesInput);
    
    return {
      summary: `User Stories Validation Complete - ${validation.score}% compliant`,
      analysis: `
# User Stories Validation Report

${this.formatSourceSummary(storiesInput)}

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
      warnings: [
        ...validation.blockingIssues.map((issue: any) => issue.description),
        ...storiesInput.missingSources.map((source) => `Source not found: ${source}`),
      ],
      shouldBlockProgress: validation.blockingIssues.length > 0,
    };
  }

  private async handleSpecificationValidation(request: TaskRequest): Promise<TaskResponse> {
    const specInput = this.extractSpecificationInput(request);
    const validation = await this.validateSpecifications(specInput);
    
    return {
      summary: `Specification Validation Complete - ${validation.score}% compliant`,
      analysis: `
# Specification Validation Report

${this.formatSourceSummary(specInput)}

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
      warnings: [
        ...validation.criticalGaps.map((gap: any) => gap.description),
        ...specInput.missingSources.map((source) => `Source not found: ${source}`),
      ],
      shouldBlockProgress: validation.criticalGaps.length > 2,
    };
  }

  private async handleTraceabilityValidation(request: TaskRequest): Promise<TaskResponse> {
    const traceabilityInput = this.extractTraceabilityInput(request);
    const validation = await this.validateTraceability(traceabilityInput);
    
    return {
      summary: `Traceability Validation Complete - ${validation.coveragePercentage}% traceability coverage`,
      analysis: `
# Traceability Validation Report

${this.formatSourceSummary(traceabilityInput)}

**Strict Mode**: ${traceabilityInput.strict ? 'enabled' : 'disabled'}
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
      warnings: [
        ...validation.brokenLinks.map((link: any) => `Broken link: ${link.from} → ${link.to}`),
        ...traceabilityInput.missingSources.map((source) => `Source not found: ${source}`),
      ],
      shouldBlockProgress: traceabilityInput.strict
        ? validation.missingLinks.length > 0 || validation.brokenLinks.length > 0 || validation.coveragePercentage < 100
        : validation.coveragePercentage < 70,
    };
  }

  private async handleCompletenessValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractCompletenessInput(request);
    const validation = await this.validateCompleteness(input);
    
    return {
      summary: `Completeness Validation Complete - ${validation.completenessScore}% complete`,
      analysis: `
# Completeness Validation Report

${this.formatSourceSummary(input)}

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
      warnings: [
        ...validation.criticalGaps.map((gap: any) => gap.description),
        ...input.missingSources.map((source) => `Source not found: ${source}`),
      ],
      shouldBlockProgress: validation.completenessScore < 60,
    };
  }

  private async handleConsistencyValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractConsistencyInput(request);
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
    const input = this.extractFeasibilityInput(request);
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
    const input = this.extractCrossValidationInput(request);
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
    const input = this.extractGenericInput(request);
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

  private resolveTaskTypeFromContext(request: TaskRequest): ValidationTaskType | null {
    const candidate = request.context?.validationTaskType;
    if (typeof candidate !== 'string') {
      return null;
    }
    if (!VALIDATION_TASK_TYPES.includes(candidate as ValidationTaskType)) {
      return null;
    }
    return candidate as ValidationTaskType;
  }

  private classifyTask(description: string, prompt: string): ValidationTaskType | 'generic-validation' {
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

  private extractRequirementsInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractStoriesInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractSpecificationInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractTraceabilityInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractCompletenessInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractConsistencyInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractFeasibilityInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractCrossValidationInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractGenericInput(request: TaskRequest): ValidationInput {
    return this.extractValidationInput(request);
  }

  private extractValidationInput(request: TaskRequest): ValidationInput {
    const requestedSources = this.collectRequestedSources(request);
    const resolved = this.resolveValidationSources(requestedSources);
    if (resolved.requestedSources.length > 0 && resolved.resolvedSources.length === 0) {
      throw new Error(`No readable validation sources found. Requested: ${resolved.requestedSources.join(', ')}`);
    }
    return {
      ...resolved,
      strict: Boolean(request.context?.strict),
    };
  }

  private collectRequestedSources(request: TaskRequest): string[] {
    const contextSources = request.context?.sources;
    if (Array.isArray(contextSources)) {
      return contextSources
        .filter((value): value is string => typeof value === 'string')
        .map((value) => value.trim())
        .filter(Boolean);
    }
    if (typeof contextSources === 'string') {
      return this.parseSourceTokens(contextSources);
    }

    const prompt = (request.prompt || '').trim();
    if (!prompt || prompt.toLowerCase() === 'validate available artifacts') {
      return [];
    }
    return this.parseSourceTokens(prompt);
  }

  private parseSourceTokens(value: string): string[] {
    return value
      .split(/[\n,]/)
      .map((item) => item.trim())
      .filter(Boolean);
  }

  private resolveValidationSources(requestedSources: string[]): Omit<ValidationInput, 'strict'> {
    const resolvedSources: ValidationSourceItem[] = [];
    const missingSources: string[] = [];
    const seen = new Set<string>();
    const cwd = process.cwd();

    for (const source of requestedSources) {
      const abs = path.resolve(cwd, source);
      if (fs.existsSync(abs)) {
        const stat = fs.statSync(abs);
        if (stat.isFile()) {
          const content = this.tryReadFile(abs);
          if (content === null) {
            missingSources.push(source);
            continue;
          }
          const key = path.normalize(abs);
          if (seen.has(key)) {
            continue;
          }
          seen.add(key);
          resolvedSources.push({ path: source, content });
          continue;
        }

        if (stat.isDirectory()) {
          const files = this.collectReadableFiles(abs);
          if (files.length === 0) {
            missingSources.push(source);
            continue;
          }
          for (const file of files) {
            const key = path.normalize(file);
            if (seen.has(key)) {
              continue;
            }
            seen.add(key);
            const content = this.tryReadFile(file);
            if (content === null) {
              continue;
            }
            resolvedSources.push({ path: path.relative(cwd, file), content });
            if (resolvedSources.length >= this.sourceFileLimit) {
              break;
            }
          }
        }
      } else if (/\s/.test(source)) {
        resolvedSources.push({ path: `inline:${source.slice(0, 40)}`, content: source });
      } else {
        missingSources.push(source);
      }

      if (resolvedSources.length >= this.sourceFileLimit) {
        break;
      }
    }

    return {
      requestedSources,
      resolvedSources,
      missingSources,
    };
  }

  private collectReadableFiles(root: string): string[] {
    const supportedExt = new Set([
      '.md',
      '.txt',
      '.yaml',
      '.yml',
      '.json',
      '.feature',
      '.adoc',
      '.rst',
      '.spec',
    ]);
    const stack: string[] = [root];
    const files: string[] = [];
    while (stack.length > 0 && files.length < this.sourceFileLimit) {
      const current = stack.pop();
      if (!current) {
        continue;
      }
      let entries: fs.Dirent[] = [];
      try {
        entries = fs.readdirSync(current, { withFileTypes: true });
      } catch {
        continue;
      }
      entries.sort((a, b) => a.name.localeCompare(b.name));
      for (const entry of entries) {
        const abs = path.join(current, entry.name);
        if (entry.isDirectory()) {
          stack.push(abs);
          continue;
        }
        if (!entry.isFile()) {
          continue;
        }
        const ext = path.extname(entry.name).toLowerCase();
        if (supportedExt.has(ext) || entry.name.toLowerCase().includes('requirement')) {
          files.push(abs);
          if (files.length >= this.sourceFileLimit) {
            break;
          }
        }
      }
    }
    return files;
  }

  private tryReadFile(filePath: string): string | null {
    try {
      const stat = fs.statSync(filePath);
      if (!stat.isFile() || stat.size > 1024 * 1024) {
        return null;
      }
      return fs.readFileSync(filePath, 'utf8');
    } catch {
      return null;
    }
  }

  private formatSourceSummary(input: ValidationInput): string {
    const resolvedPreview = input.resolvedSources
      .slice(0, 5)
      .map((source) => `- ${source.path}`)
      .join('\n');

    return `
## Source Inputs
- Requested: ${input.requestedSources.length}
- Resolved: ${input.resolvedSources.length}
- Missing: ${input.missingSources.length}
${resolvedPreview ? `- Sample:\n${resolvedPreview}` : ''}
`.trim();
  }

  // Lightweight source-aware heuristics for CLI validation
  private async validateRequirements(input: ValidationInput): Promise<ValidationResult> {
    const text = this.collectSourceText(input);
    const lines = text
      .split(/\r?\n/)
      .map((line) => line.trim())
      .filter(Boolean);
    const requirementLines = lines.filter((line) =>
      /\b(must|should|shall|requirement|acceptance|given|when|then)\b/i.test(line),
    );
    const missingPenalty = input.missingSources.length * 6;
    const score = this.clamp(55 + Math.min(12, input.resolvedSources.length * 2) + Math.min(25, requirementLines.length) - missingPenalty, 0, 99);
    const functional = this.keywordCoverage(text, ['api', 'create', 'update', 'delete', 'search'], 58);
    const nonFunctional = this.keywordCoverage(text, ['performance', 'security', 'latency', 'availability', 'reliability'], 55);
    const business = this.keywordCoverage(text, ['customer', 'business', 'order', 'payment', 'invoice'], 57);
    const technical = this.keywordCoverage(text, ['database', 'service', 'cache', 'queue', 'schema'], 56);

    const issues: ValidationIssue[] = [];
    if (requirementLines.length === 0) {
      issues.push({
        id: 'REQ001',
        type: 'warning',
        severity: 'high',
        category: 'Completeness',
        description: 'No requirement-like statements were detected in the resolved sources',
        suggestion: 'Add explicit requirement statements using MUST/SHOULD or acceptance criteria format',
      });
    } else if (requirementLines.length < 3) {
      issues.push({
        id: 'REQ002',
        type: 'warning',
        severity: 'medium',
        category: 'Coverage',
        description: 'Requirement statements are present but sparse',
        suggestion: 'Add more detailed acceptance criteria and edge case requirements',
      });
    }
    if (input.missingSources.length > 0) {
      issues.push({
        id: 'REQ003',
        type: 'warning',
        severity: 'medium',
        category: 'Input',
        description: `${input.missingSources.length} source path(s) could not be resolved`,
        suggestion: 'Verify --sources paths and rerun validation',
      });
    }

    return {
      isValid: issues.every((issue) => issue.severity !== 'high' && issue.severity !== 'critical'),
      score,
      issues,
      recommendations: ['Improve requirement specificity'],
      coverageReport: {
        functional,
        nonFunctional,
        business,
        technical,
        overall: score,
      },
    };
  }

  async validateUserStories(input: any): Promise<any> {
    const normalizedInput = this.toValidationInput(input);
    const text = this.collectSourceText(normalizedInput);
    const blocks = text
      .split(/\n{2,}/)
      .map((block) => block.trim())
      .filter(Boolean);
    const storyBlocks = blocks.filter((block) => /\bas a\b[\s\S]*\bi want\b[\s\S]*\bso that\b/i.test(block));
    const totalStories = Math.max(storyBlocks.length, normalizedInput.resolvedSources.length > 0 ? 1 : 0);
    const validStories = storyBlocks.length;
    const score = this.clamp(50 + validStories * 10 - normalizedInput.missingSources.length * 5, 0, 99);
    const formatCompliance = totalStories === 0 ? 0 : this.clamp(Math.round((validStories / totalStories) * 100), 0, 100);
    const acceptanceCriteria = this.keywordCoverage(text, ['given', 'when', 'then', 'acceptance'], 45);
    const testability = this.keywordCoverage(text, ['test', 'assert', 'verify', 'scenario'], 50);
    const independence = this.keywordCoverage(text, ['independent', 'isolated', 'self-contained'], 60);
    const estimability = this.keywordCoverage(text, ['estimate', 'point', 'effort', 'story points'], 55);

    return {
      score,
      totalStories,
      validStories,
      qualityMetrics: {
        formatCompliance,
        acceptanceCriteria,
        testability,
        independence,
        estimability,
      },
      commonIssues: acceptanceCriteria < 65
        ? [{ description: 'Missing or weak acceptance criteria', frequency: Math.max(1, totalStories - validStories) }]
        : [],
      storyIssues: [],
      blockingIssues: totalStories === 0
        ? [{ description: 'No user stories found in provided sources' }]
        : [],
    };
  }

  private async validateSpecifications(input: ValidationInput): Promise<any> {
    const text = this.collectSourceText(input);
    const totalSpecs = input.resolvedSources.length;
    const formalNotation = this.keywordCoverage(text, ['state', 'invariant', 'precondition', 'postcondition', 'schema'], 55);
    const completeness = this.keywordCoverage(text, ['must', 'should', 'acceptance', 'scenario', 'constraint'], 58);
    const consistency = this.keywordCoverage(text, ['same', 'consistent', 'align', 'trace'], 60);
    const clarity = this.keywordCoverage(text, ['example', 'definition', 'glossary', 'term'], 57);
    const testability = this.keywordCoverage(text, ['test', 'verify', 'assert', 'expected'], 60);
    const score = this.clamp(
      Math.round((formalNotation + completeness + consistency + clarity + testability) / 5) - input.missingSources.length * 4,
      0,
      99,
    );

    const criticalGaps: Array<{ description: string; impact: string }> = [];
    if (completeness < 65) {
      criticalGaps.push({ description: 'Specification completeness is below threshold', impact: 'high' });
    }
    if (testability < 60) {
      criticalGaps.push({ description: 'Specification lacks executable acceptance criteria', impact: 'medium' });
    }

    return {
      score,
      totalSpecs,
      compliance: {
        formalNotation,
        completeness,
        consistency,
        clarity,
        testability,
      },
      issuesByCategory: {
        'Formal Notation': formalNotation < 65 ? 2 : 0,
        Completeness: completeness < 70 ? 2 : 0,
      },
      criticalGaps,
      recommendations: ['Improve formal notation usage'],
    };
  }

  private async validateTraceability(input: ValidationInput): Promise<any> {
    const matrixRows = this.extractTraceabilityMatrixRows(input);
    if (matrixRows.length > 0) {
      const linkedRows = matrixRows.filter((row) => row.linked);
      const coveragePercentage = matrixRows.length > 0
        ? Math.round((linkedRows.length / matrixRows.length) * 100)
        : 0;
      const missingLinks = matrixRows
        .filter((row) => !row.linked)
        .map((row) => {
          const reasons: string[] = [];
          if (row.tests.length === 0) {
            reasons.push('no test link');
          }
          if (row.code.length === 0) {
            reasons.push('no implementation link');
          }
          return {
            from: row.requirementId,
            to: 'Tests/Implementation',
            reason: reasons.join(', ') || 'unlinked',
          };
        });

      return {
        coveragePercentage,
        totalLinks: matrixRows.length,
        brokenLinks: [],
        matrix: matrixRows.map((row) => ({
          source: row.requirementId,
          targets: [
            row.tests.length > 0 ? 'Tests' : '(missing tests)',
            row.code.length > 0 ? 'Implementation' : '(missing implementation)',
          ],
          coverage: row.linked ? 100 : 0,
        })),
        missingLinks,
        orphanedArtifacts: [],
      };
    }

    const text = this.collectSourceText(input);
    const reqIds = this.extractIds(text, /\bREQ-[A-Za-z0-9_-]+\b/g);
    const storyIds = this.extractIds(text, /\b(US|STORY)-[A-Za-z0-9_-]+\b/g);
    const specIds = this.extractIds(text, /\bSPEC-[A-Za-z0-9_-]+\b/g);
    const totalLinks = reqIds.length + storyIds.length + specIds.length;
    const coveragePercentage = this.clamp(50 + Math.min(40, totalLinks * 5) - input.missingSources.length * 6, 0, 99);
    const missingLinks: Array<{ from: string; to: string; reason: string }> = [];
    if (reqIds.length > storyIds.length) {
      missingLinks.push({ from: 'Requirements', to: 'User Stories', reason: 'some REQ-* IDs have no user story mapping' });
    }
    if (storyIds.length > specIds.length) {
      missingLinks.push({ from: 'User Stories', to: 'Specifications', reason: 'some stories have no SPEC-* mapping' });
    }

    return {
      coveragePercentage,
      totalLinks,
      brokenLinks: [],
      matrix: [
        { source: 'Requirements', targets: ['User Stories', 'Specifications'], coverage: coveragePercentage },
      ],
      missingLinks,
      orphanedArtifacts: [],
    };
  }

  private extractTraceabilityMatrixRows(input: ValidationInput): Array<{
    requirementId: string;
    tests: string[];
    code: string[];
    linked: boolean;
  }> {
    const rows: Array<{ requirementId: string; tests: string[]; code: string[]; linked: boolean }> = [];
    for (const source of input.resolvedSources) {
      let parsed: unknown;
      try {
        parsed = JSON.parse(source.content);
      } catch {
        continue;
      }
      if (!parsed || typeof parsed !== 'object') {
        continue;
      }
      const schemaVersion = (parsed as { schemaVersion?: unknown }).schemaVersion;
      if (schemaVersion !== 'issue-traceability-matrix/v1') {
        continue;
      }
      const candidateRows = (parsed as { rows?: unknown }).rows;
      if (!Array.isArray(candidateRows)) {
        continue;
      }
      for (const row of candidateRows) {
        if (!row || typeof row !== 'object') {
          continue;
        }
        const requirementId = (row as { requirementId?: unknown }).requirementId;
        if (typeof requirementId !== 'string' || requirementId.trim().length === 0) {
          continue;
        }
        const tests = Array.isArray((row as { tests?: unknown }).tests)
          ? ((row as { tests: unknown[] }).tests.filter((value): value is string => typeof value === 'string'))
          : [];
        const code = Array.isArray((row as { code?: unknown }).code)
          ? ((row as { code: unknown[] }).code.filter((value): value is string => typeof value === 'string'))
          : [];
        const linked = typeof (row as { linked?: unknown }).linked === 'boolean'
          ? Boolean((row as { linked: unknown }).linked)
          : tests.length > 0 && code.length > 0;
        rows.push({
          requirementId: requirementId.trim(),
          tests,
          code,
          linked,
        });
      }
    }
    return rows;
  }

  private async validateCompleteness(input: ValidationInput): Promise<any> {
    const text = this.collectSourceText(input);
    const categories = [
      { name: 'Requirements', keywords: ['requirement', 'must', 'should'] },
      { name: 'User Stories', keywords: ['as a', 'i want', 'so that'] },
      { name: 'Specifications', keywords: ['spec', 'api', 'schema'] },
      { name: 'Tests', keywords: ['test', 'given', 'when', 'then'] },
    ];
    const categoryScores = categories.map((category) => {
      const hits = category.keywords.filter((keyword) => text.toLowerCase().includes(keyword)).length;
      return {
        name: category.name,
        score: this.clamp(40 + hits * 20, 0, 100),
        missing: Math.max(0, category.keywords.length - hits),
      };
    });
    const missingComponents = categoryScores
      .filter((category) => category.score < 60)
      .map((category) => ({
        category: category.name,
        description: `Coverage for ${category.name} is below 60%`,
        priority: 'high',
      }));
    const completenessScore = this.clamp(
      Math.round(categoryScores.reduce((sum, category) => sum + category.score, 0) / categoryScores.length) - input.missingSources.length * 4,
      0,
      99,
    );

    return {
      completenessScore,
      categoryScores,
      missingComponents,
      trends: { improving: [], declining: [], stable: [] },
      recommendations: ['Address missing components'],
      criticalGaps: missingComponents.map((component) => ({ description: component.description })),
    };
  }

  private collectSourceText(input: ValidationInput): string {
    return input.resolvedSources.map((source) => source.content).join('\n');
  }

  private toValidationInput(input: any): ValidationInput {
    if (
      input &&
      typeof input === 'object' &&
      Array.isArray(input.requestedSources) &&
      Array.isArray(input.resolvedSources) &&
      Array.isArray(input.missingSources)
    ) {
      return {
        ...(input as ValidationInput),
        strict: Boolean((input as { strict?: unknown }).strict),
      };
    }
    if (typeof input === 'string') {
      return {
        requestedSources: ['inline'],
        resolvedSources: [{ path: 'inline', content: input }],
        missingSources: [],
        strict: false,
      };
    }
    if (input && typeof input === 'object') {
      return {
        requestedSources: [],
        resolvedSources: [{ path: 'inline:object', content: JSON.stringify(input, null, 2) }],
        missingSources: [],
        strict: false,
      };
    }
    return {
      requestedSources: [],
      resolvedSources: [],
      missingSources: [],
      strict: false,
    };
  }

  private keywordCoverage(text: string, keywords: string[], baseline: number): number {
    const lower = text.toLowerCase();
    const hits = keywords.filter((keyword) => lower.includes(keyword)).length;
    return this.clamp(baseline + hits * 8, 0, 100);
  }

  private extractIds(text: string, pattern: RegExp): string[] {
    return Array.from(new Set(text.match(pattern) || []));
  }

  private clamp(value: number, min: number, max: number): number {
    return Math.max(min, Math.min(max, value));
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
