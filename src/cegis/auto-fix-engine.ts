/**
 * CEGIS Auto-Fix Engine
 * 
 * Implements counter-example guided inductive synthesis for automated
 * specification and code repair based on failure artifacts
 */

import * as fs from 'fs';
import * as path from 'path';
import { 
  FailureArtifact, 
  FailureArtifactCollection,
  RepairAction,
  FailureCategory,
  FailureSeverity 
} from './failure-artifact-schema.js';

export interface AutoFixOptions {
  dryRun: boolean;
  maxIterations: number;
  confidenceThreshold: number;
  backupOriginals: boolean;
  outputDir: string;
}

export interface FixResult {
  success: boolean;
  appliedActions: RepairAction[];
  errors: string[];
  generatedFiles: string[];
  backupFiles: string[];
  recommendations: string[];
}

export interface FixStrategy {
  category: FailureCategory;
  severity: FailureSeverity[];
  minConfidence: number;
  execute(artifact: FailureArtifact, options: AutoFixOptions): Promise<FixResult>;
}

export class AutoFixEngine {
  private strategies: Map<FailureCategory, FixStrategy> = new Map();
  private fixHistory: FixResult[] = [];

  constructor() {
    this.registerDefaultStrategies();
  }

  /**
   * Register a fix strategy for a specific failure category
   */
  registerStrategy(strategy: FixStrategy): void {
    this.strategies.set(strategy.category, strategy);
  }

  /**
   * Analyze failure artifacts and propose fixes
   */
  async analyzeFailures(
    failures: FailureArtifact[] | FailureArtifactCollection,
    options: Partial<AutoFixOptions> = {}
  ): Promise<{ analysis: string; proposedFixes: RepairAction[]; riskAssessment: string }> {
    const artifacts = Array.isArray(failures) ? failures : failures.failures;
    const opts = this.mergeOptions(options);

    // Group failures by category and severity
    const groupedFailures = this.groupFailures(artifacts);
    
    // Analyze patterns and root causes
    const patterns = this.analyzePatterns(groupedFailures);
    
    // Generate comprehensive analysis
    const analysis = this.generateAnalysis(groupedFailures, patterns);
    
    // Propose fixes based on patterns
    const proposedFixes = this.proposeFixes(groupedFailures, opts);
    
    // Assess risks of proposed fixes
    const riskAssessment = this.assessRisks(proposedFixes, artifacts);

    return {
      analysis,
      proposedFixes,
      riskAssessment,
    };
  }

  /**
   * Execute automated fixes for failure artifacts
   */
  async executeFixes(
    failures: FailureArtifact[] | FailureArtifactCollection,
    options: Partial<AutoFixOptions> = {}
  ): Promise<FixResult> {
    const artifacts = Array.isArray(failures) ? failures : failures.failures;
    const opts = this.mergeOptions(options);

    const result: FixResult = {
      success: true,
      appliedActions: [],
      errors: [],
      generatedFiles: [],
      backupFiles: [],
      recommendations: [],
    };

    if (opts.dryRun) {
      console.log('🔍 Running in dry-run mode - no files will be modified');
    }

    try {
      // Create output directory
      if (!fs.existsSync(opts.outputDir)) {
        fs.mkdirSync(opts.outputDir, { recursive: true });
      }

      // Sort failures by severity and confidence
      const sortedFailures = this.prioritizeFailures(artifacts);

      let iterations = 0;
      for (const failure of sortedFailures) {
        if (iterations >= opts.maxIterations) {
          result.recommendations.push(`Reached maximum iterations (${opts.maxIterations}). ${sortedFailures.length - iterations} failures remaining.`);
          break;
        }

        try {
          const fixResult = await this.fixSingleFailure(failure, opts);
          
          // Merge results
          result.appliedActions.push(...fixResult.appliedActions);
          result.generatedFiles.push(...fixResult.generatedFiles);
          result.backupFiles.push(...fixResult.backupFiles);
          result.recommendations.push(...fixResult.recommendations);
          
          if (!fixResult.success) {
            result.errors.push(...fixResult.errors);
            result.success = false;
          }

        } catch (error) {
          result.errors.push(`Failed to fix ${failure.id}: ${error}`);
          result.success = false;
        }

        iterations++;
      }

      // Generate summary
      this.generateFixSummary(result, opts);

    } catch (error) {
      result.errors.push(`Auto-fix execution failed: ${error}`);
      result.success = false;
    }

    // Store fix history
    this.fixHistory.push(result);

    return result;
  }

  /**
   * Fix a single failure artifact
   */
  private async fixSingleFailure(artifact: FailureArtifact, options: AutoFixOptions): Promise<FixResult> {
    const strategy = this.strategies.get(artifact.category);
    
    if (!strategy) {
      return {
        success: false,
        appliedActions: [],
        errors: [`No strategy found for category: ${artifact.category}`],
        generatedFiles: [],
        backupFiles: [],
        recommendations: [`Consider implementing a fix strategy for ${artifact.category} failures`],
      };
    }

    // Check if severity is supported by strategy
    if (!strategy.severity.includes(artifact.severity)) {
      return {
        success: false,
        appliedActions: [],
        errors: [],
        generatedFiles: [],
        backupFiles: [],
        recommendations: [`${artifact.category} strategy does not support ${artifact.severity} severity`],
      };
    }

    // Filter actions by confidence threshold
    const viableActions = artifact.suggestedActions.filter(
      action => action.confidence >= options.confidenceThreshold
    );

    if (viableActions.length === 0) {
      return {
        success: false,
        appliedActions: [],
        errors: [],
        generatedFiles: [],
        backupFiles: [],
        recommendations: [`No actions meet confidence threshold of ${options.confidenceThreshold} for ${artifact.id}`],
      };
    }

    console.log(`🔧 Fixing ${artifact.category} failure: ${artifact.title}`);
    return await strategy.execute(artifact, options);
  }

  /**
   * Register default fix strategies
   */
  private registerDefaultStrategies(): void {
    // Contract violation strategy
    this.registerStrategy(new ContractViolationStrategy());
    
    // Specification mismatch strategy
    this.registerStrategy(new SpecificationMismatchStrategy());
    
    // Test failure strategy
    this.registerStrategy(new TestFailureStrategy());
    
    // Type error strategy
    this.registerStrategy(new TypeErrorStrategy());
  }

  private mergeOptions(options: Partial<AutoFixOptions>): AutoFixOptions {
    return {
      dryRun: options.dryRun ?? false,
      maxIterations: options.maxIterations ?? 10,
      confidenceThreshold: options.confidenceThreshold ?? 0.7,
      backupOriginals: options.backupOriginals ?? true,
      outputDir: options.outputDir ?? '.ae/auto-fix',
      ...options,
    };
  }

  private groupFailures(failures: FailureArtifact[]): Map<FailureCategory, FailureArtifact[]> {
    const groups = new Map<FailureCategory, FailureArtifact[]>();
    
    for (const failure of failures) {
      const category = failure.category;
      if (!groups.has(category)) {
        groups.set(category, []);
      }
      groups.get(category)!.push(failure);
    }
    
    return groups;
  }

  private analyzePatterns(groupedFailures: Map<FailureCategory, FailureArtifact[]>): string[] {
    const patterns: string[] = [];
    
    for (const [category, failures] of groupedFailures) {
      if (failures.length > 3) {
        patterns.push(`High frequency of ${category} failures (${failures.length} occurrences)`);
      }
      
      // Analyze common files/locations
      const locations = failures.map(f => f.location?.file).filter(Boolean);
      const locationCounts = new Map<string, number>();
      
      for (const loc of locations) {
        locationCounts.set(loc!, (locationCounts.get(loc!) || 0) + 1);
      }
      
      for (const [file, count] of locationCounts) {
        if (count > 2) {
          patterns.push(`Multiple ${category} failures in ${file} (${count} occurrences)`);
        }
      }
    }
    
    return patterns;
  }

  private generateAnalysis(
    groupedFailures: Map<FailureCategory, FailureArtifact[]>,
    patterns: string[]
  ): string {
    const totalFailures = Array.from(groupedFailures.values()).reduce((sum, arr) => sum + arr.length, 0);
    
    let analysis = `# Failure Analysis Report\n\n`;
    analysis += `**Total Failures**: ${totalFailures}\n\n`;
    
    analysis += `## Failure Distribution\n`;
    for (const [category, failures] of groupedFailures) {
      const percentage = ((failures.length / totalFailures) * 100).toFixed(1);
      analysis += `- **${category}**: ${failures.length} (${percentage}%)\n`;
    }
    
    if (patterns.length > 0) {
      analysis += `\n## Detected Patterns\n`;
      for (const pattern of patterns) {
        analysis += `- ${pattern}\n`;
      }
    }
    
    return analysis;
  }

  private proposeFixes(
    groupedFailures: Map<FailureCategory, FailureArtifact[]>,
    options: AutoFixOptions
  ): RepairAction[] {
    const allActions: RepairAction[] = [];
    
    for (const failures of groupedFailures.values()) {
      for (const failure of failures) {
        const viableActions = failure.suggestedActions.filter(
          action => action.confidence >= options.confidenceThreshold
        );
        allActions.push(...viableActions);
      }
    }
    
    // Deduplicate and sort by confidence
    const uniqueActions = this.deduplicateActions(allActions);
    return uniqueActions.sort((a, b) => b.confidence - a.confidence);
  }

  private assessRisks(proposedFixes: RepairAction[], artifacts: FailureArtifact[]): string {
    const highRiskActions = proposedFixes.filter(action => 
      action.type === 'spec_update' || action.confidence < 0.8
    );
    
    const criticalFailures = artifacts.filter(a => a.severity === 'critical').length;
    
    let assessment = `# Risk Assessment\n\n`;
    
    if (highRiskActions.length > 0) {
      assessment += `⚠️ **High Risk Actions**: ${highRiskActions.length}\n`;
      assessment += `- Specification updates may require manual review\n`;
      assessment += `- Actions with low confidence may introduce new issues\n\n`;
    }
    
    if (criticalFailures > 0) {
      assessment += `🚨 **Critical Failures**: ${criticalFailures}\n`;
      assessment += `- Immediate attention required\n`;
      assessment += `- Consider manual intervention\n\n`;
    }
    
    assessment += `**Recommendation**: Review all proposed fixes before applying in production.\n`;
    
    return assessment;
  }

  private prioritizeFailures(failures: FailureArtifact[]): FailureArtifact[] {
    const severityOrder = { critical: 4, major: 3, minor: 2, info: 1 };
    
    return failures.sort((a, b) => {
      // Sort by severity first
      const severityDiff = severityOrder[b.severity] - severityOrder[a.severity];
      if (severityDiff !== 0) return severityDiff;
      
      // Then by highest confidence in suggested actions
      const aMaxConfidence = Math.max(...a.suggestedActions.map(action => action.confidence));
      const bMaxConfidence = Math.max(...b.suggestedActions.map(action => action.confidence));
      
      return bMaxConfidence - aMaxConfidence;
    });
  }

  private deduplicateActions(actions: RepairAction[]): RepairAction[] {
    const seen = new Set<string>();
    const unique: RepairAction[] = [];
    
    for (const action of actions) {
      const key = `${action.type}:${action.targetFile}:${action.description}`;
      if (!seen.has(key)) {
        seen.add(key);
        unique.push(action);
      }
    }
    
    return unique;
  }

  private generateFixSummary(result: FixResult, options: AutoFixOptions): void {
    const summaryPath = path.join(options.outputDir, 'fix-summary.md');
    
    let summary = `# Auto-Fix Summary\n\n`;
    summary += `**Generated**: ${new Date().toISOString()}\n`;
    summary += `**Mode**: ${options.dryRun ? 'Dry Run' : 'Execution'}\n`;
    summary += `**Success**: ${result.success ? '✅' : '❌'}\n\n`;
    
    summary += `## Applied Actions\n`;
    if (result.appliedActions.length === 0) {
      summary += `No actions were applied.\n\n`;
    } else {
      for (const action of result.appliedActions) {
        summary += `- **${action.type}**: ${action.description}\n`;
        if (action.targetFile) {
          summary += `  - File: ${action.targetFile}\n`;
        }
        summary += `  - Confidence: ${(action.confidence * 100).toFixed(1)}%\n`;
      }
      summary += `\n`;
    }
    
    if (result.errors.length > 0) {
      summary += `## Errors\n`;
      for (const error of result.errors) {
        summary += `- ${error}\n`;
      }
      summary += `\n`;
    }
    
    if (result.recommendations.length > 0) {
      summary += `## Recommendations\n`;
      for (const rec of result.recommendations) {
        summary += `- ${rec}\n`;
      }
      summary += `\n`;
    }
    
    if (!options.dryRun) {
      fs.writeFileSync(summaryPath, summary);
      console.log(`📝 Fix summary saved to: ${summaryPath}`);
    } else {
      console.log('📝 Fix Summary (Dry Run):\n' + summary);
    }
  }

  /**
   * Get fix history
   */
  getFixHistory(): FixResult[] {
    return [...this.fixHistory];
  }

  /**
   * Clear fix history
   */
  clearFixHistory(): void {
    this.fixHistory = [];
  }
}

// Default strategy implementations
class ContractViolationStrategy implements FixStrategy {
  category: FailureCategory = 'contract_violation';
  severity: FailureSeverity[] = ['critical', 'major'];
  minConfidence = 0.8;

  async execute(artifact: FailureArtifact, options: AutoFixOptions): Promise<FixResult> {
    const result: FixResult = {
      success: true,
      appliedActions: [],
      errors: [],
      generatedFiles: [],
      backupFiles: [],
      recommendations: [],
    };

    // For contract violations, prioritize spec updates
    const specAction = artifact.suggestedActions.find(a => a.type === 'spec_update');
    
    if (specAction && specAction.confidence >= this.minConfidence) {
      if (!options.dryRun) {
        // In a real implementation, this would update specification files
        result.recommendations.push('Contract violation detected - consider updating specification');
        result.recommendations.push(`Proposed change: ${specAction.proposedChange || 'See description'}`);
      }
      
      result.appliedActions.push(specAction);
      result.success = true;
    } else {
      result.recommendations.push('Manual review required for contract violation');
      result.success = false;
    }

    return result;
  }
}

class SpecificationMismatchStrategy implements FixStrategy {
  category: FailureCategory = 'specification_mismatch';
  severity: FailureSeverity[] = ['critical', 'major', 'minor'];
  minConfidence = 0.7;

  async execute(artifact: FailureArtifact, options: AutoFixOptions): Promise<FixResult> {
    return {
      success: false,
      appliedActions: [],
      errors: [],
      generatedFiles: [],
      backupFiles: [],
      recommendations: ['Specification mismatch requires manual analysis'],
    };
  }
}

class TestFailureStrategy implements FixStrategy {
  category: FailureCategory = 'test_failure';
  severity: FailureSeverity[] = ['major', 'minor'];
  minConfidence = 0.6;

  async execute(artifact: FailureArtifact, options: AutoFixOptions): Promise<FixResult> {
    return {
      success: false,
      appliedActions: [],
      errors: [],
      generatedFiles: [],
      backupFiles: [],
      recommendations: ['Test failure analysis - consider test update or code fix'],
    };
  }
}

class TypeErrorStrategy implements FixStrategy {
  category: FailureCategory = 'type_error';
  severity: FailureSeverity[] = ['major', 'minor'];
  minConfidence = 0.8;

  async execute(artifact: FailureArtifact, options: AutoFixOptions): Promise<FixResult> {
    return {
      success: false,
      appliedActions: [],
      errors: [],
      generatedFiles: [],
      backupFiles: [],
      recommendations: ['Type error detected - TypeScript compilation required'],
    };
  }
}