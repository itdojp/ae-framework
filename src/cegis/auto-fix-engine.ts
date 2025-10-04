/**
 * Auto-Fix Engine
 * Phase 2.1: Core engine for analyzing failures and applying automated fixes
 */

import type {
  FailureArtifact,
  FixStrategy,
  FixResult,
  AppliedFix,
  SkippedFix,
  AutoFixConfig,
  AutoFixOptions,
  FailurePattern,
  FailureCategory,
  RepairAction
} from './types.js';

export type { AutoFixOptions };
import { RiskAssessmentService } from './risk-assessment-service.js';
import { TypeErrorFixStrategy } from './strategies/type-error-strategy.js';
import { TestFailureFixStrategy } from './strategies/test-failure-strategy.js';
import { ContractViolationFixStrategy } from './strategies/contract-violation-strategy.js';

export class AutoFixEngine {
  private strategies: Map<FailureCategory, FixStrategy[]> = new Map();
  private riskAssessment: RiskAssessmentService;
  private config: AutoFixConfig;

  constructor(
    config: Partial<AutoFixConfig> = {},
    riskAssessment?: RiskAssessmentService
  ) {
    this.config = {
      dryRun: false,
      confidenceThreshold: 0.7,
      maxRiskLevel: 3,
      enabledCategories: [
        'type_error',
        'test_failure',
        'contract_violation',
        'lint_error',
        'build_error'
      ],
      maxFixesPerRun: 10,
      timeoutMs: 30000,
      backupFiles: true,
      generateReport: true,
      ...config
    };

    this.riskAssessment = riskAssessment || new RiskAssessmentService();
    this.initializeDefaultStrategies();
  }

  /**
   * Execute automatic fixes for the given failure artifacts
   */
  async executeFixes(
    failures: FailureArtifact[],
    options: AutoFixOptions = {}
  ): Promise<FixResult> {
    const startTime = Date.now();
    const effectiveConfig = { ...this.config, ...options };
    
    console.log(`🔧 Starting auto-fix process for ${failures.length} failures...`);
    
    try {
      // 1. Filter and validate failures
      const validFailures = this.filterValidFailures(failures, effectiveConfig);
      console.log(`📋 Processing ${validFailures.length} valid failures`);
      
      // 2. Analyze failure patterns
      const patterns = this.analyzeFailurePatterns(validFailures);
      console.log(`🔍 Identified ${patterns.length} failure patterns`);
      
      // 3. Select and prioritize strategies
      const strategies = await this.selectStrategies(validFailures);
      console.log(`⚙️  Selected ${strategies.length} fix strategies`);
      
      // 4. Execute fixes
      const { appliedFixes, skippedFixes } = await this.applyFixes(
        strategies,
        validFailures,
        effectiveConfig
      );
      
      // 5. Generate summary and recommendations
      const summary = this.generateSummary(validFailures, appliedFixes, skippedFixes);
      const recommendations = this.generateRecommendations(
        validFailures,
        appliedFixes,
        patterns
      );
      
      // 6. Generate report if requested
      let reportPath: string | undefined;
      if (effectiveConfig.generateReport) {
        reportPath = await this.generateReport(
          validFailures,
          appliedFixes,
          skippedFixes,
          summary,
          recommendations
        );
      }
      
      const duration = Date.now() - startTime;
      console.log(`✅ Auto-fix completed in ${duration}ms`);
      console.log(`📊 Applied: ${appliedFixes.length}, Skipped: ${skippedFixes.length}`);
      
      return {
        success: appliedFixes.length > 0,
        appliedActions: appliedFixes,
        generatedFiles: appliedFixes.map(fix => fix.targetFile || '').filter(Boolean),
        backupFiles: [], // No backup files generated in this implementation
        appliedFixes,
        skippedFixes,
        summary,
        recommendations,
        ...(reportPath ? { reportPath } : {}),
        errors: [] // No errors if we reach this point
      };
      
    } catch (error) {
      console.error('❌ Auto-fix process failed:', error);
      throw error;
    }
  }

  /**
   * Add a custom fix strategy
   */
  addStrategy(strategy: FixStrategy): void {
    if (!this.strategies.has(strategy.category)) {
      this.strategies.set(strategy.category, []);
    }
    this.strategies.get(strategy.category)!.push(strategy);
  }

  /**
   * Get available strategies for a category
   */
  getStrategies(category: FailureCategory): FixStrategy[] {
    return this.strategies.get(category) || [];
  }

  /**
   * Analyze failure patterns to identify common issues
   */
  analyzeFailurePatterns(failures: FailureArtifact[]): FailurePattern[] {
    const patterns: FailurePattern[] = [];
    const categoryGroups = this.groupByCategory(failures);
    
    for (const [category, categoryFailures] of categoryGroups) {
      // Analyze common error messages
      const errorMessages = categoryFailures
        .map(f => f.evidence.errorMessage)
        .filter(Boolean) as string[];
      
      const messagePatterns = this.findCommonPatterns(errorMessages);
      
      for (const pattern of messagePatterns) {
        patterns.push({
          pattern: pattern.text,
          frequency: pattern.count,
          categories: [category],
          commonLocations: categoryFailures
            .filter(f => f.location)
            .map(f => f.location!),
          suggestedStrategies: this.getSuggestedStrategies(category, pattern.text),
          confidence: this.calculatePatternConfidence(pattern.count, categoryFailures.length)
        });
      }
    }
    
    return patterns.sort((a, b) => b.frequency - a.frequency);
  }

  private initializeDefaultStrategies(): void {
    // Type error strategies
    this.strategies.set('type_error', [
      new TypeErrorFixStrategy()
    ]);
    
    // Test failure strategies
    this.strategies.set('test_failure', [
      new TestFailureFixStrategy()
    ]);
    
    // Contract violation strategies
    this.strategies.set('contract_violation', [
      new ContractViolationFixStrategy()
    ]);
    
    // Add more strategies as needed
  }

  private filterValidFailures(
    failures: FailureArtifact[],
    config: AutoFixConfig
  ): FailureArtifact[] {
    return failures.filter(failure => {
      // Check if category is enabled
      if (!config.enabledCategories.includes(failure.category)) {
        return false;
      }
      
      // Check if we have necessary information
      if (!failure.location?.filePath) {
        return false;
      }
      
      // Check severity
      if (failure.severity === 'info' && config.maxRiskLevel < 2) {
        return false;
      }
      
      return true;
    });
  }

  private async selectStrategies(
    failures: FailureArtifact[]
  ): Promise<{ strategy: FixStrategy; failures: FailureArtifact[] }[]> {
    const strategyGroups: { strategy: FixStrategy; failures: FailureArtifact[] }[] = [];
    
    for (const failure of failures) {
      const categoryStrategies = this.strategies.get(failure.category) || [];
      
      for (const strategy of categoryStrategies) {
        if (await strategy.canApply(failure)) {
          const existingGroup = strategyGroups.find(g => g.strategy.name === strategy.name);
          if (existingGroup) {
            existingGroup.failures.push(failure);
          } else {
            strategyGroups.push({
              strategy,
              failures: [failure]
            });
          }
        }
      }
    }
    
    // Sort by strategy confidence and failure count
    return strategyGroups.sort((a, b) => {
      const scoreA = a.strategy.confidence * a.failures.length;
      const scoreB = b.strategy.confidence * b.failures.length;
      return scoreB - scoreA;
    });
  }

  private async applyFixes(
    strategyGroups: { strategy: FixStrategy; failures: FailureArtifact[] }[],
    allFailures: FailureArtifact[],
    config: AutoFixConfig
  ): Promise<{ appliedFixes: AppliedFix[]; skippedFixes: SkippedFix[] }> {
    const appliedFixes: AppliedFix[] = [];
    const skippedFixes: SkippedFix[] = [];
    const processedFiles = new Set<string>();
    
    let fixCount = 0;
    
    for (const { strategy, failures } of strategyGroups) {
      if (fixCount >= config.maxFixesPerRun) {
        skippedFixes.push({
          strategy: strategy.name,
          reason: 'Maximum fixes per run reached',
          confidence: strategy.confidence,
          riskLevel: strategy.riskLevel
        });
        continue;
      }
      
      // Check strategy confidence
      if (strategy.confidence < config.confidenceThreshold) {
        skippedFixes.push({
          strategy: strategy.name,
          reason: 'Low confidence',
          confidence: strategy.confidence,
          riskLevel: strategy.riskLevel
        });
        continue;
      }
      
      // Check risk level
      if (strategy.riskLevel > config.maxRiskLevel) {
        skippedFixes.push({
          strategy: strategy.name,
          reason: 'High risk level',
          confidence: strategy.confidence,
          riskLevel: strategy.riskLevel
        });
        continue;
      }
      
      try {
        console.log(`🔧 Applying strategy: ${strategy.name} to ${failures.length} failures`);
        
        const fix = await this.applySingleStrategy(
          strategy,
          failures,
          config,
          processedFiles
        );
        
        if (fix) {
          appliedFixes.push(fix);
          fixCount++;
          
          // Track processed files to avoid conflicts
          fix.filesModified.forEach(file => processedFiles.add(file));
        }
        
      } catch (error) {
        skippedFixes.push({
          strategy: strategy.name,
          reason: 'Execution failed',
          error: error instanceof Error ? error.message : 'Unknown error',
          confidence: strategy.confidence,
          riskLevel: strategy.riskLevel
        });
      }
    }
    
    return { appliedFixes, skippedFixes };
  }

  private async applySingleStrategy(
    strategy: FixStrategy,
    failures: FailureArtifact[],
    config: AutoFixConfig,
    processedFiles: Set<string>
  ): Promise<AppliedFix | null> {
    const startTime = Date.now();
    const filesModified: string[] = [];
    const errors: string[] = [];
    const warnings: string[] = [];
    const allActions: RepairAction[] = [];
    
    for (const failure of failures) {
      // Skip if file already processed
      if (failure.location?.filePath && processedFiles.has(failure.location.filePath)) {
        warnings.push(`File already processed: ${failure.location.filePath}`);
        continue;
      }
      
      const actions = await strategy.generateFix(failure);
      allActions.push(...actions);
      
      for (const action of actions) {
        try {
          if (action.filePath && !config.dryRun) {
            // Backup file if requested
            if (config.backupFiles) {
              await this.backupFile(action.filePath);
            }
            
            // Apply the fix
            await this.applyAction(action);
            
            if (action.filePath && !filesModified.includes(action.filePath)) {
              filesModified.push(action.filePath);
            }
          }
        } catch (error) {
          errors.push(`Failed to apply action: ${error instanceof Error ? error.message : 'Unknown error'}`);
        }
      }
    }
    
    const duration = Date.now() - startTime;
    
    return {
      strategy: strategy.name,
      actions: allActions,
      success: errors.length === 0,
      filesModified,
      errors,
      warnings,
      metadata: {
        timestamp: new Date().toISOString(),
        duration,
        confidence: strategy.confidence,
        riskLevel: strategy.riskLevel
      }
    };
  }

  private async applyAction(action: RepairAction): Promise<void> {
    if (action.type === 'code_change' && action.codeChange && action.filePath) {
      const fs = await import('fs');
      const content = await fs.promises.readFile(action.filePath, 'utf-8');
      const lines = content.split('\n');
      
      // Replace the specified lines
      const startIdx = action.codeChange.startLine - 1;
      const endIdx = action.codeChange.endLine;
      
      lines.splice(startIdx, endIdx - startIdx, action.codeChange.newCode);
      
      await fs.promises.writeFile(action.filePath, lines.join('\n'));
    }
    
    // Handle other action types as needed
  }

  private async backupFile(filePath: string): Promise<void> {
    const fs = await import('fs');

    const backupPath = `${filePath}.backup.${Date.now()}`;
    await fs.promises.copyFile(filePath, backupPath);
  }

  private groupByCategory(failures: FailureArtifact[]): Map<FailureCategory, FailureArtifact[]> {
    const groups = new Map<FailureCategory, FailureArtifact[]>();
    
    for (const failure of failures) {
      if (!groups.has(failure.category)) {
        groups.set(failure.category, []);
      }
      groups.get(failure.category)!.push(failure);
    }
    
    return groups;
  }

  private findCommonPatterns(messages: string[]): { text: string; count: number }[] {
    const patterns: Map<string, number> = new Map();
    
    for (const message of messages) {
      // Extract common error patterns
      const normalizedMessage = message.replace(/['"`][^'"`]*['"`]/g, 'STRING')
                                      .replace(/\d+/g, 'NUMBER')
                                      .replace(/\w+\(\)/g, 'FUNCTION()');
      
      patterns.set(normalizedMessage, (patterns.get(normalizedMessage) || 0) + 1);
    }
    
    return Array.from(patterns.entries())
      .map(([text, count]) => ({ text, count }))
      .filter(p => p.count > 1)
      .sort((a, b) => b.count - a.count);
  }

  private getSuggestedStrategies(category: FailureCategory, pattern: string): string[] {
    const strategies = this.strategies.get(category) || [];
    return strategies.map(s => s.name);
  }

  private calculatePatternConfidence(occurrences: number, total: number): number {
    return Math.min(occurrences / total, 0.9);
  }

  private generateSummary(
    failures: FailureArtifact[],
    appliedFixes: AppliedFix[],
    skippedFixes: SkippedFix[]
  ): FixResult['summary'] {
    const filesModified = new Set<string>();
    const errors: string[] = [];
    const warnings: string[] = [];
    
    for (const fix of appliedFixes) {
      fix.filesModified.forEach(file => filesModified.add(file));
      errors.push(...fix.errors);
      warnings.push(...fix.warnings);
    }
    
    return {
      totalFailures: failures.length,
      fixesApplied: appliedFixes.length,
      fixesSkipped: skippedFixes.length,
      filesModified: filesModified.size,
      success: errors.length === 0,
      errors,
      warnings
    };
  }

  private generateRecommendations(
    failures: FailureArtifact[],
    appliedFixes: AppliedFix[],
    patterns: FailurePattern[]
  ): string[] {
    const recommendations: string[] = [];
    
    // Pattern-based recommendations
    for (const pattern of patterns.slice(0, 3)) {
      if (pattern.frequency > 2) {
        recommendations.push(
          `Consider reviewing the recurring pattern: "${pattern.pattern}" (${pattern.frequency} occurrences)`
        );
      }
    }
    
    // Category-based recommendations
    const categoryGroups = this.groupByCategory(failures);
    for (const [category, categoryFailures] of categoryGroups) {
      if (categoryFailures.length > 3) {
        recommendations.push(
          `High frequency of ${category} errors (${categoryFailures.length}). Consider improving ${category} practices.`
        );
      }
    }
    
    // Success rate recommendations
    const successRate = appliedFixes.length === 0 ? 0 : appliedFixes.filter(f => f.success).length / appliedFixes.length;
    if (appliedFixes.length > 0 && successRate < 0.8) {
      recommendations.push(
        'Low fix success rate. Consider manual review of failed fixes.'
      );
    }

    return recommendations;
  }

  private async generateReport(
    failures: FailureArtifact[],
    appliedFixes: AppliedFix[],
    skippedFixes: SkippedFix[],
    summary: FixResult['summary'],
    recommendations: string[]
  ): Promise<string> {
    const reportPath = `cegis-report-${Date.now()}.json`;
    
    const report = {
      timestamp: new Date().toISOString(),
      summary,
      failures: failures.length,
      appliedFixes: appliedFixes.map(f => ({
        strategy: f.strategy,
        success: f.success,
        filesModified: f.filesModified,
        metadata: f.metadata
      })),
      skippedFixes,
      recommendations,
      patterns: this.analyzeFailurePatterns(failures)
    };
    
    const fs = await import('fs');
    await fs.promises.writeFile(reportPath, JSON.stringify(report, null, 2));
    
    return reportPath;
  }
}
