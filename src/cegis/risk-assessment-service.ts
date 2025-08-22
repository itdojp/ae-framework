/**
 * Risk Assessment Service
 * Phase 2.1: Evaluates risks associated with automated fixes
 */

import { FixStrategy, RepairAction, RiskAssessment, FailureArtifact } from './types.js';

export class RiskAssessmentService {
  
  /**
   * Assess the risk level of applying a fix strategy
   */
  async assess(strategy: FixStrategy): Promise<number> {
    let riskScore = strategy.riskLevel;
    
    // Adjust risk based on strategy characteristics
    if (strategy.category === 'contract_violation') {
      riskScore += 1; // Contract changes are inherently risky
    }
    
    if (strategy.confidence < 0.7) {
      riskScore += 1; // Low confidence increases risk
    }
    
    if (strategy.category === 'test_failure' && strategy.confidence > 0.8) {
      riskScore -= 1; // High-confidence test fixes are safer
    }
    
    return Math.min(Math.max(riskScore, 1), 5);
  }

  /**
   * Assess risk of a specific repair action
   */
  async assessAction(action: RepairAction): Promise<RiskAssessment> {
    const baseRisk = action.riskLevel;
    const factors: string[] = [];
    const mitigation: string[] = [];
    
    // Risk factors
    if (action.type === 'code_change') {
      if (action.filePath?.includes('test')) {
        factors.push('Test file modification - lower impact');
      } else {
        factors.push('Production code modification');
      }
    }
    
    if (action.type === 'dependency_update') {
      factors.push('Dependency changes can have wide-reaching effects');
      mitigation.push('Test thoroughly after dependency updates');
    }
    
    if (action.confidence < 0.7) {
      factors.push('Low confidence in automated fix');
      mitigation.push('Manual review recommended');
    }
    
    if (action.type === 'validation_update') {
      factors.push('Schema/validation changes affect data contracts');
      mitigation.push('Verify backward compatibility');
    }
    
    // Mitigation strategies
    mitigation.push('Create backup before applying changes');
    
    if (baseRisk > 3) {
      mitigation.push('Apply in non-production environment first');
      mitigation.push('Have rollback plan ready');
    }
    
    // Determine recommendation
    let recommendation: 'proceed' | 'caution' | 'abort';
    
    if (baseRisk <= 2 && action.confidence >= 0.8) {
      recommendation = 'proceed';
    } else if (baseRisk <= 3 && action.confidence >= 0.6) {
      recommendation = 'caution';
    } else {
      recommendation = 'abort';
    }
    
    return {
      level: baseRisk,
      factors,
      mitigation,
      recommendation
    };
  }

  /**
   * Assess cumulative risk of multiple actions
   */
  async assessBatch(actions: RepairAction[]): Promise<RiskAssessment> {
    if (actions.length === 0) {
      return {
        level: 1,
        factors: [],
        mitigation: [],
        recommendation: 'proceed'
      };
    }
    
    const assessments = await Promise.all(
      actions.map(action => this.assessAction(action))
    );
    
    // Calculate cumulative risk
    const maxRisk = Math.max(...assessments.map(a => a.level));
    const avgRisk = assessments.reduce((sum, a) => sum + a.level, 0) / assessments.length;
    const cumulativeRisk = Math.ceil((maxRisk + avgRisk) / 2);
    
    // Aggregate factors and mitigation
    const allFactors = assessments.flatMap(a => a.factors);
    const allMitigation = assessments.flatMap(a => a.mitigation);
    
    // Deduplicate
    const uniqueFactors = [...new Set(allFactors)];
    const uniqueMitigation = [...new Set(allMitigation)];
    
    // Add batch-specific factors
    if (actions.length > 5) {
      uniqueFactors.push(`High number of simultaneous changes (${actions.length})`);
      uniqueMitigation.push('Consider applying changes in smaller batches');
    }
    
    // Files affected
    const affectedFiles = new Set(actions.map(a => a.filePath).filter(Boolean));
    if (affectedFiles.size > 3) {
      uniqueFactors.push(`Multiple files affected (${affectedFiles.size})`);
      uniqueMitigation.push('Review all affected files for potential interactions');
    }
    
    // Determine batch recommendation
    let recommendation: 'proceed' | 'caution' | 'abort';
    
    if (cumulativeRisk <= 2) {
      recommendation = 'proceed';
    } else if (cumulativeRisk <= 3) {
      recommendation = 'caution';
    } else {
      recommendation = 'abort';
    }
    
    return {
      level: cumulativeRisk,
      factors: uniqueFactors,
      mitigation: uniqueMitigation,
      recommendation
    };
  }

  /**
   * Generate risk report for a set of failures and proposed fixes
   */
  async generateRiskReport(
    failures: FailureArtifact[],
    proposedActions: RepairAction[]
  ): Promise<string> {
    const batchAssessment = await this.assessBatch(proposedActions);
    
    let report = '# Risk Assessment Report\n\n';
    report += `**Overall Risk Level**: ${batchAssessment.level}/5\n`;
    report += `**Recommendation**: ${batchAssessment.recommendation.toUpperCase()}\n\n`;
    
    // Risk factors
    if (batchAssessment.factors.length > 0) {
      report += '## Risk Factors\n';
      for (const factor of batchAssessment.factors) {
        report += `- ${factor}\n`;
      }
      report += '\n';
    }
    
    // Mitigation strategies
    if (batchAssessment.mitigation.length > 0) {
      report += '## Mitigation Strategies\n';
      for (const strategy of batchAssessment.mitigation) {
        report += `- ${strategy}\n`;
      }
      report += '\n';
    }
    
    // Breakdown by action type
    const actionsByType = this.groupActionsByType(proposedActions);
    if (Object.keys(actionsByType).length > 0) {
      report += '## Actions by Type\n';
      for (const [type, actions] of Object.entries(actionsByType)) {
        const avgConfidence = actions.reduce((sum, a) => sum + a.confidence, 0) / actions.length;
        const avgRisk = actions.reduce((sum, a) => sum + a.riskLevel, 0) / actions.length;
        
        report += `- **${type}**: ${actions.length} actions\n`;
        report += `  - Average Confidence: ${(avgConfidence * 100).toFixed(1)}%\n`;
        report += `  - Average Risk: ${avgRisk.toFixed(1)}/5\n`;
      }
      report += '\n';
    }
    
    // High-risk actions
    const highRiskActions = proposedActions.filter(a => a.riskLevel >= 4);
    if (highRiskActions.length > 0) {
      report += '## High-Risk Actions (Risk Level ≥ 4)\n';
      for (const action of highRiskActions) {
        report += `- **${action.type}**: ${action.description}\n`;
        report += `  - File: ${action.filePath || 'N/A'}\n`;
        report += `  - Confidence: ${(action.confidence * 100).toFixed(1)}%\n`;
        report += `  - Risk Level: ${action.riskLevel}/5\n`;
      }
      report += '\n';
    }
    
    // Recommendations based on overall risk
    report += '## Recommendations\n';
    
    switch (batchAssessment.recommendation) {
      case 'proceed':
        report += '✅ **PROCEED**: Risk level is acceptable for automated execution.\n';
        report += '- Monitor execution closely\n';
        report += '- Have rollback plan ready\n';
        break;
        
      case 'caution':
        report += '⚠️ **PROCEED WITH CAUTION**: Moderate risk level detected.\n';
        report += '- Manual review recommended before execution\n';
        report += '- Apply changes in non-production environment first\n';
        report += '- Consider applying changes in smaller batches\n';
        break;
        
      case 'abort':
        report += '🛑 **DO NOT PROCEED**: High risk level detected.\n';
        report += '- Manual intervention required\n';
        report += '- Review high-risk actions individually\n';
        report += '- Consider alternative approaches\n';
        break;
    }
    
    return report;
  }

  /**
   * Check if a combination of actions creates additional risks
   */
  private checkInteractionRisks(actions: RepairAction[]): string[] {
    const risks: string[] = [];
    
    // Check for conflicting changes to the same file
    const fileGroups = new Map<string, RepairAction[]>();
    for (const action of actions) {
      if (action.filePath) {
        if (!fileGroups.has(action.filePath)) {
          fileGroups.set(action.filePath, []);
        }
        fileGroups.get(action.filePath)!.push(action);
      }
    }
    
    for (const [filePath, fileActions] of fileGroups) {
      if (fileActions.length > 1) {
        risks.push(`Multiple changes to ${filePath} may conflict`);
      }
    }
    
    // Check for dependency-related risks
    const dependencyActions = actions.filter(a => a.type === 'dependency_update');
    if (dependencyActions.length > 1) {
      risks.push('Multiple dependency updates may cause version conflicts');
    }
    
    // Check for schema/validation conflicts
    const schemaActions = actions.filter(a => 
      a.type === 'validation_update'
    );
    if (schemaActions.length > 1) {
      risks.push('Multiple schema changes may break data contracts');
    }
    
    return risks;
  }

  private groupActionsByType(actions: RepairAction[]): Record<string, RepairAction[]> {
    const groups: Record<string, RepairAction[]> = {};
    
    for (const action of actions) {
      if (!groups[action.type]) {
        groups[action.type] = [];
      }
      groups[action.type].push(action);
    }
    
    return groups;
  }
}