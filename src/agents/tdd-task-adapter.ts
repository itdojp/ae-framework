/**
 * TDD Task Adapter for Claude Code
 * 
 * This adapter integrates TDD guidance with Claude Code's Task tool,
 * enabling seamless TDD workflow integration and proactive assistance.
 */

import { TDDAgent, TDDAgentConfig, TDDContext } from './tdd-agent.js';

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

export class TDDTaskAdapter {
  private agent: TDDAgent;

  constructor() {
    const config: TDDAgentConfig = {
      strictMode: true,
      coverageThreshold: 80,
      testFramework: 'vitest',
      blockCodeWithoutTests: true,
      enableRealTimeGuidance: true,
    };

    const context: TDDContext = {
      projectPath: process.cwd(),
      currentPhase: this.detectCurrentPhase(),
    };

    this.agent = new TDDAgent(config, context);
  }

  /**
   * Main handler for TDD-related tasks from Claude Code
   */
  async handleTDDTask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    
    switch (taskType) {
      case 'implement-feature':
        return this.handleFeatureImplementation(request);
      
      case 'validate-tdd':
        return this.handleTDDValidation(request);
      
      case 'guide-development':
        return this.handleDevelopmentGuidance(request);
      
      case 'enforce-compliance':
        return this.handleComplianceEnforcement(request);
      
      case 'analyze-code':
        return this.handleCodeAnalysis(request);
      
      default:
        return this.handleGenericTDDGuidance(request);
    }
  }

  /**
   * Proactive TDD suggestions for Claude Code's autonomous operation
   */
  async provideProviacticeGuidance(context: {
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
    // Analyze context to determine if TDD intervention is needed
    const analysis = await this.analyzeRecentActivity(context);
    
    if (analysis.hasTDDViolations) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'warning',
          message: 'TDD violation detected in recent development',
          recommendedActions: analysis.correctionActions,
        },
      };
    }

    if (analysis.missedTDDOpportunity) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'suggestion',
          message: 'Consider following TDD approach for better code quality',
          recommendedActions: analysis.tddSuggestions,
        },
      };
    }

    return {
      shouldIntervene: false,
      intervention: {
        type: 'suggestion',
        message: 'Development looks good from TDD perspective',
        recommendedActions: [],
      },
    };
  }

  private async handleFeatureImplementation(request: TaskRequest): Promise<TaskResponse> {
    const feature = this.extractFeatureName(request.prompt);
    const plan = await this.agent.generateFeatureTDDPlan(feature);
    
    const currentPhase = plan.phases[0]; // Start with RED phase
    
    return {
      summary: `TDD Implementation Plan for: ${feature}`,
      analysis: `
# TDD Implementation Plan

**Feature**: ${feature}
**Estimated Effort**: ${plan.estimatedEffort}
**Current Phase**: ${currentPhase.name}

## Risk Factors
${plan.riskFactors.map((risk: any) => `• ${risk}`).join('\n')}
      `.trim(),
      recommendations: currentPhase.tasks.map((task: any) => `${task.action} (${task.priority} priority)`),
      nextActions: [
        'Start with RED phase - write failing tests first',
        `Create test file for ${feature}`,
        'Run tests to confirm they fail',
        'Only then proceed to implementation',
      ],
      warnings: plan.riskFactors.length > 0 ? ['High complexity feature - extra attention to test coverage needed'] : [],
      shouldBlockProgress: false,
    };
  }

  private async handleTDDValidation(request: TaskRequest): Promise<TaskResponse> {
    const guidance = await this.agent.provideTDDGuidance(request.prompt);
    const compliance = await this.agent.monitorTDDCompliance();
    
    return {
      summary: `TDD Validation Results - Compliance Score: ${compliance.complianceScore}%`,
      analysis: guidance.analysis,
      recommendations: guidance.nextSteps,
      nextActions: guidance.tasks.map((task: any) => task.action),
      warnings: guidance.warnings.concat(
        compliance.violations
          .filter((v: any) => v.severity === 'error')
          .map((v: any) => v.description)
      ),
      shouldBlockProgress: compliance.violations.some((v: any) => v.severity === 'error'),
    };
  }

  private async handleDevelopmentGuidance(request: TaskRequest): Promise<TaskResponse> {
    const guidance = await this.agent.provideTDDGuidance(request.prompt);
    
    return {
      summary: 'TDD Development Guidance',
      analysis: guidance.analysis,
      recommendations: guidance.nextSteps,
      nextActions: guidance.tasks.map((task: any) => `${task.action} - ${task.expectedOutcome}`),
      warnings: guidance.warnings,
      shouldBlockProgress: false,
    };
  }

  private async handleComplianceEnforcement(request: TaskRequest): Promise<TaskResponse> {
    const compliance = await this.agent.monitorTDDCompliance();
    const criticalViolations = compliance.violations.filter((v: any) => v.severity === 'error');
    
    return {
      summary: `TDD Compliance Check - ${criticalViolations.length} critical violations found`,
      analysis: `
# TDD Compliance Report

**Compliance Score**: ${compliance.complianceScore}%
**Total Violations**: ${compliance.violations.length}
**Critical Violations**: ${criticalViolations.length}

## Trends
- **Improving**: ${compliance.trends.improving ? 'Yes' : 'No'}
- **Recent Violations**: ${compliance.trends.recentViolations}
- **Coverage Trend**: ${compliance.trends.coverageTrend}
      `.trim(),
      recommendations: compliance.violations.map((v: any) => v.recommendation),
      nextActions: criticalViolations.map((v: any) => `Fix: ${v.description}`),
      warnings: criticalViolations.map((v: any) => v.description),
      shouldBlockProgress: criticalViolations.length > 0,
    };
  }

  private async handleCodeAnalysis(request: TaskRequest): Promise<TaskResponse> {
    const codeFile = this.extractFilePath(request.prompt);
    
    if (codeFile && codeFile.endsWith('.ts')) {
      try {
        // Read file content (in real implementation)
        const content = ''; // Placeholder
        const testSuggestion = await this.agent.suggestTestsForCode(codeFile, content);
        
        return {
          summary: `Test suggestions for ${codeFile}`,
          analysis: `
# Test Analysis for ${codeFile}

**Suggested Test File**: ${testSuggestion.testFile}
**Test Cases**: ${testSuggestion.testCases.length}

## Critical Test Cases
${testSuggestion.testCases
  .filter((tc: any) => tc.importance === 'critical')
  .map((tc: any) => `• ${tc.name}: ${tc.description}`)
  .join('\n')}
          `.trim(),
          recommendations: [
            `Create ${testSuggestion.testFile}`,
            `Implement ${testSuggestion.testCases.length} test cases`,
            'Focus on critical test cases first',
          ],
          nextActions: [
            'Create test file before implementing functionality',
            'Write failing tests that describe expected behavior',
            'Implement minimal code to make tests pass',
          ],
          warnings: testSuggestion.testCases.length === 0 ? ['No testable functionality detected'] : [],
          shouldBlockProgress: false,
        };
      } catch (error) {
        return {
          summary: 'Code analysis failed',
          analysis: `Error analyzing ${codeFile}: ${error}`,
          recommendations: ['Ensure file exists and is readable'],
          nextActions: ['Check file path and permissions'],
          warnings: ['Could not analyze code file'],
          shouldBlockProgress: false,
        };
      }
    }

    return this.handleGenericTDDGuidance(request);
  }

  private async handleGenericTDDGuidance(request: TaskRequest): Promise<TaskResponse> {
    const guidance = await this.agent.provideTDDGuidance(request.prompt);
    
    return {
      summary: 'General TDD Guidance',
      analysis: guidance.analysis,
      recommendations: guidance.nextSteps,
      nextActions: guidance.tasks.map((task: any) => task.action),
      warnings: guidance.warnings,
      shouldBlockProgress: false,
    };
  }

  private classifyTask(description: string, prompt: string): string {
    const combined = (description + ' ' + prompt).toLowerCase();
    
    if (combined.includes('implement') || combined.includes('create') || combined.includes('add')) {
      return 'implement-feature';
    }
    
    if (combined.includes('validate') || combined.includes('check') || combined.includes('verify')) {
      return 'validate-tdd';
    }
    
    if (combined.includes('guide') || combined.includes('help') || combined.includes('how')) {
      return 'guide-development';
    }
    
    if (combined.includes('enforce') || combined.includes('compliance') || combined.includes('violation')) {
      return 'enforce-compliance';
    }
    
    if (combined.includes('analyze') || combined.includes('review') || combined.includes('suggest')) {
      return 'analyze-code';
    }
    
    return 'generic-guidance';
  }

  private extractFeatureName(prompt: string): string {
    // Extract feature name from prompt
    const match = prompt.match(/implement\s+([^\.]+)/i) || 
                  prompt.match(/create\s+([^\.]+)/i) ||
                  prompt.match(/add\s+([^\.]+)/i);
    
    return match ? match[1].trim() : 'new feature';
  }

  private extractFilePath(prompt: string): string | null {
    // Extract file path from prompt
    const match = prompt.match(/([^\s]+\.ts)/);
    return match ? match[1] : null;
  }

  private detectCurrentPhase(): string {
    // Detect current development phase
    if (require('fs').existsSync('src') && require('fs').existsSync('tests')) {
      return '4-code';
    } else if (require('fs').existsSync('tests') || require('fs').existsSync('specs')) {
      return '3-tests';
    } else if (require('fs').existsSync('specs/formal')) {
      return '2-formal';
    } else {
      return '1-intent';
    }
  }

  private async analyzeRecentActivity(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    hasTDDViolations: boolean;
    missedTDDOpportunity: boolean;
    correctionActions: string[];
    tddSuggestions: string[];
  }> {
    const srcFiles = context.recentFiles.filter(f => f.startsWith('src/') && f.endsWith('.ts'));
    const testFiles = context.recentFiles.filter(f => f.includes('.test.ts') || f.includes('.spec.ts'));
    
    const hasTDDViolations = srcFiles.length > 0 && testFiles.length === 0;
    const missedTDDOpportunity = context.userIntent.toLowerCase().includes('implement') && testFiles.length === 0;
    
    return {
      hasTDDViolations,
      missedTDDOpportunity,
      correctionActions: hasTDDViolations ? [
        'Create test files for the recently added source files',
        'Write failing tests before continuing implementation',
        'Run tests to ensure they fail (RED phase)',
      ] : [],
      tddSuggestions: missedTDDOpportunity ? [
        'Consider starting with test-first approach',
        'Define expected behavior in tests before implementation',
        'Follow RED-GREEN-REFACTOR cycle for better code quality',
      ] : [],
    };
  }
}

// Export for Claude Code Task tool integration
export const createTDDTaskHandler = () => {
  const adapter = new TDDTaskAdapter();
  
  return {
    handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
      return adapter.handleTDDTask(request);
    },
    
    provideProactiveGuidance: async (context: any): Promise<any> => {
      return adapter.provideProviacticeGuidance(context);
    },
  };
};