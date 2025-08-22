/**
 * Phase 1: ContextManager Setup for Efficient Development
 * 
 * This module configures the ContextManager with optimal settings for
 * the self-improvement development process, enabling efficient context
 * management during TypeScript error fixes and codebase improvements.
 */

import { ContextManager, ContextOptions } from '../utils/context-manager.js';
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

export interface ContextSetupResult {
  success: boolean;
  contextManager: ContextManager;
  initialContext: any;
  optimizedSettings: ContextOptions;
  errors: string[];
  recommendations: string[];
}

export class ContextManagerSetup {
  private contextManager: ContextManager;
  private phaseStateManager: PhaseStateManager;
  private projectRoot: string;

  constructor(projectRoot?: string) {
    this.projectRoot = projectRoot || process.cwd();
    this.contextManager = new ContextManager(this.projectRoot);
    this.phaseStateManager = new PhaseStateManager(this.projectRoot);
  }

  /**
   * Set up ContextManager with optimal settings for Phase 1 development
   */
  async setupForPhase1(): Promise<ContextSetupResult> {
    const errors: string[] = [];
    const recommendations: string[] = [];

    try {
      // Ensure Phase 1 is properly initialized
      await this.initializePhase1();

      // Configure optimal context settings for TypeScript error fixing
      const optimizedSettings: ContextOptions = {
        maxTokens: 12000, // Increased for complex TypeScript analysis
        includeHistory: true,
        includeArtifacts: true,
        focusPhase: 'code' as PhaseType, // Use 'code' phase for TypeScript fixes
        relevantKeywords: [
          'typescript',
          'compilation',
          'error',
          'type',
          'interface',
          'class',
          'function',
          'import',
          'export',
          'any',
          'undefined',
          'null',
          'promise',
          'async',
          'await'
        ]
      };

      // Build initial context
      const initialContext = await this.contextManager.buildContext(optimizedSettings);

      // Add working memory for common TypeScript patterns
      await this.setupTypeScriptWorkingMemory();

      // Validate setup
      const validationResults = await this.validateSetup(initialContext);
      errors.push(...validationResults.errors);
      recommendations.push(...validationResults.recommendations);

      return {
        success: errors.length === 0,
        contextManager: this.contextManager,
        initialContext,
        optimizedSettings,
        errors,
        recommendations: [
          ...recommendations,
          'Context manager configured for TypeScript error resolution',
          'Working memory loaded with common TypeScript patterns',
          'Phase 1 context optimized for efficient development',
          'Token budget allocated for comprehensive analysis'
        ]
      };

    } catch (error) {
      errors.push(`Context manager setup failed: ${error}`);
      
      return {
        success: false,
        contextManager: this.contextManager,
        initialContext: null,
        optimizedSettings: {},
        errors,
        recommendations: ['Review context manager configuration and dependencies']
      };
    }
  }

  /**
   * Initialize Phase 1 in the phase state manager
   */
  private async initializePhase1(): Promise<void> {
    const hasProject = await this.phaseStateManager.hasProject();
    
    // Initialize project if no state exists
    if (!hasProject) {
      await this.phaseStateManager.initializeProject('ae-framework-v2', true);
    }
    
    const currentState = await this.phaseStateManager.getCurrentState();
    
    // Move to code phase if we're not already there (since Phase 1 involves TypeScript fixes)
    if (currentState && currentState.currentPhase !== 'code') {
      await this.phaseStateManager.startPhase('code');
    }
  }

  /**
   * Set up working memory with TypeScript-specific patterns and solutions
   */
  private async setupTypeScriptWorkingMemory(): Promise<void> {
    const typeScriptPatterns = {
      'common-type-errors': {
        'any-type-usage': {
          problem: 'Use of "any" type reduces type safety',
          solution: 'Replace with specific interfaces or generic types',
          examples: [
            'Replace "data: any" with "data: T" where T is generic',
            'Use "unknown" instead of "any" for safer type handling',
            'Create specific interfaces for object structures'
          ]
        },
        'undefined-property': {
          problem: 'Property access on potentially undefined values',
          solution: 'Use optional chaining or null checks',
          examples: [
            'Use "obj?.property" instead of "obj.property"',
            'Check "if (obj && obj.property)" before access',
            'Use "obj.property!" for definite assignment assertion'
          ]
        },
        'type-assertion': {
          problem: 'Incorrect type assertions causing runtime errors',
          solution: 'Use proper type guards or interface validation',
          examples: [
            'Replace "data as Type" with type guards',
            'Validate object structure before casting',
            'Use discriminated unions for complex types'
          ]
        }
      },
      'compilation-strategies': {
        'incremental-fixing': {
          approach: 'Fix errors in dependency order',
          steps: [
            'Identify core utility classes first',
            'Fix interface and type definitions',
            'Resolve import/export issues',
            'Address implementation-specific errors'
          ]
        },
        'error-prioritization': {
          high: ['Interface compatibility', 'Missing properties', 'Type mismatches'],
          medium: ['Implicit any types', 'Unused imports', 'Optional parameters'],
          low: ['Formatting issues', 'Prefer const assertions', 'Prefer readonly']
        }
      },
      'common-solutions': {
        'buffer-type-handling': {
          problem: 'Buffer type compatibility with generic types',
          solution: 'Use type assertions with "as any" at assignment level',
          example: '(entry as any).data = await this.compress(entry.data);'
        },
        'missing-properties': {
          problem: 'Missing required properties in object literals',
          solution: 'Add missing properties or make them optional in interface',
          example: 'Add "primaryIntent" property or make it optional with "?"'
        }
      }
    };

    // Add patterns to working memory
    await this.addToWorkingMemory('typescript-patterns', typeScriptPatterns);
    await this.addToWorkingMemory('phase1-progress', {
      currentTask: 'TypeScript error resolution',
      errorsFixed: 1, // enhanced-state-manager.ts
      totalErrors: 278,
      nextPriority: 'Interface compatibility issues'
    });
  }

  /**
   * Add items to working memory through context manager
   */
  private async addToWorkingMemory(key: string, value: any): Promise<void> {
    // Access the private workingMemory through reflection or direct property access
    // Note: This is a workaround since workingMemory is private
    (this.contextManager as any).workingMemory.set(key, value);
  }

  /**
   * Validate the context manager setup
   */
  private async validateSetup(context: any): Promise<{ errors: string[]; recommendations: string[] }> {
    const errors: string[] = [];
    const recommendations: string[] = [];

    // Check context completeness
    if (!context.steering) {
      errors.push('Steering context not loaded');
    }

    if (!context.phaseInfo) {
      errors.push('Phase information not available');
    }

    if (context.totalTokens === 0) {
      errors.push('No context content generated');
    }

    // Check token budget efficiency
    if (context.totalTokens > 15000) {
      recommendations.push('Consider reducing token budget for better performance');
    }

    // Validate phase state
    try {
      const state = await this.phaseStateManager.getCurrentState();
      if (!state) {
        errors.push('Phase state not properly initialized');
      }
    } catch (error) {
      errors.push('Phase state manager validation failed');
    }

    return { errors, recommendations };
  }

  /**
   * Generate a setup report
   */
  generateSetupReport(result: ContextSetupResult): string {
    return `
# ContextManager Setup Report - Phase 1

## Setup Status
${result.success ? '✅ **SUCCESS**' : '❌ **FAILED**'}

## Configuration
- **Max Tokens**: ${result.optimizedSettings.maxTokens || 'Default'}
- **Focus Phase**: ${result.optimizedSettings.focusPhase || 'None'}
- **Include History**: ${result.optimizedSettings.includeHistory ? 'Yes' : 'No'}
- **Include Artifacts**: ${result.optimizedSettings.includeArtifacts ? 'Yes' : 'No'}
- **Relevant Keywords**: ${result.optimizedSettings.relevantKeywords?.length || 0} keywords

## Context Analysis
${result.initialContext ? `
- **Total Tokens**: ${result.initialContext.totalTokens}
- **Steering Length**: ${result.initialContext.steering?.length || 0} chars
- **Phase Info Length**: ${result.initialContext.phaseInfo?.length || 0} chars
- **Working Memory**: ${result.initialContext.workingMemory?.length || 0} chars
- **Relevant Files**: ${result.initialContext.relevantFiles?.length || 0} chars
` : '- No context data available'}

## Errors
${result.errors.length > 0 ? result.errors.map(error => `- ❌ ${error}`).join('\n') : '- None'}

## Recommendations
${result.recommendations.map(rec => `- 💡 ${rec}`).join('\n')}

---
*Generated by ae-framework Phase 1 ContextManager Setup*
    `.trim();
  }
}

export default ContextManagerSetup;