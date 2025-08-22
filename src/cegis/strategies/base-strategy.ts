/**
 * Base Fix Strategy Interface
 * Phase 2.1: Abstract base class for all fix strategies
 */

import { FailureArtifact, FixStrategy, RepairAction, FailureCategory } from '../types.js';

export abstract class BaseFixStrategy implements FixStrategy {
  abstract readonly name: string;
  abstract readonly category: FailureCategory;
  abstract readonly confidence: number;
  abstract readonly riskLevel: number;
  abstract readonly description: string;

  /**
   * Check if this strategy can be applied to the given failure
   */
  abstract canApply(failure: FailureArtifact): Promise<boolean>;

  /**
   * Generate repair actions for the given failure
   */
  abstract generateFix(failure: FailureArtifact): Promise<RepairAction[]>;

  /**
   * Common validation for repair actions
   */
  protected validateRepairAction(action: RepairAction): boolean {
    if (!action.description || action.description.trim().length === 0) {
      return false;
    }
    
    if (action.confidence < 0 || action.confidence > 1) {
      return false;
    }
    
    if (action.riskLevel < 1 || action.riskLevel > 5) {
      return false;
    }
    
    return true;
  }

  /**
   * Helper method to create a code change repair action
   */
  protected createCodeChangeAction(
    description: string,
    filePath: string,
    oldCode: string,
    newCode: string,
    startLine: number,
    endLine: number,
    confidence: number = 0.8,
    riskLevel: number = 2
  ): RepairAction {
    return {
      type: 'code_change',
      description,
      confidence,
      riskLevel,
      estimatedEffort: 'low',
      filePath,
      codeChange: {
        oldCode: oldCode.trim(),
        newCode: newCode.trim(),
        startLine,
        endLine
      },
      dependencies: [],
      prerequisites: []
    };
  }

  /**
   * Helper method to create a dependency update action
   */
  protected createDependencyUpdateAction(
    description: string,
    packageName: string,
    fromVersion: string,
    toVersion: string,
    confidence: number = 0.9,
    riskLevel: number = 3
  ): RepairAction {
    return {
      type: 'dependency_update',
      description,
      confidence,
      riskLevel,
      estimatedEffort: 'medium',
      dependencies: [packageName],
      prerequisites: [`Backup package.json before updating ${packageName}`]
    };
  }

  /**
   * Helper method to create a type annotation action
   */
  protected createTypeAnnotationAction(
    description: string,
    filePath: string,
    oldCode: string,
    newCode: string,
    startLine: number,
    endLine: number,
    confidence: number = 0.7
  ): RepairAction {
    return {
      type: 'type_annotation',
      description,
      confidence,
      riskLevel: 1, // Type annotations are generally low risk
      estimatedEffort: 'low',
      filePath,
      codeChange: {
        oldCode: oldCode.trim(),
        newCode: newCode.trim(),
        startLine,
        endLine
      },
      dependencies: [],
      prerequisites: ['Ensure TypeScript is configured']
    };
  }

  /**
   * Helper method to create a test update action
   */
  protected createTestUpdateAction(
    description: string,
    filePath: string,
    oldCode: string,
    newCode: string,
    startLine: number,
    endLine: number,
    confidence: number = 0.8
  ): RepairAction {
    return {
      type: 'test_update',
      description,
      confidence,
      riskLevel: 1, // Test updates are generally low risk
      estimatedEffort: 'low',
      filePath,
      codeChange: {
        oldCode: oldCode.trim(),
        newCode: newCode.trim(),
        startLine,
        endLine
      },
      dependencies: [],
      prerequisites: ['Run existing tests to ensure baseline']
    };
  }

  /**
   * Helper method to create a validation update action
   */
  protected createValidationUpdateAction(
    description: string,
    filePath: string,
    oldSchema: string,
    newSchema: string,
    confidence: number = 0.8
  ): RepairAction {
    return {
      type: 'validation_update',
      description,
      confidence,
      riskLevel: 2,
      estimatedEffort: 'medium',
      filePath,
      dependencies: ['zod'],
      prerequisites: ['Backup existing validation schema']
    };
  }

  /**
   * Helper method to extract code context around a location
   */
  protected async extractCodeContext(
    filePath: string,
    startLine: number,
    endLine: number,
    contextLines: number = 3
  ): Promise<string> {
    try {
      const fs = await import('fs');
      const content = await fs.promises.readFile(filePath, 'utf-8');
      const lines = content.split('\n');
      
      const start = Math.max(0, startLine - contextLines - 1);
      const end = Math.min(lines.length, endLine + contextLines);
      
      return lines.slice(start, end).join('\n');
    } catch (error) {
      return `// Could not read file: ${filePath}`;
    }
  }

  /**
   * Helper method to check if a file exists
   */
  protected async fileExists(filePath: string): Promise<boolean> {
    try {
      const fs = await import('fs');
      await fs.promises.access(filePath);
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Helper method to parse TypeScript error message
   */
  protected parseTypeScriptError(message: string): {
    code: string;
    type: string;
    description: string;
  } | null {
    // Match TypeScript error pattern: TS2304: Cannot find name 'someVariable'.
    const match = message.match(/TS(\d+):\s*(.+)/);
    if (!match) return null;

    const [, code, description] = match;
    if (!code || !description) return null;
    
    return {
      code,
      type: this.getTypeScriptErrorType(code),
      description: description.trim()
    };
  }

  /**
   * Get TypeScript error type based on error code
   */
  private getTypeScriptErrorType(code: string): string {
    const typeMap: Record<string, string> = {
      '2304': 'name_not_found',
      '2339': 'property_not_found',
      '2345': 'argument_type_mismatch',
      '2322': 'type_assignment_error',
      '2307': 'module_not_found',
      '2571': 'object_literal_type_error',
      '2740': 'missing_properties'
    };
    
    return typeMap[code] || 'unknown_type_error';
  }

  /**
   * Helper method to determine confidence based on error patterns
   */
  protected calculateConfidence(failure: FailureArtifact): number {
    let baseConfidence = 0.5;
    
    // Higher confidence for common error patterns
    if (failure.evidence.stackTrace) {
      baseConfidence += 0.2;
    }
    
    if (failure.evidence.sourceCode) {
      baseConfidence += 0.1;
    }
    
    if (failure.location) {
      baseConfidence += 0.1;
    }
    
    // Lower confidence for complex or rare errors
    if (failure.relatedArtifacts.length > 3) {
      baseConfidence -= 0.1;
    }
    
    return Math.min(Math.max(baseConfidence, 0.1), 0.9);
  }

  /**
   * Helper method to assess risk level
   */
  protected assessRiskLevel(failure: FailureArtifact, changeType: 'code' | 'dependency' | 'config'): number {
    let baseRisk = 2; // Medium risk by default
    
    // Code changes
    if (changeType === 'code') {
      if (failure.location?.functionName?.includes('test')) {
        baseRisk = 1; // Low risk for test changes
      } else if (failure.category === 'type_error') {
        baseRisk = 1; // Type fixes are usually safe
      } else if (failure.category === 'runtime_error') {
        baseRisk = 3; // Runtime fixes can be risky
      }
    }
    
    // Dependency changes
    if (changeType === 'dependency') {
      baseRisk = 3; // Dependencies are inherently risky
      if (failure.category === 'security_violation') {
        baseRisk = 4; // Security updates are high risk
      }
    }
    
    // Configuration changes
    if (changeType === 'config') {
      baseRisk = 2; // Config changes are medium risk
    }
    
    return Math.min(Math.max(baseRisk, 1), 5);
  }
}