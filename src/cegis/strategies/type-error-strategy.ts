/**
 * TypeScript Type Error Fix Strategy
 * Phase 2.1: Automatic fixes for common TypeScript compilation errors
 */

import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';

export class TypeErrorFixStrategy extends BaseFixStrategy {
  readonly name = 'TypeScript Type Error Fix';
  readonly category: FailureCategory = 'type_error';
  readonly confidence = 0.8;
  readonly riskLevel = 1;
  readonly description = 'Automatically fixes common TypeScript type errors including missing imports, type annotations, and interface mismatches';

  async canApply(failure: FailureArtifact): Promise<boolean> {
    return failure.category === 'type_error' && 
           !!failure.evidence.errorMessage &&
           !!failure.location?.filePath;
  }

  async generateFix(failure: FailureArtifact): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const errorMessage = failure.evidence.errorMessage || '';
    const tsError = this.parseTypeScriptError(errorMessage);
    
    if (!tsError || !failure.location) {
      return actions;
    }

    switch (tsError.type) {
      case 'name_not_found':
        actions.push(...await this.fixNameNotFound(failure, tsError));
        break;
      case 'property_not_found':
        actions.push(...await this.fixPropertyNotFound(failure, tsError));
        break;
      case 'module_not_found':
        actions.push(...await this.fixModuleNotFound(failure, tsError));
        break;
      case 'type_assignment_error':
        actions.push(...await this.fixTypeAssignmentError(failure, tsError));
        break;
      case 'argument_type_mismatch':
        actions.push(...await this.fixArgumentTypeMismatch(failure, tsError));
        break;
      case 'missing_properties':
        actions.push(...await this.fixMissingProperties(failure, tsError));
        break;
      default:
        actions.push(...await this.fixGenericTypeError(failure, tsError));
    }

    return actions.filter(action => this.validateRepairAction(action));
  }

  private async fixNameNotFound(
    failure: FailureArtifact,
    tsError: { code: string; type: string; description: string }
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const nameMatch = tsError.description.match(/Cannot find name '([^']+)'/);
    
    if (!nameMatch || !nameMatch[1] || !failure.location) return actions;
    
    const missingName = nameMatch[1];
    const filePath = failure.location.filePath;
    
    // Try to add common imports
    const commonImports = this.getCommonImports(missingName);
    
    for (const importStatement of commonImports) {
      actions.push(this.createCodeChangeAction(
        `Add missing import for '${missingName}'`,
        filePath,
        '// Add import at top of file',
        importStatement,
        1,
        1,
        0.8,
        1
      ));
    }
    
    // Try to add type annotation if it looks like a variable declaration
    if (failure.evidence.sourceCode) {
      const sourceLines = failure.evidence.sourceCode.split('\n');
      const targetLine = sourceLines[failure.location.startLine - 1] || '';
      
      if (targetLine.includes(`${missingName} =`) || targetLine.includes(`const ${missingName}`)) {
        const typeAnnotation = this.inferTypeAnnotation(missingName, targetLine);
        if (typeAnnotation) {
          actions.push(this.createTypeAnnotationAction(
            `Add type annotation for '${missingName}'`,
            filePath,
            targetLine,
            targetLine.replace(missingName, `${missingName}: ${typeAnnotation}`),
            failure.location.startLine,
            failure.location.endLine
          ));
        }
      }
    }
    
    return actions;
  }

  private async fixPropertyNotFound(
    failure: FailureArtifact,
    tsError: { code: string; type: string; description: string }
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const propertyMatch = tsError.description.match(/Property '([^']+)' does not exist on type '([^']+)'/);
    
    if (!propertyMatch || !failure.location) return actions;
    
    const [, property, type] = propertyMatch;
    const filePath = failure.location.filePath;
    
    // Suggest optional property access
    if (failure.evidence.sourceCode) {
      const sourceLines = failure.evidence.sourceCode.split('\n');
      const targetLine = sourceLines[failure.location.startLine - 1] || '';
      
      // Change obj.property to obj?.property
      const optionalAccessFix = targetLine.replace(
        new RegExp(`\\.${property}\\b`),
        `?.${property}`
      );
      
      if (optionalAccessFix !== targetLine) {
        actions.push(this.createCodeChangeAction(
          `Use optional property access for '${property}'`,
          filePath,
          targetLine,
          optionalAccessFix,
          failure.location.startLine,
          failure.location.endLine,
          0.9,
          1
        ));
      }
      
      // Suggest type assertion if appropriate
      const typeAssertionFix = targetLine.replace(
        new RegExp(`\\b(\\w+)\\.${property}\\b`),
        `($1 as any).${property}`
      );
      
      if (typeAssertionFix !== targetLine) {
        actions.push(this.createCodeChangeAction(
          `Add type assertion for '${property}' access`,
          filePath,
          targetLine,
          typeAssertionFix,
          failure.location.startLine,
          failure.location.endLine,
          0.6,
          2
        ));
      }
    }
    
    return actions;
  }

  private async fixModuleNotFound(
    failure: FailureArtifact,
    tsError: { code: string; type: string; description: string }
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const moduleMatch = tsError.description.match(/Cannot find module '([^']+)'/);
    
    if (!moduleMatch || !moduleMatch[1] || !failure.location) return actions;
    
    const moduleName = moduleMatch[1];
    const filePath = failure.location.filePath;
    
    // Check if it's a relative import that needs fixing
    if (moduleName.startsWith('.')) {
      // Suggest adding file extension
      const fixes = [
        `${moduleName}.js`,
        `${moduleName}.ts`,
        `${moduleName}/index.js`,
        `${moduleName}/index.ts`
      ];
      
      for (const fix of fixes) {
        actions.push(this.createCodeChangeAction(
          `Fix relative import path: '${moduleName}' -> '${fix}'`,
          filePath,
          `import ... from '${moduleName}'`,
          `import ... from '${fix}'`,
          failure.location.startLine,
          failure.location.endLine,
          0.7,
          1
        ));
      }
    } else {
      // Suggest installing missing package
      actions.push(this.createDependencyUpdateAction(
        `Install missing package '${moduleName}'`,
        moduleName,
        'not_installed',
        'latest',
        0.8,
        3
      ));
    }
    
    return actions;
  }

  private async fixTypeAssignmentError(
    failure: FailureArtifact,
    tsError: { code: string; type: string; description: string }
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    
    if (!failure.location || !failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location.startLine - 1] || '';
    const filePath = failure.location.filePath;
    
    // Try to add type assertion
    const typeAssertionMatch = tsError.description.match(/Type '([^']+)' is not assignable to type '([^']+)'/);
    if (typeAssertionMatch) {
      const [, sourceType, targetType] = typeAssertionMatch;
      
      // Add type assertion
      const withAssertion = targetLine.replace(
        /=\s*([^;]+)/,
        `= $1 as ${targetType}`
      );
      
      if (withAssertion !== targetLine) {
        actions.push(this.createCodeChangeAction(
          `Add type assertion: ${sourceType} as ${targetType}`,
          filePath,
          targetLine,
          withAssertion,
          failure.location.startLine,
          failure.location.endLine,
          0.7,
          2
        ));
      }
    }
    
    return actions;
  }

  private async fixArgumentTypeMismatch(
    failure: FailureArtifact,
    tsError: { code: string; type: string; description: string }
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    
    if (!failure.location || !failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location.startLine - 1] || '';
    const filePath = failure.location.filePath;
    
    // Try to fix common argument type mismatches
    const argMatch = tsError.description.match(/Argument of type '([^']+)' is not assignable to parameter of type '([^']+)'/);
    if (argMatch) {
      const [, argType, paramType] = argMatch;
      
      if (!argType || !paramType) return actions;
      
      // Common fixes
      if (argType === 'string' && paramType === 'number') {
        const withParseInt = targetLine.replace(/(\w+)\s*\)/, 'parseInt($1))');
        if (withParseInt !== targetLine) {
          actions.push(this.createCodeChangeAction(
            `Convert string to number using parseInt()`,
            filePath,
            targetLine,
            withParseInt,
            failure.location.startLine,
            failure.location.endLine,
            0.9,
            1
          ));
        }
      }
      
      if (argType.includes('undefined') && !paramType.includes('undefined')) {
        const withNullCheck = targetLine.replace(
          /(\w+)\s*\)/,
          '$1 || defaultValue)'
        );
        if (withNullCheck !== targetLine) {
          actions.push(this.createCodeChangeAction(
            `Add null check with default value`,
            filePath,
            targetLine,
            withNullCheck,
            failure.location.startLine,
            failure.location.endLine,
            0.7,
            2
          ));
        }
      }
    }
    
    return actions;
  }

  private async fixMissingProperties(
    failure: FailureArtifact,
    tsError: { code: string; type: string; description: string }
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    
    if (!failure.location || !failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location.startLine - 1] || '';
    const filePath = failure.location.filePath;
    
    // Extract missing properties from error message
    const missingMatch = tsError.description.match(/Property '([^']+)' is missing/);
    if (missingMatch) {
      const missingProperty = missingMatch[1];
      
      // Try to add missing property to object literal
      if (targetLine.includes('{') && targetLine.includes('}')) {
        const withProperty = targetLine.replace(
          /\{\s*([^}]*)\s*\}/,
          `{ $1, ${missingProperty}: undefined }`
        );
        
        actions.push(this.createCodeChangeAction(
          `Add missing property '${missingProperty}' with undefined value`,
          filePath,
          targetLine,
          withProperty,
          failure.location.startLine,
          failure.location.endLine,
          0.8,
          1
        ));
      }
    }
    
    return actions;
  }

  private async fixGenericTypeError(
    failure: FailureArtifact,
    tsError: { code: string; type: string; description: string }
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    
    if (!failure.location || !failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location.startLine - 1] || '';
    const filePath = failure.location.filePath;
    
    // Add @ts-ignore as last resort
    actions.push(this.createCodeChangeAction(
      `Add @ts-ignore comment to suppress type error`,
      filePath,
      targetLine,
      `// @ts-ignore\n${targetLine}`,
      failure.location.startLine,
      failure.location.endLine,
      0.3,
      3
    ));
    
    return actions;
  }

  private getCommonImports(name: string): string[] {
    const importMap: Record<string, string[]> = {
      'React': [`import React from 'react';`],
      'useState': [`import { useState } from 'react';`],
      'useEffect': [`import { useEffect } from 'react';`],
      'Component': [`import { Component } from 'react';`],
      'describe': [`import { describe } from 'vitest';`],
      'it': [`import { it } from 'vitest';`],
      'expect': [`import { expect } from 'vitest';`],
      'z': [`import { z } from 'zod';`],
      'express': [`import express from 'express';`],
      'fs': [`import fs from 'fs';`, `import { readFileSync } from 'fs';`],
      'path': [`import path from 'path';`, `import { join } from 'path';`]
    };
    
    return importMap[name] || [];
  }

  private inferTypeAnnotation(name: string, line: string): string | null {
    // Basic type inference from assignment
    if (line.includes('= true') || line.includes('= false')) {
      return 'boolean';
    }
    
    if (line.includes('= []')) {
      return 'any[]';
    }
    
    if (line.includes('= {}')) {
      return 'Record<string, any>';
    }
    
    if (line.match(/= \d+/)) {
      return 'number';
    }
    
    if (line.match(/= ['"`]/)) {
      return 'string';
    }
    
    return null;
  }
}