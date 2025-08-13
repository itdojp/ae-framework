/**
 * Improve Command for ae-framework  
 * Suggests and applies code improvements
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as ts from 'typescript';
import type { CommandResult, CommandContext } from '../slash-command-manager.js';
import { EvidenceValidator } from '../../utils/evidence-validator.js';

export interface ImprovementResult {
  file: string;
  improvements: Improvement[];
  applied: boolean;
  evidence?: any;
}

export interface Improvement {
  type: ImprovementType;
  description: string;
  location: {
    line: number;
    column?: number;
  };
  original: string;
  suggested: string;
  impact: 'high' | 'medium' | 'low';
  category: 'performance' | 'readability' | 'maintainability' | 'security' | 'best-practice';
}

export type ImprovementType = 
  | 'refactor'
  | 'optimize'
  | 'simplify'
  | 'modernize'
  | 'security'
  | 'pattern'
  | 'naming'
  | 'documentation';

export class ImproveCommand {
  private validator: EvidenceValidator;

  constructor() {
    this.validator = new EvidenceValidator();
  }

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a file or directory to improve'
      };
    }

    const target = args[0];
    const options = this.parseOptions(args.slice(1));

    try {
      const results = await this.improve(target, options);
      const summary = this.generateSummary(results);

      return {
        success: true,
        message: summary,
        data: results
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Improvement failed: ${error.message}`
      };
    }
  }

  private parseOptions(args: string[]): any {
    const options: any = {
      apply: false,
      category: 'all',
      validateSuggestions: false,
      interactive: false
    };

    for (let i = 0; i < args.length; i++) {
      switch (args[i]) {
        case '--apply':
          options.apply = true;
          break;
        case '--category':
          options.category = args[++i] || 'all';
          break;
        case '--validate':
          options.validateSuggestions = true;
          break;
        case '--interactive':
          options.interactive = true;
          break;
      }
    }

    return options;
  }

  private async improve(target: string, options: any): Promise<ImprovementResult[]> {
    const results: ImprovementResult[] = [];
    const stats = await fs.stat(target);

    if (stats.isDirectory()) {
      const files = await this.findSourceFiles(target);
      for (const file of files) {
        const result = await this.improveFile(file, options);
        results.push(result);
      }
    } else {
      const result = await this.improveFile(target, options);
      results.push(result);
    }

    return results;
  }

  private async findSourceFiles(dir: string): Promise<string[]> {
    const files: string[] = [];
    const entries = await fs.readdir(dir, { withFileTypes: true });

    for (const entry of entries) {
      const fullPath = path.join(dir, entry.name);
      
      if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
        const subFiles = await this.findSourceFiles(fullPath);
        files.push(...subFiles);
      } else if (entry.isFile() && (entry.name.endsWith('.ts') || entry.name.endsWith('.js'))) {
        files.push(fullPath);
      }
    }

    return files;
  }

  private async improveFile(file: string, options: any): Promise<ImprovementResult> {
    const content = await fs.readFile(file, 'utf-8');
    const improvements: Improvement[] = [];

    // Detect various improvement opportunities
    improvements.push(...this.detectRefactoringOpportunities(content));
    improvements.push(...this.detectOptimizationOpportunities(content));
    improvements.push(...this.detectModernizationOpportunities(content));
    improvements.push(...this.detectPatternImprovements(content));
    improvements.push(...this.detectNamingImprovements(content));
    improvements.push(...this.detectSecurityImprovements(content));

    // Filter by category if specified
    const filteredImprovements = options.category === 'all'
      ? improvements
      : improvements.filter(i => i.category === options.category);

    // Validate suggestions if requested
    if (options.validateSuggestions && filteredImprovements.length > 0) {
      const validation = await this.validator.validateClaim(
        `Code improvements for ${file}`,
        JSON.stringify(filteredImprovements.map(i => i.description)),
        { minConfidence: 0.6 }
      );
      
      // Filter out low-confidence suggestions
      if (validation.confidence < 0.5) {
        filteredImprovements.splice(filteredImprovements.length / 2);
      }
    }

    // Apply improvements if requested
    let applied = false;
    if (options.apply && filteredImprovements.length > 0) {
      applied = await this.applyImprovements(file, content, filteredImprovements, options);
    }

    return {
      file,
      improvements: filteredImprovements,
      applied
    };
  }

  private detectRefactoringOpportunities(content: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Long functions
      if (line.includes('function') || line.includes('=>')) {
        const functionBody = this.extractFunctionBody(lines, index);
        if (functionBody.length > 50) {
          improvements.push({
            type: 'refactor',
            description: 'Extract smaller functions from long function',
            location: { line: index + 1 },
            original: line,
            suggested: '// Break into smaller functions',
            impact: 'medium',
            category: 'maintainability'
          });
        }
      }

      // Duplicate code detection (simplified)
      const codePattern = line.trim();
      if (codePattern.length > 30) {
        let duplicates = 0;
        for (let i = index + 1; i < lines.length; i++) {
          if (lines[i].trim() === codePattern) {
            duplicates++;
          }
        }
        if (duplicates > 1) {
          improvements.push({
            type: 'refactor',
            description: 'Extract duplicate code to reusable function',
            location: { line: index + 1 },
            original: line,
            suggested: '// Extract to shared function',
            impact: 'high',
            category: 'maintainability'
          });
        }
      }

      // Complex conditionals
      const logicalOps = (line.match(/&&|\|\|/g) || []).length;
      if (logicalOps > 3) {
        improvements.push({
          type: 'simplify',
          description: 'Simplify complex conditional',
          location: { line: index + 1 },
          original: line,
          suggested: '// Extract to named boolean variables',
          impact: 'medium',
          category: 'readability'
        });
      }
    });

    return improvements;
  }

  private detectOptimizationOpportunities(content: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Array operations that could be optimized
      if (line.includes('.filter(') && line.includes('.map(')) {
        improvements.push({
          type: 'optimize',
          description: 'Combine filter and map into single reduce',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace('.filter(', '.reduce((acc, item) => {'),
          impact: 'medium',
          category: 'performance'
        });
      }

      // Multiple array iterations
      if (line.includes('.forEach(') && lines[index + 1]?.includes('.forEach(')) {
        improvements.push({
          type: 'optimize',
          description: 'Combine multiple forEach loops',
          location: { line: index + 1 },
          original: line,
          suggested: '// Combine into single iteration',
          impact: 'medium',
          category: 'performance'
        });
      }

      // String concatenation in loops
      if ((line.includes('for') || line.includes('while')) && 
          lines.slice(index, index + 10).some(l => l.includes('+='))) {
        improvements.push({
          type: 'optimize',
          description: 'Use array.join() instead of string concatenation in loop',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use array.push() then join()',
          impact: 'high',
          category: 'performance'
        });
      }

      // Synchronous file operations
      if (line.includes('readFileSync') || line.includes('writeFileSync')) {
        const asyncVersion = line.replace('Sync', '');
        improvements.push({
          type: 'optimize',
          description: 'Use async file operations',
          location: { line: index + 1 },
          original: line,
          suggested: `await ${asyncVersion}`,
          impact: 'high',
          category: 'performance'
        });
      }
    });

    return improvements;
  }

  private detectModernizationOpportunities(content: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // var to const/let
      if (line.includes('var ')) {
        const suggested = line.replace(/\bvar\b/, 'const');
        improvements.push({
          type: 'modernize',
          description: 'Replace var with const/let',
          location: { line: index + 1 },
          original: line,
          suggested,
          impact: 'low',
          category: 'best-practice'
        });
      }

      // Callback to async/await
      if (line.includes('callback') || line.includes('cb(')) {
        improvements.push({
          type: 'modernize',
          description: 'Convert callback to async/await',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use async/await pattern',
          impact: 'medium',
          category: 'readability'
        });
      }

      // Old array methods
      if (line.includes('arguments.') || line.includes('Array.prototype.slice.call')) {
        improvements.push({
          type: 'modernize',
          description: 'Use rest parameters or spread operator',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use ...args',
          impact: 'low',
          category: 'best-practice'
        });
      }

      // Template literals
      if (line.includes('" + ') || line.includes("' + ")) {
        const suggested = this.convertToTemplateLiteral(line);
        if (suggested !== line) {
          improvements.push({
            type: 'modernize',
            description: 'Use template literals',
            location: { line: index + 1 },
            original: line,
            suggested,
            impact: 'low',
            category: 'readability'
          });
        }
      }
    });

    return improvements;
  }

  private detectPatternImprovements(content: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    // Detect anti-patterns
    lines.forEach((line, index) => {
      // Nested ternary operators
      if ((line.match(/\?/g) || []).length > 1) {
        improvements.push({
          type: 'pattern',
          description: 'Replace nested ternary with if-else or switch',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use if-else statement',
          impact: 'medium',
          category: 'readability'
        });
      }

      // Magic numbers
      if (line.match(/[^0-9][0-9]{2,}[^0-9]/) && !line.includes('const')) {
        improvements.push({
          type: 'pattern',
          description: 'Extract magic number to named constant',
          location: { line: index + 1 },
          original: line,
          suggested: '// Define as const MEANINGFUL_NAME',
          impact: 'low',
          category: 'maintainability'
        });
      }

      // God objects (too many methods)
      if (line.includes('class ')) {
        const classBody = this.extractClassBody(lines, index);
        const methodCount = (classBody.join('\n').match(/^\s*(async\s+)?[a-zA-Z]+\s*\(/gm) || []).length;
        if (methodCount > 10) {
          improvements.push({
            type: 'pattern',
            description: 'Split large class into smaller, focused classes',
            location: { line: index + 1 },
            original: line,
            suggested: '// Apply Single Responsibility Principle',
            impact: 'high',
            category: 'maintainability'
          });
        }
      }
    });

    return improvements;
  }

  private detectNamingImprovements(content: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Single letter variables (except in loops)
      const varPattern = /\b(const|let|var)\s+([a-z])\s*=/;
      const match = line.match(varPattern);
      if (match && !line.includes('for')) {
        improvements.push({
          type: 'naming',
          description: `Use descriptive name instead of '${match[2]}'`,
          location: { line: index + 1 },
          original: line,
          suggested: line.replace(match[2], 'descriptiveName'),
          impact: 'low',
          category: 'readability'
        });
      }

      // Non-camelCase functions
      const funcPattern = /function\s+([a-z]+_[a-z]+)/;
      const funcMatch = line.match(funcPattern);
      if (funcMatch) {
        const camelCase = funcMatch[1].replace(/_([a-z])/g, (_, letter) => letter.toUpperCase());
        improvements.push({
          type: 'naming',
          description: 'Use camelCase for function names',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace(funcMatch[1], camelCase),
          impact: 'low',
          category: 'best-practice'
        });
      }

      // Boolean variables without is/has prefix
      const boolPattern = /\b(const|let)\s+([a-z]+)\s*=\s*(true|false)/;
      const boolMatch = line.match(boolPattern);
      if (boolMatch && !boolMatch[2].startsWith('is') && !boolMatch[2].startsWith('has')) {
        improvements.push({
          type: 'naming',
          description: `Prefix boolean variable with 'is' or 'has'`,
          location: { line: index + 1 },
          original: line,
          suggested: line.replace(boolMatch[2], `is${boolMatch[2][0].toUpperCase()}${boolMatch[2].slice(1)}`),
          impact: 'low',
          category: 'readability'
        });
      }
    });

    return improvements;
  }

  private detectSecurityImprovements(content: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // eval usage
      if (line.includes('eval(')) {
        improvements.push({
          type: 'security',
          description: 'Remove eval() - security risk',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use JSON.parse() or Function constructor',
          impact: 'high',
          category: 'security'
        });
      }

      // innerHTML
      if (line.includes('innerHTML')) {
        improvements.push({
          type: 'security',
          description: 'Use textContent or sanitize HTML',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace('innerHTML', 'textContent'),
          impact: 'high',
          category: 'security'
        });
      }

      // SQL queries without parameterization
      if (line.match(/query\(.*\+.*\)/) || line.match(/query\(`.*\${/)) {
        improvements.push({
          type: 'security',
          description: 'Use parameterized queries to prevent SQL injection',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use prepared statements',
          impact: 'high',
          category: 'security'
        });
      }

      // Hardcoded secrets
      if (line.match(/api[_-]?key|password|secret|token/i) && line.includes('"')) {
        improvements.push({
          type: 'security',
          description: 'Move secrets to environment variables',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use process.env.SECRET_NAME',
          impact: 'high',
          category: 'security'
        });
      }
    });

    return improvements;
  }

  private extractFunctionBody(lines: string[], startIndex: number): string[] {
    const body: string[] = [];
    let braceCount = 0;
    let started = false;

    for (let i = startIndex; i < lines.length; i++) {
      const line = lines[i];
      
      if (line.includes('{')) {
        started = true;
        braceCount += (line.match(/{/g) || []).length;
      }
      
      if (started) {
        body.push(line);
      }
      
      if (line.includes('}')) {
        braceCount -= (line.match(/}/g) || []).length;
        if (braceCount === 0 && started) {
          break;
        }
      }
    }

    return body;
  }

  private extractClassBody(lines: string[], startIndex: number): string[] {
    return this.extractFunctionBody(lines, startIndex);
  }

  private convertToTemplateLiteral(line: string): string {
    // Simple conversion of string concatenation to template literals
    return line.replace(/"([^"]*)" \+ ([a-zA-Z_$][a-zA-Z0-9_$]*) \+ "([^"]*)"/g, '`$1${$2}$3`')
               .replace(/'([^']*)' \+ ([a-zA-Z_$][a-zA-Z0-9_$]*) \+ '([^']*)'/g, '`$1${$2}$3`');
  }

  private async applyImprovements(
    file: string,
    content: string,
    improvements: Improvement[],
    options: any
  ): Promise<boolean> {
    let modifiedContent = content;
    const lines = content.split('\n');

    // Sort improvements by line number (reverse order to avoid line number shifts)
    improvements.sort((a, b) => b.location.line - a.location.line);

    for (const improvement of improvements) {
      if (options.interactive) {
        // In a real implementation, this would prompt the user
        console.log(`Apply improvement: ${improvement.description}? (y/n)`);
        // For now, we'll skip interactive mode
        continue;
      }

      const lineIndex = improvement.location.line - 1;
      if (lineIndex >= 0 && lineIndex < lines.length) {
        // Only apply if the suggested change is not a comment
        if (!improvement.suggested.startsWith('//')) {
          lines[lineIndex] = improvement.suggested;
        }
      }
    }

    modifiedContent = lines.join('\n');

    // Only write if content actually changed
    if (modifiedContent !== content) {
      await fs.writeFile(file, modifiedContent, 'utf-8');
      return true;
    }

    return false;
  }

  private generateSummary(results: ImprovementResult[]): string {
    let summary = `Analyzed ${results.length} file(s)\n\n`;
    
    let totalImprovements = 0;
    let appliedCount = 0;
    const byCategory: Record<string, number> = {};

    for (const result of results) {
      totalImprovements += result.improvements.length;
      if (result.applied) appliedCount++;

      for (const improvement of result.improvements) {
        byCategory[improvement.category] = (byCategory[improvement.category] || 0) + 1;
      }
    }

    summary += `Total improvements found: ${totalImprovements}\n`;
    if (appliedCount > 0) {
      summary += `Files modified: ${appliedCount}\n`;
    }

    if (Object.keys(byCategory).length > 0) {
      summary += '\nImprovements by category:\n';
      for (const [category, count] of Object.entries(byCategory)) {
        summary += `  ${category}: ${count}\n`;
      }
    }

    // Add top improvements
    const highImpact = results
      .flatMap(r => r.improvements)
      .filter(i => i.impact === 'high')
      .slice(0, 3);

    if (highImpact.length > 0) {
      summary += '\nHigh impact improvements:\n';
      for (const improvement of highImpact) {
        summary += `  - ${improvement.description}\n`;
      }
    }

    return summary;
  }
}