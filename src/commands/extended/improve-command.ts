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
  name = '/ae:improve';
  description = 'Suggest and apply code improvements';
  category = 'utility' as const;
  usage = '/ae:improve <file> [--apply] [--category=performance|readability|maintainability|security] [--validate]';
  aliases = ['/improve', '/a:improve'];

  private validator: EvidenceValidator;

  constructor() {
    this.validator = new EvidenceValidator();
  }

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a file to improve'
      };
    }

    const target = args[0];
    const options = this.parseOptions(args.slice(1));

    try {
      const results = await this.generateImprovements(target, options);
      const summary = this.generateSummary(results);

      // Validate improvements with evidence if requested
      if (options.validate) {
        for (const result of results) {
          for (const improvement of result.improvements) {
            const validation = await this.validator.validateClaim(
              `Code improvement: ${improvement.description}`,
              JSON.stringify({ original: improvement.original, suggested: improvement.suggested }),
              { minConfidence: 0.7 }
            );
            
            if (!result.evidence) result.evidence = [];
            result.evidence.push(validation);
          }
        }
      }

      return {
        success: true,
        message: summary,
        data: results
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Improvement generation failed: ${error.message}`
      };
    }
  }

  private parseOptions(args: string[]): any {
    const options: any = {
      apply: false,
      category: null,
      validate: false,
      impact: null
    };

    for (const arg of args) {
      if (arg === '--apply') {
        options.apply = true;
      } else if (arg.startsWith('--category=')) {
        options.category = arg.split('=')[1];
      } else if (arg.startsWith('--impact=')) {
        options.impact = arg.split('=')[1];
      } else if (arg === '--validate') {
        options.validate = true;
      }
    }

    return options;
  }

  private async generateImprovements(target: string, options: any): Promise<ImprovementResult[]> {
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
    const improvements = await this.analyzeForImprovements(content, file, options);
    
    let applied = false;
    if (options.apply && improvements.length > 0) {
      applied = await this.applyImprovements(file, improvements);
    }

    return {
      file,
      improvements,
      applied
    };
  }

  private async analyzeForImprovements(
    content: string, 
    file: string, 
    options: any
  ): Promise<Improvement[]> {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    // Performance improvements
    if (!options.category || options.category === 'performance') {
      improvements.push(...this.findPerformanceImprovements(content, lines));
    }

    // Readability improvements
    if (!options.category || options.category === 'readability') {
      improvements.push(...this.findReadabilityImprovements(content, lines));
    }

    // Maintainability improvements
    if (!options.category || options.category === 'maintainability') {
      improvements.push(...this.findMaintainabilityImprovements(content, lines));
    }

    // Security improvements
    if (!options.category || options.category === 'security') {
      improvements.push(...this.findSecurityImprovements(content, lines));
    }

    // Best practice improvements
    if (!options.category || options.category === 'best-practice') {
      improvements.push(...this.findBestPracticeImprovements(content, lines));
    }

    // Filter by impact if specified
    if (options.impact) {
      return improvements.filter(imp => imp.impact === options.impact);
    }

    return improvements;
  }

  private findPerformanceImprovements(content: string, lines: string[]): Improvement[] {
    const improvements: Improvement[] = [];

    lines.forEach((line, index) => {
      const trimmed = line.trim();

      // Suggest using const instead of let when variable is not reassigned
      if (trimmed.match(/^let\s+\w+\s*=/) && !content.includes(`${trimmed.split('=')[0].replace('let', '').trim()} =`)) {
        improvements.push({
          type: 'optimize',
          description: 'Use const instead of let for variables that are not reassigned',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace('let ', 'const '),
          impact: 'low',
          category: 'performance'
        });
      }

      // Suggest using for...of instead of forEach for better performance
      if (trimmed.includes('.forEach(')) {
        const arrayName = trimmed.split('.forEach(')[0].trim();
        improvements.push({
          type: 'optimize',
          description: 'Use for...of loop instead of forEach for better performance',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace(`${arrayName}.forEach(`, `for (const item of ${arrayName}) {`),
          impact: 'medium',
          category: 'performance'
        });
      }

      // Suggest avoiding nested loops
      if (trimmed.includes('for (') && content.substring(content.indexOf(line)).includes('for (')) {
        improvements.push({
          type: 'refactor',
          description: 'Consider refactoring nested loops to improve O(n²) complexity',
          location: { line: index + 1 },
          original: line,
          suggested: '// Consider using Map or Set for O(1) lookups instead',
          impact: 'high',
          category: 'performance'
        });
      }
    });

    return improvements;
  }

  private findReadabilityImprovements(content: string, lines: string[]): Improvement[] {
    const improvements: Improvement[] = [];

    lines.forEach((line, index) => {
      const trimmed = line.trim();

      // Suggest better variable names
      if (trimmed.match(/^(let|const|var)\s+[a-z]\s*=/)) {
        improvements.push({
          type: 'naming',
          description: 'Use more descriptive variable names instead of single letters',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace(/\b[a-z]\b/, 'descriptiveName'),
          impact: 'medium',
          category: 'readability'
        });
      }

      // Suggest adding comments for complex logic
      if (trimmed.includes('?') && trimmed.includes(':') && !lines[index - 1]?.trim().startsWith('//')) {
        improvements.push({
          type: 'documentation',
          description: 'Add comment to explain complex ternary operation',
          location: { line: index + 1 },
          original: line,
          suggested: `// Explain the condition\n${line}`,
          impact: 'low',
          category: 'readability'
        });
      }

      // Suggest breaking long lines
      if (line.length > 120) {
        improvements.push({
          type: 'simplify',
          description: 'Break long line for better readability',
          location: { line: index + 1 },
          original: line,
          suggested: '// Consider breaking this line into multiple lines',
          impact: 'low',
          category: 'readability'
        });
      }
    });

    return improvements;
  }

  private findMaintainabilityImprovements(content: string, lines: string[]): Improvement[] {
    const improvements: Improvement[] = [];

    lines.forEach((line, index) => {
      const trimmed = line.trim();

      // Suggest extracting magic numbers
      const magicNumbers = trimmed.match(/\b\d{2,}\b/g);
      if (magicNumbers) {
        for (const num of magicNumbers) {
          if (num !== '100' && num !== '200' && !['0', '1', '2'].includes(num)) {
            improvements.push({
              type: 'refactor',
              description: `Extract magic number ${num} to a named constant`,
              location: { line: index + 1 },
              original: line,
              suggested: line.replace(num, `MEANINGFUL_CONSTANT_NAME`),
              impact: 'medium',
              category: 'maintainability'
            });
          }
        }
      }

      // Suggest removing dead code (commented out lines)
      if (trimmed.startsWith('//') && trimmed.length > 10 && !trimmed.includes('TODO') && !trimmed.includes('FIXME')) {
        improvements.push({
          type: 'simplify',
          description: 'Remove commented out code to reduce clutter',
          location: { line: index + 1 },
          original: line,
          suggested: '',
          impact: 'low',
          category: 'maintainability'
        });
      }

      // Suggest using template literals
      if (trimmed.includes('+') && trimmed.includes('"') && trimmed.includes("'")) {
        improvements.push({
          type: 'modernize',
          description: 'Use template literals instead of string concatenation',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace(/["'].*?["']/g, '`template literal`'),
          impact: 'low',
          category: 'maintainability'
        });
      }
    });

    return improvements;
  }

  private findSecurityImprovements(content: string, lines: string[]): Improvement[] {
    const improvements: Improvement[] = [];

    lines.forEach((line, index) => {
      const trimmed = line.trim();

      // Suggest avoiding eval
      if (trimmed.includes('eval(')) {
        improvements.push({
          type: 'security',
          description: 'Avoid using eval() as it can execute arbitrary code',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use safer alternatives like JSON.parse() or Function constructor',
          impact: 'high',
          category: 'security'
        });
      }

      // Suggest input validation
      if (trimmed.includes('req.body') || trimmed.includes('req.params') || trimmed.includes('req.query')) {
        improvements.push({
          type: 'security',
          description: 'Add input validation for user data',
          location: { line: index + 1 },
          original: line,
          suggested: `// Validate input: ${line}`,
          impact: 'high',
          category: 'security'
        });
      }

      // Suggest using HTTPS
      if (trimmed.includes('http://')) {
        improvements.push({
          type: 'security',
          description: 'Use HTTPS instead of HTTP for secure communication',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace('http://', 'https://'),
          impact: 'high',
          category: 'security'
        });
      }
    });

    return improvements;
  }

  private findBestPracticeImprovements(content: string, lines: string[]): Improvement[] {
    const improvements: Improvement[] = [];

    lines.forEach((line, index) => {
      const trimmed = line.trim();

      // Suggest removing console.log in production
      if (trimmed.includes('console.log')) {
        improvements.push({
          type: 'pattern',
          description: 'Remove console.log statements from production code',
          location: { line: index + 1 },
          original: line,
          suggested: '// Use proper logging library instead',
          impact: 'medium',
          category: 'best-practice'
        });
      }

      // Suggest using async/await instead of .then()
      if (trimmed.includes('.then(')) {
        improvements.push({
          type: 'modernize',
          description: 'Consider using async/await instead of .then() for better readability',
          location: { line: index + 1 },
          original: line,
          suggested: '// Refactor to use async/await',
          impact: 'medium',
          category: 'best-practice'
        });
      }

      // Suggest using arrow functions for short functions
      if (trimmed.startsWith('function(') && line.length < 80) {
        improvements.push({
          type: 'modernize',
          description: 'Use arrow function for concise syntax',
          location: { line: index + 1 },
          original: line,
          suggested: line.replace('function(', '(').replace(') {', ') => {'),
          impact: 'low',
          category: 'best-practice'
        });
      }
    });

    return improvements;
  }

  private async applyImprovements(file: string, improvements: Improvement[]): Promise<boolean> {
    try {
      let content = await fs.readFile(file, 'utf-8');
      const lines = content.split('\n');

      // Apply improvements in reverse order to maintain line numbers
      const sortedImprovements = improvements.sort((a, b) => b.location.line - a.location.line);

      for (const improvement of sortedImprovements) {
        const lineIndex = improvement.location.line - 1;
        if (lineIndex >= 0 && lineIndex < lines.length) {
          lines[lineIndex] = improvement.suggested;
        }
      }

      const modifiedContent = lines.join('\n');
      await fs.writeFile(file, modifiedContent);
      
      return true;
    } catch (error) {
      return false;
    }
  }

  private generateSummary(results: ImprovementResult[]): string {
    let summary = `Analyzed ${results.length} file(s) for improvements\n\n`;

    let totalImprovements = 0;
    let appliedFiles = 0;
    const categories = new Map<string, number>();
    const impacts = new Map<string, number>();

    for (const result of results) {
      totalImprovements += result.improvements.length;
      if (result.applied) appliedFiles++;

      for (const improvement of result.improvements) {
        categories.set(improvement.category, (categories.get(improvement.category) || 0) + 1);
        impacts.set(improvement.impact, (impacts.get(improvement.impact) || 0) + 1);
      }
    }

    summary += `Total improvements found: ${totalImprovements}\n`;
    
    if (appliedFiles > 0) {
      summary += `Applied improvements to: ${appliedFiles} file(s)\n`;
    }

    if (categories.size > 0) {
      summary += `\nBy category:\n`;
      for (const [category, count] of categories.entries()) {
        summary += `- ${category}: ${count}\n`;
      }
    }

    if (impacts.size > 0) {
      summary += `\nBy impact:\n`;
      for (const [impact, count] of impacts.entries()) {
        summary += `- ${impact}: ${count}\n`;
      }
    }

    return summary;
  }
}