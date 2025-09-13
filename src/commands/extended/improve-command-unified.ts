/**
 * Unified Improve Command for ae-framework
 * Provides code improvements and refactoring suggestions with unified interface
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as ts from 'typescript';
import { BaseExtendedCommand } from './base-command.js';
import type { ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import type { 
  ImprovementResult, 
  AnalysisTarget, 
  ImprovementOptions,
  Improvement,
  Issue,
  Suggestion
} from './types.js';

export class UnifiedImproveCommand extends BaseExtendedCommand {
  constructor() {
    super({
      name: '/ae:improve',
      description: 'Suggest code improvements and refactoring',
      usage: '/ae:improve <file|directory> [--category=performance|readability|security] [--apply] [--validate]',
      aliases: ['/improve', '/a:improve'],
      category: 'utility'
    });
  }

  protected override validateArgs(args: string[]): { isValid: boolean; message?: string } {
    if (args.length === 0) {
      return {
        isValid: false,
        message: 'Please specify a file or directory to improve'
      };
    }
    return { isValid: true };
  }

  protected override parseOptions(args: string[]): ImprovementOptions {
    const baseOptions = super.parseOptions(args);
    
    const category = args.find(arg => arg.startsWith('--category='))?.split('=')[1];
    const impact = args.find(arg => arg.startsWith('--impact='))?.split('=')[1] as any;
    return {
      ...baseOptions,
      ...(category ? { category } : {}),
      ...(impact ? { impact } : {}),
      apply: args.includes('--apply'),
      interactive: args.includes('--interactive')
    };
  }

  protected override async execute(
    args: string[], 
    options: ImprovementOptions, 
    context: CommandContext
  ): Promise<ExtendedCommandResult<ImprovementResult>> {
    const target = args[0];
    if (!target) {
      throw new Error('Target path is required');
    }
    const fullPath = path.resolve(context.projectRoot, target);
    
    try {
      const stats = await fs.stat(fullPath);
      const analysisTarget: AnalysisTarget = {
        path: fullPath,
        type: stats.isDirectory() ? 'directory' : 'file'
      };

      const result = await this.analyzeForImprovements(analysisTarget, options);
      const summary = this.generateSummary(result);

      return {
        success: true,
        message: summary,
        data: result,
        metrics: {
          executionTime: 0, // Will be set by base class
          filesProcessed: result.metrics.files,
          confidence: this.calculateOverallConfidence(result)
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Code improvement analysis failed: ${error.message}`,
        metrics: {
          executionTime: 0,
          filesProcessed: 0
        }
      };
    }
  }

  private async analyzeForImprovements(target: AnalysisTarget, options: ImprovementOptions): Promise<ImprovementResult> {
    const startTime = Date.now();
    
    let files: string[] = [];
    if (target.type === 'directory') {
      files = await this.findSourceFiles(target.path);
    } else {
      files = [target.path];
    }

    const improvements: Improvement[] = [];
    const issues: Issue[] = [];
    const suggestions: Suggestion[] = [];
    let totalLines = 0;
    let appliedCount = 0;

    // Process each file
    for (const file of files) {
      const fileAnalysis = await this.analyzeFile(file, options);
      
      improvements.push(...fileAnalysis.improvements);
      issues.push(...fileAnalysis.issues);
      suggestions.push(...fileAnalysis.suggestions);
      totalLines += fileAnalysis.metrics.lines;

      // Apply improvements if requested
      if (options.apply && !options.dryRun) {
        appliedCount += await this.applyImprovements(file, fileAnalysis.improvements);
      }
    }

    // Calculate estimated impact
    const estimatedImpact = this.calculateEstimatedImpact(improvements);

    return {
      target,
      summary: this.createImprovementSummary(improvements.length, appliedCount, files.length),
      issues,
      suggestions,
      metrics: {
        lines: totalLines,
        files: files.length,
        complexity: this.calculateComplexityMetric(improvements)
      },
      metadata: {
        timestamp: new Date().toISOString(),
        commandType: 'improve',
        processingTime: Date.now() - startTime
      },
      improvements,
      appliedCount,
      estimatedImpact
    };
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

  private async analyzeFile(filePath: string, options: ImprovementOptions): Promise<{
    improvements: Improvement[];
    issues: Issue[];
    suggestions: Suggestion[];
    metrics: { lines: number };
  }> {
    const content = await fs.readFile(filePath, 'utf-8');
    const lines = content.split('\n');
    
    const improvements: Improvement[] = [];
    const issues: Issue[] = [];
    const suggestions: Suggestion[] = [];

    // Pattern-based improvements
    const patternImprovements = this.analyzePatterns(content, filePath);
    improvements.push(...patternImprovements);

    // Security improvements
    const securityImprovements = this.analyzeSecurityPatterns(content, filePath);
    improvements.push(...securityImprovements);

    // Performance improvements
    const performanceImprovements = this.analyzePerformancePatterns(content, filePath);
    improvements.push(...performanceImprovements);

    // Modernization improvements
    const modernizationImprovements = this.analyzeModernizationPatterns(content, filePath);
    improvements.push(...modernizationImprovements);

    // TypeScript specific improvements
    if (filePath.endsWith('.ts')) {
      const tsImprovements = await this.analyzeTypeScriptPatterns(content, filePath);
      improvements.push(...tsImprovements);
    }

    // Filter by category if specified
    const filteredImprovements = options.category 
      ? improvements.filter(imp => imp.category === options.category)
      : improvements;

    // Filter by impact if specified
    const finalImprovements = options.impact 
      ? filteredImprovements.filter(imp => imp.impact === options.impact)
      : filteredImprovements;

    return {
      improvements: finalImprovements,
      issues,
      suggestions,
      metrics: {
        lines: lines.length
      }
    };
  }

  private analyzePatterns(content: string, filePath: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // var -> const/let
      if (line.includes('var ')) {
        const match = line.match(/var\s+(\w+)/);
        if (match) {
          improvements.push({
            type: 'modernize',
            description: `Replace 'var' with 'const' or 'let' for better scoping`,
            location: { line: index + 1 },
            original: line.trim(),
            suggested: line.replace(/\bvar\b/, 'const'),
            impact: 'medium',
            category: 'best-practice',
            confidence: 0.9
          });
        }
      }

      // == -> ===
      if (line.includes('==') && !line.includes('===') && !line.includes('!==')) {
        improvements.push({
          type: 'modernize',
          description: 'Use strict equality (===) instead of loose equality (==)',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: line.replace(/\b==\b/g, '===').replace(/\b!=\b/g, '!=='),
          impact: 'low',
          category: 'best-practice',
          confidence: 0.95
        });
      }

      // Function declarations -> arrow functions (for simple cases)
      const funcMatch = line.match(/function\s+(\w+)\s*\([^)]*\)\s*{/);
      if (funcMatch && line.includes('return ') && lines[index + 1]?.trim() === '}') {
        improvements.push({
          type: 'modernize',
          description: 'Consider using arrow function syntax for concise functions',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: `const ${funcMatch[1]} = (${line.match(/\(([^)]*)\)/)?.[1] || ''}) => {`,
          impact: 'low',
          category: 'readability',
          confidence: 0.7
        });
      }

      // Console.log removal
      if (line.includes('console.log') && !line.includes('//')) {
        improvements.push({
          type: 'optimize',
          description: 'Remove console.log statement for production code',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: '// ' + line.trim(),
          impact: 'low',
          category: 'maintainability',
          confidence: 0.8
        });
      }
    });

    return improvements;
  }

  private analyzeSecurityPatterns(content: string, filePath: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // eval() usage
      if (line.includes('eval(')) {
        improvements.push({
          type: 'security',
          description: 'Avoid using eval() - it poses security risks',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: '// Consider safer alternatives to eval()',
          impact: 'high',
          category: 'security',
          confidence: 0.95
        });
      }

      // innerHTML usage
      if (line.includes('innerHTML') && !line.includes('textContent')) {
        improvements.push({
          type: 'security',
          description: 'Consider using textContent instead of innerHTML to prevent XSS',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: line.replace('innerHTML', 'textContent'),
          impact: 'high',
          category: 'security',
          confidence: 0.8
        });
      }

      // Hardcoded secrets
      if (line.match(/(?:api[_-]?key|password|secret|token)\s*[:=]\s*['"][^'"]{8,}/i)) {
        improvements.push({
          type: 'security',
          description: 'Move hardcoded secrets to environment variables',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: '// Use environment variables: process.env.API_KEY',
          impact: 'high',
          category: 'security',
          confidence: 0.9
        });
      }
    });

    return improvements;
  }

  private analyzePerformancePatterns(content: string, filePath: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Inefficient array operations
      if (line.includes('.forEach(') && content.includes('for (')) {
        improvements.push({
          type: 'optimize',
          description: 'Consider using for loops for better performance with large datasets',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: '// Consider using for loop for better performance',
          impact: 'low',
          category: 'performance',
          confidence: 0.6
        });
      }

      // Multiple DOM queries
      if (line.includes('document.querySelector') || line.includes('document.getElementById')) {
        const selector = line.match(/querySelector\(['"]([^'"]+)['"]\)|getElementById\(['"]([^'"]+)['"]\)/);
        if (selector) {
          improvements.push({
            type: 'optimize',
            description: 'Cache DOM queries in variables for better performance',
            location: { line: index + 1 },
            original: line.trim(),
            suggested: `const element = ${line.match(/(document\.[^;]+)/)?.[1] || line.trim()};`,
            impact: 'medium',
            category: 'performance',
            confidence: 0.7
          });
        }
      }

      // Nested loops
      if (line.match(/for\s*\([^)]+\)\s*{/) && 
          lines.slice(index, index + 10).some(l => l.match(/for\s*\([^)]+\)\s*{/))) {
        improvements.push({
          type: 'refactor',
          description: 'Nested loops detected - consider optimization or refactoring',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: '// Consider breaking into separate functions or using more efficient algorithms',
          impact: 'medium',
          category: 'performance',
          confidence: 0.8
        });
      }
    });

    return improvements;
  }

  private analyzeModernizationPatterns(content: string, filePath: string): Improvement[] {
    const improvements: Improvement[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Callbacks -> async/await
      if (line.includes('callback') && (line.includes('function') || line.includes('=>'))) {
        improvements.push({
          type: 'modernize',
          description: 'Consider using async/await instead of callbacks',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: '// Convert to async/await pattern for better readability',
          impact: 'medium',
          category: 'readability',
          confidence: 0.6
        });
      }

      // String concatenation -> template literals
      if (line.includes(' + ') && line.includes('"') && line.includes('\'')) {
        improvements.push({
          type: 'modernize',
          description: 'Use template literals instead of string concatenation',
          location: { line: index + 1 },
          original: line.trim(),
          suggested: '// Use `template ${variable} literals` instead',
          impact: 'low',
          category: 'readability',
          confidence: 0.8
        });
      }

      // require -> import
      if (line.includes('require(') && !line.includes('//')) {
        const match = line.match(/(?:const|let|var)\s+(\w+)\s*=\s*require\(['"]([^'"]+)['"]\)/);
        if (match) {
          improvements.push({
            type: 'modernize',
            description: 'Use ES6 import instead of require',
            location: { line: index + 1 },
            original: line.trim(),
            suggested: `import ${match[1]} from '${match[2]}';`,
            impact: 'low',
            category: 'best-practice',
            confidence: 0.9
          });
        }
      }
    });

    return improvements;
  }

  private async analyzeTypeScriptPatterns(content: string, filePath: string): Promise<Improvement[]> {
    const improvements: Improvement[] = [];

    try {
      const sourceFile = ts.createSourceFile(
        filePath,
        content,
        ts.ScriptTarget.Latest,
        true
      );

      const visit = (node: ts.Node) => {
        // any type usage
        if (ts.isTypeReferenceNode(node) && node.typeName.getText() === 'any') {
          const { line } = sourceFile.getLineAndCharacterOfPosition(node.getStart());
          improvements.push({
            type: 'refactor',
            description: 'Replace "any" type with more specific types',
            location: { line: line + 1 },
            original: 'any',
            suggested: '// Use specific type instead of any',
            impact: 'medium',
            category: 'maintainability',
            confidence: 0.8
          });
        }

        // Non-null assertions
        if (node.kind === ts.SyntaxKind.NonNullExpression) {
          const { line } = sourceFile.getLineAndCharacterOfPosition(node.getStart());
          improvements.push({
            type: 'refactor',
            description: 'Consider proper null checking instead of non-null assertion',
            location: { line: line + 1 },
            original: node.getText(),
            suggested: '// Add proper null/undefined check',
            impact: 'medium',
            category: 'maintainability',
            confidence: 0.7
          });
        }

        ts.forEachChild(node, visit);
      };

      visit(sourceFile);
    } catch (error) {
      // TypeScript analysis failed, continue without TS-specific improvements
    }

    return improvements;
  }

  private async applyImprovements(filePath: string, improvements: Improvement[]): Promise<number> {
    if (improvements.length === 0) return 0;

    // This is a simplified version - in practice, you'd want to be more careful about applying changes
    // and handle potential conflicts between improvements
    let applied = 0;
    
    try {
      const content = await fs.readFile(filePath, 'utf-8');
      let modifiedContent = content;
      const lines = content.split('\n');

      // Sort improvements by line number (descending) to avoid index shifting
      const sortedImprovements = improvements
        .filter(imp => imp.confidence > 0.8) // Only apply high-confidence improvements
        .sort((a, b) => b.location.line - a.location.line);

      for (const improvement of sortedImprovements) {
        const lineIndex = improvement.location.line - 1;
        if (lineIndex >= 0 && lineIndex < lines.length) {
          const originalLine = lines[lineIndex];
          if (originalLine && originalLine.trim() === improvement.original.trim()) {
            lines[lineIndex] = originalLine.replace(improvement.original.trim(), improvement.suggested);
            applied++;
          }
        }
      }

      if (applied > 0) {
        modifiedContent = lines.join('\n');
        await fs.writeFile(filePath, modifiedContent);
      }
    } catch (error) {
      // Failed to apply improvements, continue without error
    }

    return applied;
  }

  private calculateEstimatedImpact(improvements: Improvement[]): string {
    const highImpact = improvements.filter(imp => imp.impact === 'high').length;
    const mediumImpact = improvements.filter(imp => imp.impact === 'medium').length;
    const lowImpact = improvements.filter(imp => imp.impact === 'low').length;

    if (highImpact > 0) return 'High - significant performance or security improvements';
    if (mediumImpact > 0) return 'Medium - noticeable code quality improvements';
    if (lowImpact > 0) return 'Low - minor readability and maintainability improvements';
    return 'None - no improvements found';
  }

  private calculateComplexityMetric(improvements: Improvement[]): number {
    // Simple complexity based on number and type of improvements
    return improvements.reduce((total, imp) => {
      switch (imp.impact) {
        case 'high': return total + 3;
        case 'medium': return total + 2;
        case 'low': return total + 1;
        default: return total;
      }
    }, 0);
  }

  private calculateOverallConfidence(result: ImprovementResult): number {
    if (result.improvements.length === 0) return 1.0;
    
    const avgConfidence = result.improvements.reduce((sum, imp) => sum + imp.confidence, 0) / result.improvements.length;
    return avgConfidence;
  }

  private createImprovementSummary(improvementCount: number, appliedCount: number, fileCount: number): string {
    let summary = `Found ${improvementCount} improvement(s) across ${fileCount} file(s)`;
    if (appliedCount > 0) {
      summary += ` (${appliedCount} applied)`;
    }
    return summary;
  }

  protected override generateValidationClaim(data: ImprovementResult): string {
    return `Code improvement analysis for ${data.target.path}: ${data.improvements.length} improvements identified with estimated ${data.estimatedImpact.toLowerCase()} impact`;
  }

  protected override generateSummary(data: ImprovementResult): string {
    return data.summary;
  }
}
