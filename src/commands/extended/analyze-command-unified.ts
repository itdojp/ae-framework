/**
 * Unified Analyze Command for ae-framework
 * Provides deep code analysis with unified interface
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as ts from 'typescript';
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { 
  CodeAnalysis, 
  AnalysisTarget, 
  AnalysisOptions,
  Issue,
  Suggestion,
  Metrics 
} from './types.js';

export class UnifiedAnalyzeCommand extends BaseExtendedCommand {
  constructor() {
    super({
      name: '/ae:analyze',
      description: 'Deep code analysis with multiple perspectives',
      usage: '/ae:analyze <file|directory> [--depth=shallow|normal|deep] [--security] [--performance] [--validate]',
      aliases: ['/analyze', '/a:analyze'],
      category: 'utility'
    });
  }

  protected validateArgs(args: string[]): { isValid: boolean; message?: string } {
    if (args.length === 0) {
      return {
        isValid: false,
        message: 'Please specify a file or directory to analyze'
      };
    }
    return { isValid: true };
  }

  protected parseOptions(args: string[]): AnalysisOptions {
    const baseOptions = super.parseOptions(args);
    
    return {
      ...baseOptions,
      depth: (args.find(arg => arg.startsWith('--depth='))?.split('=')[1] as any) || 'normal',
      includeTests: args.includes('--include-tests'),
      includeSecurity: args.includes('--security'),
      includePerformance: args.includes('--performance'),
      minConfidence: parseFloat(args.find(arg => arg.startsWith('--confidence='))?.split('=')[1] || '0.7')
    };
  }

  protected async execute(
    args: string[], 
    options: AnalysisOptions, 
    context: CommandContext
  ): Promise<ExtendedCommandResult<CodeAnalysis>> {
    const target = args[0];
    if (!target) {
      throw new Error('Target path is required for analysis');
    }
    const fullPath = path.resolve(context.projectRoot, target);
    
    try {
      const stats = await fs.stat(fullPath);
      const analysisTarget: AnalysisTarget = {
        path: fullPath,
        type: stats.isDirectory() ? 'directory' : 'file'
      };

      const result = await this.performAnalysis(analysisTarget, options);
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
        message: `Analysis failed: ${error.message}`,
        metrics: {
          executionTime: 0,
          filesProcessed: 0
        }
      };
    }
  }

  private async performAnalysis(target: AnalysisTarget, options: AnalysisOptions): Promise<CodeAnalysis> {
    const startTime = Date.now();
    
    let files: string[] = [];
    if (target.type === 'directory') {
      files = await this.findSourceFiles(target.path, options.includeTests || false);
    } else {
      files = [target.path];
    }

    const issues: Issue[] = [];
    const suggestions: Suggestion[] = [];
    const securityIssues: Issue[] = [];
    const performanceIssues: Issue[] = [];
    
    let totalLines = 0;
    let totalFunctions = 0;
    let totalClasses = 0;
    let totalComplexity = 0;
    const dependencies = new Set<string>();

    // Process each file
    for (const file of files) {
      const analysis = await this.analyzeFile(file, options);
      
      issues.push(...analysis.issues);
      suggestions.push(...analysis.suggestions);
      
      if (options.includeSecurity) {
        securityIssues.push(...analysis.securityIssues);
      }
      
      if (options.includePerformance) {
        performanceIssues.push(...analysis.performanceIssues);
      }
      
      totalLines += analysis.metrics.lines;
      totalFunctions += analysis.codeMetrics.functions;
      totalClasses += analysis.codeMetrics.classes;
      totalComplexity += analysis.codeMetrics.cyclomaticComplexity;
      
      analysis.codeMetrics.dependencies.forEach((dep: string) => dependencies.add(dep));
    }

    return {
      target,
      summary: this.createSummary(files.length, issues.length, suggestions.length),
      issues,
      suggestions,
      metrics: {
        lines: totalLines,
        files: files.length,
        complexity: totalComplexity / files.length
      },
      metadata: {
        timestamp: new Date().toISOString(),
        commandType: 'analyze',
        processingTime: Date.now() - startTime
      },
      codeMetrics: {
        functions: totalFunctions,
        classes: totalClasses,
        dependencies: Array.from(dependencies),
        cyclomaticComplexity: totalComplexity,
        cognitiveComplexity: this.calculateCognitiveComplexity(issues)
      },
      securityIssues,
      performanceIssues
    };
  }

  private async analyzeFile(filePath: string, options: AnalysisOptions): Promise<{
    issues: Issue[];
    suggestions: Suggestion[];
    securityIssues: Issue[];
    performanceIssues: Issue[];
    metrics: Metrics;
    codeMetrics: any;
  }> {
    const content = await fs.readFile(filePath, 'utf-8');
    const lines = content.split('\n');
    
    const issues: Issue[] = [];
    const suggestions: Suggestion[] = [];
    const securityIssues: Issue[] = [];
    const performanceIssues: Issue[] = [];

    // Basic code analysis
    const basicAnalysis = this.performBasicAnalysis(content, filePath);
    issues.push(...basicAnalysis.issues);
    suggestions.push(...basicAnalysis.suggestions);

    // Security analysis
    if (options.includeSecurity) {
      const secAnalysis = this.performSecurityAnalysis(content, filePath);
      securityIssues.push(...secAnalysis);
    }

    // Performance analysis
    if (options.includePerformance) {
      const perfAnalysis = this.performPerformanceAnalysis(content, filePath);
      performanceIssues.push(...perfAnalysis);
    }

    // TypeScript analysis if applicable
    if (filePath.endsWith('.ts')) {
      const tsAnalysis = await this.performTypeScriptAnalysis(content, filePath);
      issues.push(...tsAnalysis);
    }

    const codeMetrics = this.calculateCodeMetrics(content);

    return {
      issues,
      suggestions,
      securityIssues,
      performanceIssues,
      metrics: {
        lines: lines.length,
        files: 1,
        complexity: codeMetrics.cyclomaticComplexity
      },
      codeMetrics
    };
  }

  private performBasicAnalysis(content: string, filePath: string): {
    issues: Issue[];
    suggestions: Suggestion[];
  } {
    const issues: Issue[] = [];
    const suggestions: Suggestion[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Check for common issues
      if (line.includes('console.log')) {
        issues.push({
          type: 'debug-code',
          severity: 'low',
          message: 'Console.log statement found',
          location: { file: filePath, line: index + 1 }
        });
      }

      if (line.includes('TODO') || line.includes('FIXME')) {
        issues.push({
          type: 'incomplete-code',
          severity: 'info',
          message: 'TODO/FIXME comment found',
          location: { file: filePath, line: index + 1 }
        });
      }

      if (line.includes(': any')) {
        suggestions.push({
          type: 'type-improvement',
          message: 'Consider using specific types instead of "any"',
          priority: 'medium',
          category: 'type-safety'
        });
      }
    });

    return { issues, suggestions };
  }

  private performSecurityAnalysis(content: string, filePath: string): Issue[] {
    const issues: Issue[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Check for potential security issues
      if (line.includes('eval(')) {
        issues.push({
          type: 'security-risk',
          severity: 'critical',
          message: 'Use of eval() detected - potential security risk',
          location: { file: filePath, line: index + 1 }
        });
      }

      if (line.match(/api[_-]?key|password|secret|token/i) && line.includes('=')) {
        issues.push({
          type: 'hardcoded-secret',
          severity: 'high',
          message: 'Potential hardcoded secret detected',
          location: { file: filePath, line: index + 1 }
        });
      }

      if (line.includes('innerHTML') || line.includes('dangerouslySetInnerHTML')) {
        issues.push({
          type: 'xss-risk',
          severity: 'high',
          message: 'Potential XSS vulnerability',
          location: { file: filePath, line: index + 1 }
        });
      }
    });

    return issues;
  }

  private performPerformanceAnalysis(content: string, filePath: string): Issue[] {
    const issues: Issue[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Check for performance issues
      if (line.includes('.forEach(') && content.includes('for (')) {
        issues.push({
          type: 'performance-inefficiency',
          severity: 'low',
          message: 'Consider using for loops for better performance',
          location: { file: filePath, line: index + 1 }
        });
      }

      if (line.match(/for.*for|while.*while/)) {
        issues.push({
          type: 'nested-loops',
          severity: 'medium',
          message: 'Nested loops detected - consider optimization',
          location: { file: filePath, line: index + 1 }
        });
      }
    });

    return issues;
  }

  private async performTypeScriptAnalysis(content: string, filePath: string): Promise<Issue[]> {
    const issues: Issue[] = [];

    try {
      const sourceFile = ts.createSourceFile(
        filePath,
        content,
        ts.ScriptTarget.Latest,
        true
      );

      const program = ts.createProgram([filePath], {
        noEmit: true,
        strict: true
      });

      const diagnostics = ts.getPreEmitDiagnostics(program);

      diagnostics.forEach(diagnostic => {
        if (diagnostic.file && diagnostic.start !== undefined) {
          const { line, character } = diagnostic.file.getLineAndCharacterOfPosition(diagnostic.start);
          issues.push({
            type: 'typescript-error',
            severity: 'high',
            message: ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n'),
            location: { file: filePath, line: line + 1, column: character + 1 }
          });
        }
      });
    } catch (error) {
      // TypeScript analysis failed, but continue
    }

    return issues;
  }

  private calculateCodeMetrics(content: string) {
    const lines = content.split('\n');
    const functions = (content.match(/function\s+\w+|=>\s*{|async\s+\w+/g) || []).length;
    const classes = (content.match(/class\s+\w+/g) || []).length;
    const dependencies = this.extractDependencies(content);
    
    return {
      functions,
      classes,
      dependencies,
      cyclomaticComplexity: this.calculateCyclomaticComplexity(content),
      cognitiveComplexity: this.calculateFileCognitiveComplexity(content)
    };
  }

  private extractDependencies(content: string): string[] {
    const dependencies: Set<string> = new Set();
    const importPattern = /import\s+.*?\s+from\s+['"]([^'"]+)['"]/g;
    const requirePattern = /require\s*\(['"]([^'"]+)['"]\)/g;
    
    let match;
    while ((match = importPattern.exec(content)) !== null) {
      if (match[1]) {
        dependencies.add(match[1]);
      }
    }
    while ((match = requirePattern.exec(content)) !== null) {
      if (match[1]) {
        dependencies.add(match[1]);
      }
    }

    return Array.from(dependencies);
  }

  private calculateCyclomaticComplexity(content: string): number {
    let complexity = 1;
    const patterns = [
      /if\s*\(/g, /for\s*\(/g, /while\s*\(/g, /case\s+/g,
      /catch\s*\(/g, /\?\s*[^:]+:/g, /&&/g, /\|\|/g
    ];

    patterns.forEach(pattern => {
      const matches = content.match(pattern);
      if (matches) complexity += matches.length;
    });

    return complexity;
  }

  private calculateCognitiveComplexity(issues: Issue[]): number {
    return issues.filter(issue => 
      ['nested-loops', 'complex-condition'].includes(issue.type)
    ).length * 2;
  }

  private calculateFileCognitiveComplexity(content: string): number {
    let complexity = 0;
    let nestingLevel = 0;
    const lines = content.split('\n');
    
    lines.forEach(line => {
      if (line.includes('{')) nestingLevel++;
      if (line.includes('}')) nestingLevel = Math.max(0, nestingLevel - 1);
      
      if (line.match(/if\s*\(|for\s*\(|while\s*\(/)) {
        complexity += 1 + nestingLevel;
      }
    });
    
    return complexity;
  }

  private async findSourceFiles(dir: string, includeTests: boolean): Promise<string[]> {
    const files: string[] = [];
    const entries = await fs.readdir(dir, { withFileTypes: true });

    for (const entry of entries) {
      const fullPath = path.join(dir, entry.name);
      
      if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
        const subFiles = await this.findSourceFiles(fullPath, includeTests);
        files.push(...subFiles);
      } else if (entry.isFile()) {
        const isSourceFile = entry.name.endsWith('.ts') || entry.name.endsWith('.js');
        const isTestFile = entry.name.includes('.test.') || entry.name.includes('.spec.');
        
        if (isSourceFile && (includeTests || !isTestFile)) {
          files.push(fullPath);
        }
      }
    }

    return files;
  }

  private calculateOverallConfidence(result: CodeAnalysis): number {
    const criticalIssues = result.issues.filter(i => i.severity === 'critical').length;
    const highIssues = result.issues.filter(i => i.severity === 'high').length;
    
    if (criticalIssues > 0) return 0.3;
    if (highIssues > 3) return 0.5;
    return 0.8;
  }

  private createSummary(fileCount: number, issueCount: number, suggestionCount: number): string {
    return `Analyzed ${fileCount} file(s), found ${issueCount} issues and ${suggestionCount} suggestions`;
  }

  protected generateValidationClaim(data: CodeAnalysis): string {
    return `Code analysis findings for ${data.target.path}: ${data.issues.length} issues detected`;
  }

  protected generateSummary(data: CodeAnalysis): string {
    return data.summary;
  }
}