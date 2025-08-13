/**
 * Analyze Command for ae-framework
 * Provides deep code analysis with metrics, issues, and complexity assessment
 */

import * as ts from 'typescript';
import * as fs from 'fs/promises';
import * as path from 'path';
import { exec } from 'child_process';
import { promisify } from 'util';
import type { CommandResult, CommandContext } from '../slash-command-manager.js';
import { EvidenceValidator } from '../../utils/evidence-validator.js';

const execAsync = promisify(exec);

export interface AnalysisResult {
  file: string;
  metrics: CodeMetrics;
  issues: CodeIssue[];
  complexity: ComplexityAnalysis;
  security: SecurityAnalysis;
  performance: PerformanceAnalysis;
  suggestions: string[];
  evidence?: any;
}

export interface CodeMetrics {
  lines: number;
  functions: number;
  classes: number;
  complexity: number;
  dependencies: string[];
  coverage?: number;
}

export interface CodeIssue {
  type: 'error' | 'warning' | 'info';
  line: number;
  column: number;
  message: string;
  rule?: string;
  severity: 'critical' | 'major' | 'minor' | 'info';
}

export interface ComplexityAnalysis {
  cyclomatic: number;
  cognitive: number;
  nesting: number;
  coupling: number;
  cohesion: number;
}

export interface SecurityAnalysis {
  vulnerabilities: SecurityVulnerability[];
  score: number;
  recommendations: string[];
}

export interface SecurityVulnerability {
  type: string;
  severity: 'critical' | 'high' | 'medium' | 'low';
  location: { line: number; column: number };
  description: string;
  fix?: string;
}

export interface PerformanceAnalysis {
  bottlenecks: PerformanceBottleneck[];
  optimizations: string[];
  estimatedGains: string;
}

export interface PerformanceBottleneck {
  type: string;
  location: { line: number; column: number };
  impact: 'high' | 'medium' | 'low';
  description: string;
}

export class AnalyzeCommand {
  name = '/ae:analyze';
  description = 'Deep code analysis with multiple perspectives';
  category = 'utility' as const;
  usage = '/ae:analyze <file|directory> [options]';
  aliases = ['/analyze', '/a:analyze'];
  
  private validator: EvidenceValidator;

  constructor() {
    this.validator = new EvidenceValidator();
  }

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a file or directory to analyze'
      };
    }

    const target = args[0];
    const options = this.parseOptions(args.slice(1));

    try {
      const results = await this.analyze(target, options);
      const summary = this.generateSummary(results);

      // Validate findings with evidence
      if (options.validateFindings) {
        for (const result of results) {
          const validation = await this.validator.validateClaim(
            `Code analysis findings for ${result.file}`,
            JSON.stringify(result.issues),
            { minConfidence: 0.7 }
          );
          result.evidence = validation;
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
        message: `Analysis failed: ${error.message}`
      };
    }
  }

  private parseOptions(args: string[]): any {
    const options: any = {
      depth: 'full',
      includeTests: false,
      validateFindings: false
    };

    for (let i = 0; i < args.length; i++) {
      switch (args[i]) {
        case '--depth':
          options.depth = args[++i] || 'full';
          break;
        case '--include-tests':
          options.includeTests = true;
          break;
        case '--validate':
          options.validateFindings = true;
          break;
      }
    }

    return options;
  }

  private async analyze(target: string, options: any): Promise<AnalysisResult[]> {
    const results: AnalysisResult[] = [];
    const stats = await fs.stat(target);

    if (stats.isDirectory()) {
      const files = await this.findSourceFiles(target, options.includeTests);
      for (const file of files) {
        const result = await this.analyzeFile(file, options);
        results.push(result);
      }
    } else {
      const result = await this.analyzeFile(target, options);
      results.push(result);
    }

    return results;
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

  private async analyzeFile(file: string, options: any): Promise<AnalysisResult> {
    const content = await fs.readFile(file, 'utf-8');
    
    const metrics = await this.calculateMetrics(content, file);
    const issues = await this.detectIssues(content, file);
    const complexity = this.analyzeComplexity(content);
    const security = await this.analyzeSecurity(content, file);
    const performance = this.analyzePerformance(content);
    const suggestions = this.generateSuggestions(metrics, issues, complexity);

    return {
      file,
      metrics,
      issues,
      complexity,
      security,
      performance,
      suggestions
    };
  }

  private async calculateMetrics(content: string, file: string): Promise<CodeMetrics> {
    const lines = content.split('\n').length;
    const functions = (content.match(/function\s+\w+|=>\s*{|async\s+\w+/g) || []).length;
    const classes = (content.match(/class\s+\w+/g) || []).length;
    
    // Calculate cyclomatic complexity (simplified)
    const complexity = this.calculateCyclomaticComplexity(content);
    
    // Extract dependencies
    const dependencies = this.extractDependencies(content);

    // Try to get coverage if available
    const coverage = await this.getCoverage(file);

    return {
      lines,
      functions,
      classes,
      complexity,
      dependencies,
      coverage
    };
  }

  private calculateCyclomaticComplexity(content: string): number {
    let complexity = 1; // Base complexity
    
    // Count decision points
    const decisionPatterns = [
      /if\s*\(/g,
      /else\s+if\s*\(/g,
      /for\s*\(/g,
      /while\s*\(/g,
      /case\s+/g,
      /catch\s*\(/g,
      /\?\s*[^:]+:/g, // ternary operator
      /&&/g,
      /\|\|/g
    ];

    for (const pattern of decisionPatterns) {
      const matches = content.match(pattern);
      if (matches) {
        complexity += matches.length;
      }
    }

    return complexity;
  }

  private extractDependencies(content: string): string[] {
    const dependencies: Set<string> = new Set();
    
    // Extract import statements
    const importPattern = /import\s+.*?\s+from\s+['"]([^'"]+)['"]/g;
    const requirePattern = /require\s*\(['"]([^'"]+)['"]\)/g;
    
    let match;
    while ((match = importPattern.exec(content)) !== null) {
      dependencies.add(match[1]);
    }
    while ((match = requirePattern.exec(content)) !== null) {
      dependencies.add(match[1]);
    }

    return Array.from(dependencies);
  }

  private async getCoverage(file: string): Promise<number | undefined> {
    try {
      // Try to read coverage report if it exists
      const coverageFile = path.join(process.cwd(), 'coverage', 'coverage-summary.json');
      const coverage = await fs.readFile(coverageFile, 'utf-8');
      const data = JSON.parse(coverage);
      
      const relativeFile = path.relative(process.cwd(), file);
      if (data[relativeFile]) {
        return data[relativeFile].lines.pct;
      }
    } catch {
      // Coverage not available
    }
    
    return undefined;
  }

  private async detectIssues(content: string, file: string): Promise<CodeIssue[]> {
    const issues: CodeIssue[] = [];
    const lines = content.split('\n');

    // Check for common issues
    lines.forEach((line, index) => {
      // Check for console.log
      if (line.includes('console.log')) {
        issues.push({
          type: 'warning',
          line: index + 1,
          column: line.indexOf('console.log'),
          message: 'Remove console.log statement',
          rule: 'no-console',
          severity: 'minor'
        });
      }

      // Check for TODO comments
      if (line.includes('TODO') || line.includes('FIXME')) {
        issues.push({
          type: 'info',
          line: index + 1,
          column: 0,
          message: 'Unresolved TODO/FIXME comment',
          rule: 'no-todo',
          severity: 'info'
        });
      }

      // Check for any type
      if (line.includes(': any')) {
        issues.push({
          type: 'warning',
          line: index + 1,
          column: line.indexOf(': any'),
          message: 'Avoid using "any" type',
          rule: 'no-any',
          severity: 'major'
        });
      }

      // Check for hardcoded secrets (simplified)
      if (line.match(/api[_-]?key|password|secret|token/i) && line.includes('=') && line.includes('"')) {
        issues.push({
          type: 'error',
          line: index + 1,
          column: 0,
          message: 'Potential hardcoded secret detected',
          rule: 'no-secrets',
          severity: 'critical'
        });
      }
    });

    // Try to run TypeScript compiler for type checking
    if (file.endsWith('.ts')) {
      const tsIssues = await this.runTypeScriptCheck(file);
      issues.push(...tsIssues);
    }

    return issues;
  }

  private async runTypeScriptCheck(file: string): Promise<CodeIssue[]> {
    const issues: CodeIssue[] = [];

    try {
      const program = ts.createProgram([file], {
        noEmit: true,
        strict: true,
        target: ts.ScriptTarget.ES2020,
        module: ts.ModuleKind.CommonJS
      });

      const diagnostics = ts.getPreEmitDiagnostics(program);
      
      for (const diagnostic of diagnostics) {
        if (diagnostic.file && diagnostic.start !== undefined) {
          const { line, character } = diagnostic.file.getLineAndCharacterOfPosition(diagnostic.start);
          issues.push({
            type: 'error',
            line: line + 1,
            column: character + 1,
            message: ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n'),
            rule: `ts-${diagnostic.code}`,
            severity: 'major'
          });
        }
      }
    } catch (error) {
      // TypeScript checking failed
    }

    return issues;
  }

  private analyzeComplexity(content: string): ComplexityAnalysis {
    const cyclomatic = this.calculateCyclomaticComplexity(content);
    const cognitive = this.calculateCognitiveComplexity(content);
    const nesting = this.calculateMaxNesting(content);
    const coupling = this.calculateCoupling(content);
    const cohesion = this.calculateCohesion(content);

    return {
      cyclomatic,
      cognitive,
      nesting,
      coupling,
      cohesion
    };
  }

  private calculateCognitiveComplexity(content: string): number {
    let complexity = 0;
    let nestingLevel = 0;
    
    const lines = content.split('\n');
    for (const line of lines) {
      // Increase nesting for control structures
      if (line.includes('{')) {
        nestingLevel++;
      }
      if (line.includes('}')) {
        nestingLevel = Math.max(0, nestingLevel - 1);
      }

      // Add complexity for control flow
      if (line.match(/if\s*\(|for\s*\(|while\s*\(|switch\s*\(/)) {
        complexity += 1 + nestingLevel;
      }
      
      // Add complexity for logical operators
      const logicalOps = (line.match(/&&|\|\|/g) || []).length;
      complexity += logicalOps;
    }

    return complexity;
  }

  private calculateMaxNesting(content: string): number {
    let maxNesting = 0;
    let currentNesting = 0;
    
    const lines = content.split('\n');
    for (const line of lines) {
      if (line.includes('{')) {
        currentNesting++;
        maxNesting = Math.max(maxNesting, currentNesting);
      }
      if (line.includes('}')) {
        currentNesting = Math.max(0, currentNesting - 1);
      }
    }

    return maxNesting;
  }

  private calculateCoupling(content: string): number {
    // Count external dependencies
    const imports = (content.match(/import\s+.*?\s+from/g) || []).length;
    const requires = (content.match(/require\s*\(/g) || []).length;
    
    return imports + requires;
  }

  private calculateCohesion(content: string): number {
    // Simplified cohesion: ratio of internal calls to total functions
    const functions = (content.match(/function\s+\w+|=>\s*{/g) || []).length;
    const internalCalls = (content.match(/this\.\w+\(/g) || []).length;
    
    if (functions === 0) return 1;
    return Math.min(1, internalCalls / functions);
  }

  private async analyzeSecurity(content: string, file: string): Promise<SecurityAnalysis> {
    const vulnerabilities: SecurityVulnerability[] = [];
    const lines = content.split('\n');

    // Check for common security issues
    lines.forEach((line, index) => {
      // SQL Injection risk
      if (line.match(/query\s*\(.*?\+.*?\)/) || line.match(/query\s*\(`.*?\${/)) {
        vulnerabilities.push({
          type: 'SQL Injection',
          severity: 'critical',
          location: { line: index + 1, column: 0 },
          description: 'Potential SQL injection vulnerability',
          fix: 'Use parameterized queries'
        });
      }

      // XSS risk
      if (line.includes('innerHTML') || line.includes('dangerouslySetInnerHTML')) {
        vulnerabilities.push({
          type: 'XSS',
          severity: 'high',
          location: { line: index + 1, column: 0 },
          description: 'Potential XSS vulnerability',
          fix: 'Sanitize user input before rendering'
        });
      }

      // Eval usage
      if (line.includes('eval(')) {
        vulnerabilities.push({
          type: 'Code Injection',
          severity: 'critical',
          location: { line: index + 1, column: line.indexOf('eval(') },
          description: 'Use of eval() is dangerous',
          fix: 'Avoid eval() and use safer alternatives'
        });
      }

      // Weak crypto
      if (line.match(/md5|sha1/i)) {
        vulnerabilities.push({
          type: 'Weak Cryptography',
          severity: 'medium',
          location: { line: index + 1, column: 0 },
          description: 'Weak hashing algorithm detected',
          fix: 'Use SHA-256 or stronger'
        });
      }
    });

    // Calculate security score (0-100)
    const score = Math.max(0, 100 - (vulnerabilities.filter(v => v.severity === 'critical').length * 30) -
                                   (vulnerabilities.filter(v => v.severity === 'high').length * 20) -
                                   (vulnerabilities.filter(v => v.severity === 'medium').length * 10) -
                                   (vulnerabilities.filter(v => v.severity === 'low').length * 5));

    const recommendations = this.generateSecurityRecommendations(vulnerabilities);

    return {
      vulnerabilities,
      score,
      recommendations
    };
  }

  private generateSecurityRecommendations(vulnerabilities: SecurityVulnerability[]): string[] {
    const recommendations: string[] = [];

    if (vulnerabilities.some(v => v.type === 'SQL Injection')) {
      recommendations.push('Use prepared statements or ORM with parameterized queries');
    }

    if (vulnerabilities.some(v => v.type === 'XSS')) {
      recommendations.push('Implement Content Security Policy (CSP)');
      recommendations.push('Use a sanitization library for user input');
    }

    if (vulnerabilities.some(v => v.type === 'Code Injection')) {
      recommendations.push('Never use eval() or Function() with user input');
    }

    if (vulnerabilities.length === 0) {
      recommendations.push('No critical security issues detected');
    }

    return recommendations;
  }

  private analyzePerformance(content: string): PerformanceAnalysis {
    const bottlenecks: PerformanceBottleneck[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Nested loops
      if (line.match(/for.*for|while.*while/)) {
        bottlenecks.push({
          type: 'Nested Loops',
          location: { line: index + 1, column: 0 },
          impact: 'high',
          description: 'Nested loops can cause O(n²) complexity'
        });
      }

      // Synchronous file operations
      if (line.match(/readFileSync|writeFileSync/)) {
        bottlenecks.push({
          type: 'Blocking I/O',
          location: { line: index + 1, column: 0 },
          impact: 'medium',
          description: 'Synchronous file operations block the event loop'
        });
      }

      // Large array operations
      if (line.match(/\.forEach\(|\.map\(|\.filter\(.*\.map\(/)) {
        bottlenecks.push({
          type: 'Array Operations',
          location: { line: index + 1, column: 0 },
          impact: 'low',
          description: 'Consider using for loops for better performance'
        });
      }
    });

    const optimizations = this.generateOptimizations(bottlenecks);
    const estimatedGains = this.estimatePerformanceGains(bottlenecks);

    return {
      bottlenecks,
      optimizations,
      estimatedGains
    };
  }

  private generateOptimizations(bottlenecks: PerformanceBottleneck[]): string[] {
    const optimizations: string[] = [];

    if (bottlenecks.some(b => b.type === 'Nested Loops')) {
      optimizations.push('Consider using hash maps or Sets for O(1) lookups');
      optimizations.push('Optimize algorithm complexity where possible');
    }

    if (bottlenecks.some(b => b.type === 'Blocking I/O')) {
      optimizations.push('Use async/await for file operations');
      optimizations.push('Consider using streams for large files');
    }

    if (bottlenecks.some(b => b.type === 'Array Operations')) {
      optimizations.push('Use traditional for loops for performance-critical code');
      optimizations.push('Consider lazy evaluation for large datasets');
    }

    if (bottlenecks.length === 0) {
      optimizations.push('No significant performance bottlenecks detected');
    }

    return optimizations;
  }

  private estimatePerformanceGains(bottlenecks: PerformanceBottleneck[]): string {
    const highImpact = bottlenecks.filter(b => b.impact === 'high').length;
    const mediumImpact = bottlenecks.filter(b => b.impact === 'medium').length;
    
    if (highImpact > 0) {
      return `Potential ${highImpact * 30}% - ${highImpact * 50}% performance improvement`;
    } else if (mediumImpact > 0) {
      return `Potential ${mediumImpact * 10}% - ${mediumImpact * 20}% performance improvement`;
    } else {
      return 'Minor optimizations possible';
    }
  }

  private generateSuggestions(
    metrics: CodeMetrics,
    issues: CodeIssue[],
    complexity: ComplexityAnalysis
  ): string[] {
    const suggestions: string[] = [];

    // Complexity suggestions
    if (complexity.cyclomatic > 10) {
      suggestions.push('Consider breaking down complex functions');
    }
    if (complexity.nesting > 4) {
      suggestions.push('Reduce nesting levels for better readability');
    }
    if (complexity.coupling > 10) {
      suggestions.push('High coupling detected - consider reducing dependencies');
    }

    // Issue-based suggestions
    const criticalIssues = issues.filter(i => i.severity === 'critical');
    if (criticalIssues.length > 0) {
      suggestions.push(`Fix ${criticalIssues.length} critical issues immediately`);
    }

    // Metric-based suggestions
    if (metrics.functions > 20) {
      suggestions.push('Consider splitting file into smaller modules');
    }
    if (metrics.coverage !== undefined && metrics.coverage < 80) {
      suggestions.push(`Increase test coverage (currently ${metrics.coverage}%)`);
    }

    return suggestions;
  }

  private generateSummary(results: AnalysisResult[]): string {
    let summary = `Analyzed ${results.length} file(s)\n\n`;

    let totalIssues = 0;
    let totalVulnerabilities = 0;
    let totalComplexity = 0;

    for (const result of results) {
      totalIssues += result.issues.length;
      totalVulnerabilities += result.security.vulnerabilities.length;
      totalComplexity += result.complexity.cyclomatic;
    }

    summary += `Total Issues: ${totalIssues}\n`;
    summary += `Security Vulnerabilities: ${totalVulnerabilities}\n`;
    summary += `Average Complexity: ${(totalComplexity / results.length).toFixed(1)}\n`;

    // Add top suggestions
    const allSuggestions = results.flatMap(r => r.suggestions);
    const uniqueSuggestions = [...new Set(allSuggestions)].slice(0, 3);
    if (uniqueSuggestions.length > 0) {
      summary += `\nTop Suggestions:\n${uniqueSuggestions.map(s => `- ${s}`).join('\n')}`;
    }

    return summary;
  }
}