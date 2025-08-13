/**
 * Analyze Command for ae-framework
 * Provides deep code analysis with multiple perspectives
 */

import { CommandHandler, CommandResult, CommandContext } from '../slash-command-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

export class AnalyzeCommand {
  name = '/ae:analyze';
  description = 'Deep code analysis with multiple perspectives';
  category = 'utility' as const;
  usage = '/ae:analyze <file|directory> [options]';
  aliases = ['/analyze', '/a:analyze'];

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
      const analysis = await this.performAnalysis(target, options, context);
      
      return {
        success: true,
        message: this.formatAnalysisReport(analysis),
        data: analysis
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Analysis failed: ${error.message}`
      };
    }
  }

  private async performAnalysis(
    target: string,
    options: Record<string, any>,
    context: CommandContext
  ): Promise<AnalysisReport> {
    const fullPath = path.resolve(context.projectRoot, target);
    const stats = await fs.stat(fullPath);
    
    if (stats.isDirectory()) {
      return this.analyzeDirectory(fullPath, options);
    } else {
      return this.analyzeFile(fullPath, options);
    }
  }

  private async analyzeFile(filePath: string, options: Record<string, any>): Promise<AnalysisReport> {
    const content = await fs.readFile(filePath, 'utf-8');
    const ext = path.extname(filePath);
    
    const report: AnalysisReport = {
      target: filePath,
      type: 'file',
      metrics: await this.calculateMetrics(content, ext),
      issues: await this.detectIssues(content, ext),
      suggestions: await this.generateSuggestions(content, ext),
      complexity: await this.analyzeComplexity(content, ext)
    };

    // Add security analysis if requested
    if (options.security) {
      report.security = await this.analyzeSecuri

ty(content, ext);
    }

    // Add performance analysis if requested
    if (options.performance) {
      report.performance = await this.analyzePerformance(content, ext);
    }

    return report;
  }

  private async analyzeDirectory(dirPath: string, options: Record<string, any>): Promise<AnalysisReport> {
    const files = await this.scanDirectory(dirPath);
    const analyses: AnalysisReport[] = [];

    for (const file of files) {
      if (this.shouldAnalyzeFile(file)) {
        const analysis = await this.analyzeFile(file, options);
        analyses.push(analysis);
      }
    }

    return this.aggregateAnalyses(analyses, dirPath);
  }

  private async calculateMetrics(content: string, ext: string): Promise<CodeMetrics> {
    const lines = content.split('\n');
    const codeLines = lines.filter(line => line.trim() && !line.trim().startsWith('//'));
    const commentLines = lines.filter(line => line.trim().startsWith('//') || line.trim().startsWith('/*'));
    
    return {
      totalLines: lines.length,
      codeLines: codeLines.length,
      commentLines: commentLines.length,
      blankLines: lines.length - codeLines.length - commentLines.length,
      commentRatio: commentLines.length / (lines.length || 1),
      functions: this.countFunctions(content, ext),
      classes: this.countClasses(content, ext),
      imports: this.countImports(content, ext)
    };
  }

  private async detectIssues(content: string, ext: string): Promise<Issue[]> {
    const issues: Issue[] = [];

    // Check for common code smells
    if (content.includes('console.log') && ext === '.ts') {
      issues.push({
        type: 'warning',
        message: 'Console.log statements found in production code',
        line: this.findLineNumber(content, 'console.log'),
        severity: 'low'
      });
    }

    // Check for TODO comments
    const todoMatches = content.match(/\/\/\s*TODO/gi);
    if (todoMatches) {
      issues.push({
        type: 'info',
        message: `${todoMatches.length} TODO comments found`,
        severity: 'info'
      });
    }

    // Check for long functions
    const functions = this.extractFunctions(content, ext);
    for (const func of functions) {
      const lines = func.body.split('\n').length;
      if (lines > 50) {
        issues.push({
          type: 'warning',
          message: `Function ${func.name} is too long (${lines} lines)`,
          line: func.line,
          severity: 'medium'
        });
      }
    }

    // Check for deeply nested code
    const maxNesting = this.calculateMaxNesting(content);
    if (maxNesting > 4) {
      issues.push({
        type: 'warning',
        message: `Deeply nested code detected (max depth: ${maxNesting})`,
        severity: 'medium'
      });
    }

    return issues;
  }

  private async generateSuggestions(content: string, ext: string): Promise<Suggestion[]> {
    const suggestions: Suggestion[] = [];

    // Suggest refactoring for long files
    const lines = content.split('\n').length;
    if (lines > 500) {
      suggestions.push({
        type: 'refactor',
        message: 'Consider splitting this file into smaller modules',
        priority: 'high'
      });
    }

    // Suggest adding types for TypeScript
    if (ext === '.ts' && content.includes(': any')) {
      suggestions.push({
        type: 'type-safety',
        message: 'Replace "any" types with specific types',
        priority: 'medium'
      });
    }

    // Suggest error handling
    if (content.includes('async') && !content.includes('try') && !content.includes('catch')) {
      suggestions.push({
        type: 'error-handling',
        message: 'Add error handling for async operations',
        priority: 'high'
      });
    }

    return suggestions;
  }

  private async analyzeComplexity(content: string, ext: string): Promise<ComplexityMetrics> {
    const functions = this.extractFunctions(content, ext);
    const cyclomaticComplexity = functions.map(f => this.calculateCyclomaticComplexity(f.body));
    
    return {
      cyclomatic: Math.max(...cyclomaticComplexity, 0),
      cognitive: this.calculateCognitiveComplexity(content),
      halstead: this.calculateHalsteadComplexity(content),
      maintainabilityIndex: this.calculateMaintainabilityIndex(content)
    };
  }

  private async analyzeSecurity(content: string, ext: string): Promise<SecurityAnalysis> {
    const vulnerabilities: Vulnerability[] = [];

    // Check for hardcoded secrets
    const secretPatterns = [
      /api[_-]?key\s*=\s*["'][^"']+["']/gi,
      /password\s*=\s*["'][^"']+["']/gi,
      /token\s*=\s*["'][^"']+["']/gi
    ];

    for (const pattern of secretPatterns) {
      if (pattern.test(content)) {
        vulnerabilities.push({
          type: 'hardcoded-secret',
          severity: 'critical',
          message: 'Potential hardcoded secret detected'
        });
      }
    }

    // Check for SQL injection risks
    if (content.includes('query') && content.includes('${')) {
      vulnerabilities.push({
        type: 'sql-injection',
        severity: 'high',
        message: 'Potential SQL injection vulnerability'
      });
    }

    return {
      vulnerabilities,
      score: vulnerabilities.length === 0 ? 100 : Math.max(0, 100 - vulnerabilities.length * 20)
    };
  }

  private async analyzePerformance(content: string, ext: string): Promise<PerformanceAnalysis> {
    const issues: PerformanceIssue[] = [];

    // Check for nested loops
    const nestedLoops = content.match(/for.*\{[\s\S]*?for.*\{/g);
    if (nestedLoops) {
      issues.push({
        type: 'nested-loops',
        impact: 'high',
        message: `${nestedLoops.length} nested loops detected`
      });
    }

    // Check for synchronous file operations
    if (content.includes('readFileSync') || content.includes('writeFileSync')) {
      issues.push({
        type: 'sync-io',
        impact: 'medium',
        message: 'Synchronous file operations detected'
      });
    }

    return {
      issues,
      score: issues.length === 0 ? 100 : Math.max(0, 100 - issues.length * 15)
    };
  }

  // Helper methods
  private parseOptions(args: string[]): Record<string, any> {
    const options: Record<string, any> = {};
    for (const arg of args) {
      if (arg.startsWith('--')) {
        const [key, value] = arg.slice(2).split('=');
        options[key] = value || true;
      }
    }
    return options;
  }

  private async scanDirectory(dirPath: string): Promise<string[]> {
    const files: string[] = [];
    const entries = await fs.readdir(dirPath, { withFileTypes: true });
    
    for (const entry of entries) {
      const fullPath = path.join(dirPath, entry.name);
      if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
        const subFiles = await this.scanDirectory(fullPath);
        files.push(...subFiles);
      } else if (entry.isFile()) {
        files.push(fullPath);
      }
    }
    
    return files;
  }

  private shouldAnalyzeFile(filePath: string): boolean {
    const ext = path.extname(filePath);
    return ['.ts', '.js', '.tsx', '.jsx'].includes(ext);
  }

  private countFunctions(content: string, ext: string): number {
    const functionPatterns = [
      /function\s+\w+/g,
      /const\s+\w+\s*=\s*(?:async\s+)?(?:\([^)]*\)|[^=])\s*=>/g,
      /\w+\s*:\s*(?:async\s+)?(?:\([^)]*\)|[^=])\s*=>/g
    ];
    
    let count = 0;
    for (const pattern of functionPatterns) {
      const matches = content.match(pattern);
      count += matches ? matches.length : 0;
    }
    return count;
  }

  private countClasses(content: string, ext: string): number {
    const matches = content.match(/class\s+\w+/g);
    return matches ? matches.length : 0;
  }

  private countImports(content: string, ext: string): number {
    const matches = content.match(/import\s+.*from/g);
    return matches ? matches.length : 0;
  }

  private findLineNumber(content: string, search: string): number {
    const lines = content.split('\n');
    for (let i = 0; i < lines.length; i++) {
      if (lines[i].includes(search)) {
        return i + 1;
      }
    }
    return 0;
  }

  private extractFunctions(content: string, ext: string): Array<{ name: string; body: string; line: number }> {
    // Simplified function extraction
    const functions: Array<{ name: string; body: string; line: number }> = [];
    const lines = content.split('\n');
    
    for (let i = 0; i < lines.length; i++) {
      if (lines[i].match(/function\s+(\w+)/) || lines[i].match(/const\s+(\w+)\s*=/)) {
        const match = lines[i].match(/(?:function\s+|const\s+)(\w+)/);
        if (match) {
          // Simple heuristic: assume function ends at next function or class
          let endLine = i + 1;
          let braceCount = 0;
          let started = false;
          
          for (let j = i; j < lines.length; j++) {
            if (lines[j].includes('{')) {
              braceCount++;
              started = true;
            }
            if (lines[j].includes('}')) {
              braceCount--;
            }
            if (started && braceCount === 0) {
              endLine = j;
              break;
            }
          }
          
          functions.push({
            name: match[1],
            body: lines.slice(i, endLine + 1).join('\n'),
            line: i + 1
          });
        }
      }
    }
    
    return functions;
  }

  private calculateMaxNesting(content: string): number {
    let maxNesting = 0;
    let currentNesting = 0;
    
    for (const char of content) {
      if (char === '{') {
        currentNesting++;
        maxNesting = Math.max(maxNesting, currentNesting);
      } else if (char === '}') {
        currentNesting = Math.max(0, currentNesting - 1);
      }
    }
    
    return maxNesting;
  }

  private calculateCyclomaticComplexity(code: string): number {
    // Simplified cyclomatic complexity calculation
    const controlFlowKeywords = ['if', 'else', 'for', 'while', 'case', 'catch'];
    let complexity = 1;
    
    for (const keyword of controlFlowKeywords) {
      const regex = new RegExp(`\\b${keyword}\\b`, 'g');
      const matches = code.match(regex);
      complexity += matches ? matches.length : 0;
    }
    
    return complexity;
  }

  private calculateCognitiveComplexity(content: string): number {
    // Simplified cognitive complexity
    let complexity = 0;
    const lines = content.split('\n');
    let nestingLevel = 0;
    
    for (const line of lines) {
      if (line.includes('if') || line.includes('for') || line.includes('while')) {
        complexity += 1 + nestingLevel;
      }
      if (line.includes('{')) nestingLevel++;
      if (line.includes('}')) nestingLevel = Math.max(0, nestingLevel - 1);
    }
    
    return complexity;
  }

  private calculateHalsteadComplexity(content: string): number {
    // Very simplified Halstead complexity
    const operators = content.match(/[+\-*/%=<>!&|]+/g) || [];
    const operands = content.match(/\b\w+\b/g) || [];
    
    const n1 = new Set(operators).size; // Unique operators
    const n2 = new Set(operands).size;  // Unique operands
    const N1 = operators.length;        // Total operators
    const N2 = operands.length;         // Total operands
    
    const vocabulary = n1 + n2;
    const length = N1 + N2;
    const volume = length * Math.log2(vocabulary || 1);
    
    return Math.round(volume);
  }

  private calculateMaintainabilityIndex(content: string): number {
    // Simplified maintainability index
    const lines = content.split('\n').length;
    const cyclomatic = this.calculateCyclomaticComplexity(content);
    const halstead = this.calculateHalsteadComplexity(content);
    
    // Simplified formula
    const mi = Math.max(0, (171 - 5.2 * Math.log(halstead) - 0.23 * cyclomatic - 16.2 * Math.log(lines)) * 100 / 171);
    
    return Math.round(mi);
  }

  private aggregateAnalyses(analyses: AnalysisReport[], dirPath: string): AnalysisReport {
    // Aggregate metrics from multiple files
    const totalMetrics: CodeMetrics = {
      totalLines: 0,
      codeLines: 0,
      commentLines: 0,
      blankLines: 0,
      commentRatio: 0,
      functions: 0,
      classes: 0,
      imports: 0
    };

    const allIssues: Issue[] = [];
    const allSuggestions: Suggestion[] = [];
    let maxComplexity: ComplexityMetrics = {
      cyclomatic: 0,
      cognitive: 0,
      halstead: 0,
      maintainabilityIndex: 100
    };

    for (const analysis of analyses) {
      if (analysis.metrics) {
        totalMetrics.totalLines += analysis.metrics.totalLines;
        totalMetrics.codeLines += analysis.metrics.codeLines;
        totalMetrics.commentLines += analysis.metrics.commentLines;
        totalMetrics.blankLines += analysis.metrics.blankLines;
        totalMetrics.functions += analysis.metrics.functions;
        totalMetrics.classes += analysis.metrics.classes;
        totalMetrics.imports += analysis.metrics.imports;
      }

      if (analysis.issues) {
        allIssues.push(...analysis.issues);
      }

      if (analysis.suggestions) {
        allSuggestions.push(...analysis.suggestions);
      }

      if (analysis.complexity) {
        maxComplexity.cyclomatic = Math.max(maxComplexity.cyclomatic, analysis.complexity.cyclomatic);
        maxComplexity.cognitive = Math.max(maxComplexity.cognitive, analysis.complexity.cognitive);
        maxComplexity.halstead = Math.max(maxComplexity.halstead, analysis.complexity.halstead);
        maxComplexity.maintainabilityIndex = Math.min(maxComplexity.maintainabilityIndex, analysis.complexity.maintainabilityIndex);
      }
    }

    totalMetrics.commentRatio = totalMetrics.totalLines > 0 
      ? totalMetrics.commentLines / totalMetrics.totalLines 
      : 0;

    return {
      target: dirPath,
      type: 'directory',
      fileCount: analyses.length,
      metrics: totalMetrics,
      issues: allIssues,
      suggestions: this.deduplicateSuggestions(allSuggestions),
      complexity: maxComplexity
    };
  }

  private deduplicateSuggestions(suggestions: Suggestion[]): Suggestion[] {
    const seen = new Set<string>();
    return suggestions.filter(s => {
      const key = `${s.type}:${s.message}`;
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  }

  private formatAnalysisReport(report: AnalysisReport): string {
    let output = `# Analysis Report for ${path.basename(report.target)}\n\n`;
    
    if (report.type === 'directory') {
      output += `Files analyzed: ${report.fileCount || 0}\n\n`;
    }

    // Metrics section
    if (report.metrics) {
      output += `## Code Metrics\n`;
      output += `- Total Lines: ${report.metrics.totalLines}\n`;
      output += `- Code Lines: ${report.metrics.codeLines}\n`;
      output += `- Comment Lines: ${report.metrics.commentLines} (${Math.round(report.metrics.commentRatio * 100)}%)\n`;
      output += `- Functions: ${report.metrics.functions}\n`;
      output += `- Classes: ${report.metrics.classes}\n\n`;
    }

    // Complexity section
    if (report.complexity) {
      output += `## Complexity Analysis\n`;
      output += `- Cyclomatic Complexity: ${report.complexity.cyclomatic}\n`;
      output += `- Cognitive Complexity: ${report.complexity.cognitive}\n`;
      output += `- Maintainability Index: ${report.complexity.maintainabilityIndex}%\n\n`;
    }

    // Issues section
    if (report.issues && report.issues.length > 0) {
      output += `## Issues Found (${report.issues.length})\n`;
      const grouped = this.groupIssuesBySeverity(report.issues);
      for (const [severity, issues] of Object.entries(grouped)) {
        output += `### ${severity.toUpperCase()} (${issues.length})\n`;
        for (const issue of issues.slice(0, 5)) {
          output += `- ${issue.message}`;
          if (issue.line) output += ` (line ${issue.line})`;
          output += '\n';
        }
        if (issues.length > 5) {
          output += `- ... and ${issues.length - 5} more\n`;
        }
      }
      output += '\n';
    }

    // Suggestions section
    if (report.suggestions && report.suggestions.length > 0) {
      output += `## Suggestions\n`;
      const grouped = this.groupSuggestionsByPriority(report.suggestions);
      for (const [priority, suggestions] of Object.entries(grouped)) {
        output += `### ${priority.toUpperCase()} Priority\n`;
        for (const suggestion of suggestions) {
          output += `- ${suggestion.message}\n`;
        }
      }
      output += '\n';
    }

    // Security section
    if (report.security) {
      output += `## Security Analysis\n`;
      output += `Security Score: ${report.security.score}/100\n`;
      if (report.security.vulnerabilities.length > 0) {
        output += `Vulnerabilities:\n`;
        for (const vuln of report.security.vulnerabilities) {
          output += `- [${vuln.severity.toUpperCase()}] ${vuln.message}\n`;
        }
      }
      output += '\n';
    }

    // Performance section
    if (report.performance) {
      output += `## Performance Analysis\n`;
      output += `Performance Score: ${report.performance.score}/100\n`;
      if (report.performance.issues.length > 0) {
        output += `Issues:\n`;
        for (const issue of report.performance.issues) {
          output += `- [${issue.impact.toUpperCase()}] ${issue.message}\n`;
        }
      }
    }

    return output;
  }

  private groupIssuesBySeverity(issues: Issue[]): Record<string, Issue[]> {
    const grouped: Record<string, Issue[]> = {};
    for (const issue of issues) {
      const severity = issue.severity || 'info';
      if (!grouped[severity]) grouped[severity] = [];
      grouped[severity].push(issue);
    }
    return grouped;
  }

  private groupSuggestionsByPriority(suggestions: Suggestion[]): Record<string, Suggestion[]> {
    const grouped: Record<string, Suggestion[]> = {};
    for (const suggestion of suggestions) {
      const priority = suggestion.priority || 'low';
      if (!grouped[priority]) grouped[priority] = [];
      grouped[priority].push(suggestion);
    }
    return grouped;
  }
}

// Type definitions
interface AnalysisReport {
  target: string;
  type: 'file' | 'directory';
  fileCount?: number;
  metrics?: CodeMetrics;
  issues?: Issue[];
  suggestions?: Suggestion[];
  complexity?: ComplexityMetrics;
  security?: SecurityAnalysis;
  performance?: PerformanceAnalysis;
}

interface CodeMetrics {
  totalLines: number;
  codeLines: number;
  commentLines: number;
  blankLines: number;
  commentRatio: number;
  functions: number;
  classes: number;
  imports: number;
}

interface Issue {
  type: 'error' | 'warning' | 'info';
  message: string;
  line?: number;
  severity?: 'critical' | 'high' | 'medium' | 'low' | 'info';
}

interface Suggestion {
  type: string;
  message: string;
  priority?: 'high' | 'medium' | 'low';
}

interface ComplexityMetrics {
  cyclomatic: number;
  cognitive: number;
  halstead: number;
  maintainabilityIndex: number;
}

interface SecurityAnalysis {
  vulnerabilities: Vulnerability[];
  score: number;
}

interface Vulnerability {
  type: string;
  severity: 'critical' | 'high' | 'medium' | 'low';
  message: string;
}

interface PerformanceAnalysis {
  issues: PerformanceIssue[];
  score: number;
}

interface PerformanceIssue {
  type: string;
  impact: 'high' | 'medium' | 'low';
  message: string;
}