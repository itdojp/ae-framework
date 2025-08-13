/**
 * Troubleshoot Command for ae-framework
 * Intelligent debugging and problem solving assistance
 */

import { CommandHandler, CommandResult, CommandContext } from '../slash-command-manager.js';
import { execSync } from 'child_process';
import * as fs from 'fs/promises';
import * as path from 'path';

export class TroubleshootCommand {
  name = '/ae:troubleshoot';
  description = 'Intelligent debugging and problem solving';
  category = 'utility' as const;
  usage = '/ae:troubleshoot [error message or issue description]';
  aliases = ['/troubleshoot', '/debug', '/fix'];

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    const issue = args.join(' ');
    
    if (!issue) {
      // Auto-detect issues
      const detected = await this.autoDetectIssues(context);
      if (detected.length > 0) {
        return await this.troubleshootDetectedIssues(detected, context);
      }
      
      return {
        success: false,
        message: 'No issues detected. Please describe the problem you\'re experiencing.'
      };
    }

    // Analyze the described issue
    const analysis = await this.analyzeIssue(issue, context);
    const solutions = await this.findSolutions(analysis, context);
    
    return {
      success: true,
      message: this.formatTroubleshootReport(analysis, solutions),
      data: { analysis, solutions }
    };
  }

  private async autoDetectIssues(context: CommandContext): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    // Check for test failures
    try {
      const testResult = await this.runTests();
      if (!testResult.success) {
        issues.push({
          type: 'test-failure',
          description: 'Test failures detected',
          details: testResult.failures
        });
      }
    } catch (error) {
      // Tests not configured or failed to run
    }

    // Check for TypeScript errors
    try {
      const tsErrors = await this.checkTypeScriptErrors();
      if (tsErrors.length > 0) {
        issues.push({
          type: 'type-error',
          description: 'TypeScript compilation errors',
          details: tsErrors
        });
      }
    } catch (error) {
      // TypeScript not configured
    }

    // Check for missing dependencies
    const missingDeps = await this.checkMissingDependencies();
    if (missingDeps.length > 0) {
      issues.push({
        type: 'missing-dependency',
        description: 'Missing npm dependencies',
        details: missingDeps
      });
    }

    // Check for configuration issues
    const configIssues = await this.checkConfiguration(context);
    if (configIssues.length > 0) {
      issues.push({
        type: 'configuration',
        description: 'Configuration problems detected',
        details: configIssues
      });
    }

    // Check recent error logs
    const errorLogs = await this.checkErrorLogs();
    if (errorLogs.length > 0) {
      issues.push({
        type: 'runtime-error',
        description: 'Runtime errors in logs',
        details: errorLogs
      });
    }

    return issues;
  }

  private async analyzeIssue(issue: string, context: CommandContext): Promise<IssueAnalysis> {
    const analysis: IssueAnalysis = {
      originalIssue: issue,
      category: this.categorizeIssue(issue),
      patterns: this.extractPatterns(issue),
      relatedFiles: await this.findRelatedFiles(issue, context),
      possibleCauses: []
    };

    // Analyze based on category
    switch (analysis.category) {
      case 'syntax-error':
        analysis.possibleCauses = this.analyzeSyntaxError(issue);
        break;
      case 'type-error':
        analysis.possibleCauses = this.analyzeTypeError(issue);
        break;
      case 'runtime-error':
        analysis.possibleCauses = this.analyzeRuntimeError(issue);
        break;
      case 'performance':
        analysis.possibleCauses = this.analyzePerformanceIssue(issue);
        break;
      case 'dependency':
        analysis.possibleCauses = this.analyzeDependencyIssue(issue);
        break;
      default:
        analysis.possibleCauses = this.analyzeGenericIssue(issue);
    }

    return analysis;
  }

  private async findSolutions(analysis: IssueAnalysis, context: CommandContext): Promise<Solution[]> {
    const solutions: Solution[] = [];

    for (const cause of analysis.possibleCauses) {
      const solution = await this.generateSolution(cause, analysis, context);
      if (solution) {
        solutions.push(solution);
      }
    }

    // Sort solutions by confidence
    solutions.sort((a, b) => b.confidence - a.confidence);

    return solutions;
  }

  private async generateSolution(
    cause: string,
    analysis: IssueAnalysis,
    context: CommandContext
  ): Promise<Solution | null> {
    // Map common causes to solutions
    const solutionMap: Record<string, Partial<Solution>> = {
      'missing import': {
        type: 'code-fix',
        description: 'Add missing import statement',
        confidence: 0.9
      },
      'undefined variable': {
        type: 'code-fix',
        description: 'Declare or import the undefined variable',
        confidence: 0.85
      },
      'type mismatch': {
        type: 'code-fix',
        description: 'Fix type annotations or cast values',
        confidence: 0.8
      },
      'missing dependency': {
        type: 'command',
        description: 'Install missing npm package',
        confidence: 0.95
      },
      'syntax error': {
        type: 'code-fix',
        description: 'Fix syntax error in code',
        confidence: 0.9
      },
      'async not awaited': {
        type: 'code-fix',
        description: 'Add await keyword to async function call',
        confidence: 0.85
      },
      'null reference': {
        type: 'code-fix',
        description: 'Add null check or optional chaining',
        confidence: 0.8
      }
    };

    // Find matching solution template
    for (const [key, template] of Object.entries(solutionMap)) {
      if (cause.toLowerCase().includes(key)) {
        const solution: Solution = {
          ...template,
          cause,
          steps: await this.generateSteps(template.type!, cause, analysis),
          code: template.type === 'code-fix' 
            ? await this.generateCodeFix(cause, analysis)
            : undefined,
          command: template.type === 'command'
            ? await this.generateCommand(cause, analysis)
            : undefined
        } as Solution;

        return solution;
      }
    }

    // Generic solution for unknown causes
    return {
      type: 'manual',
      cause,
      description: 'Manual investigation required',
      steps: [
        `1. Review the error message: ${analysis.originalIssue}`,
        `2. Check the related files: ${analysis.relatedFiles.join(', ')}`,
        `3. Look for similar patterns in the codebase`,
        `4. Consult documentation or community resources`
      ],
      confidence: 0.5
    };
  }

  private async generateSteps(type: string, cause: string, analysis: IssueAnalysis): Promise<string[]> {
    const steps: string[] = [];

    switch (type) {
      case 'code-fix':
        steps.push('1. Locate the error in the file');
        steps.push('2. Apply the suggested code fix');
        steps.push('3. Run tests to verify the fix');
        break;
      case 'command':
        steps.push('1. Open terminal in project root');
        steps.push('2. Run the suggested command');
        steps.push('3. Restart the application if needed');
        break;
      case 'configuration':
        steps.push('1. Open the configuration file');
        steps.push('2. Update the settings as suggested');
        steps.push('3. Validate the configuration');
        break;
    }

    return steps;
  }

  private async generateCodeFix(cause: string, analysis: IssueAnalysis): Promise<string> {
    // Generate appropriate code fix based on the cause
    if (cause.includes('missing import')) {
      const module = this.extractModuleName(analysis.originalIssue);
      return `import { ${module} } from './${module.toLowerCase()}';`;
    }

    if (cause.includes('undefined variable')) {
      const variable = this.extractVariableName(analysis.originalIssue);
      return `const ${variable} = /* TODO: Initialize variable */;`;
    }

    if (cause.includes('async not awaited')) {
      return `await /* your async function call */`;
    }

    if (cause.includes('null reference')) {
      return `if (variable) {\n  // Use variable safely\n}`;
    }

    return '// TODO: Apply appropriate fix';
  }

  private async generateCommand(cause: string, analysis: IssueAnalysis): Promise<string> {
    if (cause.includes('missing dependency')) {
      const packageName = this.extractPackageName(analysis.originalIssue);
      return `npm install ${packageName}`;
    }

    if (cause.includes('outdated dependency')) {
      const packageName = this.extractPackageName(analysis.originalIssue);
      return `npm update ${packageName}`;
    }

    if (cause.includes('build error')) {
      return 'npm run build';
    }

    return '';
  }

  // Helper methods
  private async runTests(): Promise<{ success: boolean; failures?: string[] }> {
    try {
      execSync('npm test', { stdio: 'pipe' });
      return { success: true };
    } catch (error: any) {
      const output = error.stdout?.toString() || '';
      const failures = this.extractTestFailures(output);
      return { success: false, failures };
    }
  }

  private extractTestFailures(output: string): string[] {
    const failures: string[] = [];
    const lines = output.split('\n');
    
    for (const line of lines) {
      if (line.includes('FAIL') || line.includes('✗')) {
        failures.push(line.trim());
      }
    }
    
    return failures;
  }

  private async checkTypeScriptErrors(): Promise<string[]> {
    try {
      execSync('npx tsc --noEmit', { stdio: 'pipe' });
      return [];
    } catch (error: any) {
      const output = error.stdout?.toString() || '';
      return this.extractTypeScriptErrors(output);
    }
  }

  private extractTypeScriptErrors(output: string): string[] {
    const errors: string[] = [];
    const lines = output.split('\n');
    
    for (const line of lines) {
      if (line.includes('error TS')) {
        errors.push(line.trim());
      }
    }
    
    return errors;
  }

  private async checkMissingDependencies(): Promise<string[]> {
    const missing: string[] = [];
    
    try {
      // Check package.json exists
      const packageJson = JSON.parse(await fs.readFile('package.json', 'utf-8'));
      const dependencies = { ...packageJson.dependencies, ...packageJson.devDependencies };
      
      // Check node_modules for each dependency
      for (const dep of Object.keys(dependencies)) {
        try {
          await fs.access(path.join('node_modules', dep));
        } catch {
          missing.push(dep);
        }
      }
    } catch {
      // package.json not found or invalid
    }
    
    return missing;
  }

  private async checkConfiguration(context: CommandContext): Promise<string[]> {
    const issues: string[] = [];
    
    // Check for required configuration files
    const requiredFiles = ['tsconfig.json', '.gitignore'];
    
    for (const file of requiredFiles) {
      try {
        await fs.access(path.join(context.projectRoot, file));
      } catch {
        issues.push(`Missing ${file}`);
      }
    }
    
    // Check for ae-framework specific configuration
    try {
      await fs.access(path.join(context.projectRoot, '.ae'));
    } catch {
      issues.push('ae-framework not properly initialized');
    }
    
    return issues;
  }

  private async checkErrorLogs(): Promise<string[]> {
    // Check for common log files
    const logFiles = ['error.log', 'npm-debug.log', '.ae/logs/error.log'];
    const errors: string[] = [];
    
    for (const logFile of logFiles) {
      try {
        const content = await fs.readFile(logFile, 'utf-8');
        const recentErrors = this.extractRecentErrors(content);
        errors.push(...recentErrors);
      } catch {
        // Log file doesn't exist
      }
    }
    
    return errors;
  }

  private extractRecentErrors(logContent: string): string[] {
    const errors: string[] = [];
    const lines = logContent.split('\n');
    
    for (const line of lines) {
      if (line.toLowerCase().includes('error') || line.toLowerCase().includes('exception')) {
        errors.push(line.trim());
      }
    }
    
    // Return last 10 errors
    return errors.slice(-10);
  }

  private categorizeIssue(issue: string): IssueCategory {
    const lower = issue.toLowerCase();
    
    if (lower.includes('syntaxerror') || lower.includes('unexpected token')) {
      return 'syntax-error';
    }
    if (lower.includes('type') || lower.includes('cannot read') || lower.includes('undefined')) {
      return 'type-error';
    }
    if (lower.includes('error') || lower.includes('exception') || lower.includes('failed')) {
      return 'runtime-error';
    }
    if (lower.includes('slow') || lower.includes('performance') || lower.includes('timeout')) {
      return 'performance';
    }
    if (lower.includes('cannot find module') || lower.includes('dependency')) {
      return 'dependency';
    }
    if (lower.includes('config') || lower.includes('setting')) {
      return 'configuration';
    }
    
    return 'unknown';
  }

  private extractPatterns(issue: string): string[] {
    const patterns: string[] = [];
    
    // Extract file paths
    const filePattern = /[\w/\\.-]+\.(ts|js|json|tsx|jsx)/g;
    const files = issue.match(filePattern);
    if (files) patterns.push(...files);
    
    // Extract function/variable names
    const identifierPattern = /\b[a-zA-Z_]\w+(?=\(|\s*=|\s*:)/g;
    const identifiers = issue.match(identifierPattern);
    if (identifiers) patterns.push(...identifiers);
    
    // Extract error codes
    const errorCodePattern = /\b[A-Z]+\d+\b/g;
    const errorCodes = issue.match(errorCodePattern);
    if (errorCodes) patterns.push(...errorCodes);
    
    return patterns;
  }

  private async findRelatedFiles(issue: string, context: CommandContext): Promise<string[]> {
    const patterns = this.extractPatterns(issue);
    const relatedFiles: string[] = [];
    
    for (const pattern of patterns) {
      if (pattern.includes('.')) {
        // It's likely a file
        const fullPath = path.join(context.projectRoot, pattern);
        try {
          await fs.access(fullPath);
          relatedFiles.push(pattern);
        } catch {
          // File doesn't exist
        }
      }
    }
    
    return relatedFiles;
  }

  private analyzeSyntaxError(issue: string): string[] {
    const causes: string[] = [];
    
    if (issue.includes('Unexpected token')) {
      causes.push('syntax error - unexpected token');
      causes.push('missing semicolon or comma');
      causes.push('unmatched brackets or parentheses');
    }
    
    if (issue.includes('Unexpected end')) {
      causes.push('incomplete statement or block');
      causes.push('missing closing bracket');
    }
    
    return causes;
  }

  private analyzeTypeError(issue: string): string[] {
    const causes: string[] = [];
    
    if (issue.includes('undefined')) {
      causes.push('undefined variable');
      causes.push('missing import');
      causes.push('null reference');
    }
    
    if (issue.includes('is not a function')) {
      causes.push('incorrect method call');
      causes.push('type mismatch');
    }
    
    if (issue.includes('Cannot read')) {
      causes.push('null reference');
      causes.push('async not awaited');
    }
    
    return causes;
  }

  private analyzeRuntimeError(issue: string): string[] {
    const causes: string[] = [];
    
    causes.push('unhandled exception');
    causes.push('async error not caught');
    causes.push('invalid input data');
    
    return causes;
  }

  private analyzePerformanceIssue(issue: string): string[] {
    return [
      'inefficient algorithm',
      'memory leak',
      'excessive I/O operations',
      'synchronous blocking operations'
    ];
  }

  private analyzeDependencyIssue(issue: string): string[] {
    return [
      'missing dependency',
      'version conflict',
      'outdated dependency',
      'peer dependency not satisfied'
    ];
  }

  private analyzeGenericIssue(issue: string): string[] {
    return [
      'configuration issue',
      'environment variable not set',
      'permission denied',
      'network connectivity issue'
    ];
  }

  private extractModuleName(issue: string): string {
    const match = issue.match(/module\s+['"]([^'"]+)['"]/);
    return match ? match[1] : 'Module';
  }

  private extractVariableName(issue: string): string {
    const match = issue.match(/\b([a-zA-Z_]\w+)\s+is\s+not\s+defined/);
    return match ? match[1] : 'variable';
  }

  private extractPackageName(issue: string): string {
    const match = issue.match(/Cannot find module\s+['"]([^'"]+)['"]/);
    return match ? match[1] : 'package-name';
  }

  private async troubleshootDetectedIssues(
    issues: DetectedIssue[],
    context: CommandContext
  ): Promise<CommandResult> {
    const allSolutions: Solution[] = [];
    
    for (const issue of issues) {
      const analysis = await this.analyzeIssue(issue.description, context);
      const solutions = await this.findSolutions(analysis, context);
      allSolutions.push(...solutions);
    }
    
    return {
      success: true,
      message: this.formatDetectedIssuesReport(issues, allSolutions),
      data: { issues, solutions: allSolutions }
    };
  }

  private formatTroubleshootReport(analysis: IssueAnalysis, solutions: Solution[]): string {
    let report = `# Troubleshooting Report\n\n`;
    report += `## Issue Analysis\n`;
    report += `- **Category**: ${analysis.category}\n`;
    report += `- **Related Files**: ${analysis.relatedFiles.join(', ') || 'None identified'}\n`;
    report += `- **Possible Causes**: \n`;
    
    for (const cause of analysis.possibleCauses) {
      report += `  - ${cause}\n`;
    }
    
    report += `\n## Suggested Solutions\n\n`;
    
    for (let i = 0; i < Math.min(3, solutions.length); i++) {
      const solution = solutions[i];
      report += `### Solution ${i + 1} (Confidence: ${Math.round(solution.confidence * 100)}%)\n`;
      report += `**${solution.description}**\n\n`;
      
      if (solution.steps) {
        report += `Steps:\n`;
        for (const step of solution.steps) {
          report += `${step}\n`;
        }
        report += '\n';
      }
      
      if (solution.code) {
        report += `Code Fix:\n\`\`\`typescript\n${solution.code}\n\`\`\`\n\n`;
      }
      
      if (solution.command) {
        report += `Command to run:\n\`\`\`bash\n${solution.command}\n\`\`\`\n\n`;
      }
    }
    
    if (solutions.length === 0) {
      report += `No automated solutions found. Manual investigation required.\n`;
    }
    
    return report;
  }

  private formatDetectedIssuesReport(issues: DetectedIssue[], solutions: Solution[]): string {
    let report = `# Auto-Detected Issues\n\n`;
    report += `Found ${issues.length} issue(s) in your project:\n\n`;
    
    for (const issue of issues) {
      report += `## ${issue.description}\n`;
      report += `Type: ${issue.type}\n`;
      
      if (issue.details && Array.isArray(issue.details)) {
        report += `Details:\n`;
        for (const detail of issue.details.slice(0, 5)) {
          report += `- ${detail}\n`;
        }
        if (issue.details.length > 5) {
          report += `- ... and ${issue.details.length - 5} more\n`;
        }
      }
      report += '\n';
    }
    
    if (solutions.length > 0) {
      report += `## Recommended Actions\n\n`;
      const topSolutions = solutions.slice(0, 5);
      
      for (const solution of topSolutions) {
        report += `- ${solution.description}`;
        if (solution.command) {
          report += `: \`${solution.command}\``;
        }
        report += '\n';
      }
    }
    
    return report;
  }
}

// Type definitions
interface DetectedIssue {
  type: string;
  description: string;
  details?: any;
}

interface IssueAnalysis {
  originalIssue: string;
  category: IssueCategory;
  patterns: string[];
  relatedFiles: string[];
  possibleCauses: string[];
}

type IssueCategory = 
  | 'syntax-error'
  | 'type-error'
  | 'runtime-error'
  | 'performance'
  | 'dependency'
  | 'configuration'
  | 'unknown';

interface Solution {
  type: 'code-fix' | 'command' | 'configuration' | 'manual';
  cause: string;
  description: string;
  steps?: string[];
  code?: string;
  command?: string;
  confidence: number;
}