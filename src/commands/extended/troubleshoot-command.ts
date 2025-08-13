/**
 * Troubleshoot Command for ae-framework
 * Provides intelligent debugging and problem diagnosis
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { exec } from 'child_process';
import { promisify } from 'util';
import type { CommandResult, CommandContext } from '../slash-command-manager.js';
import { EvidenceValidator } from '../../utils/evidence-validator.js';

const execAsync = promisify(exec);

export interface TroubleshootResult {
  issue: DetectedIssue;
  diagnosis: Diagnosis;
  solutions: Solution[];
  evidence?: any;
}

export interface DetectedIssue {
  type: string;
  description: string;
  severity: 'critical' | 'high' | 'medium' | 'low';
  location?: {
    file?: string;
    line?: number;
    function?: string;
  };
  stackTrace?: string;
}

export interface Diagnosis {
  rootCause: string;
  affectedComponents: string[];
  impact: string;
  confidence: number;
}

export interface Solution {
  description: string;
  steps: string[];
  confidence: number;
  estimatedTime: string;
  riskLevel: 'low' | 'medium' | 'high';
}

export class TroubleshootCommand {
  private validator: EvidenceValidator;

  constructor() {
    this.validator = new EvidenceValidator();
  }

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    const options = this.parseOptions(args);

    try {
      // Auto-detect issues if no specific target provided
      const issues = options.target 
        ? await this.troubleshootTarget(options.target, options)
        : await this.autoDetectIssues(options);

      const results: TroubleshootResult[] = [];
      
      for (const issue of issues) {
        const diagnosis = await this.diagnoseIssue(issue, options);
        const solutions = await this.generateSolutions(issue, diagnosis, options);
        
        // Validate solutions with evidence
        let evidence;
        if (options.validateSolutions) {
          const validation = await this.validator.validateClaim(
            `Solution for ${issue.type}: ${solutions[0]?.description}`,
            JSON.stringify(diagnosis),
            { minConfidence: 0.6, includeExternalDocs: true }
          );
          evidence = validation;
        }

        results.push({
          issue,
          diagnosis,
          solutions,
          evidence
        });
      }

      const summary = this.generateSummary(results);

      return {
        success: true,
        message: summary,
        data: results
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Troubleshooting failed: ${error.message}`
      };
    }
  }

  private parseOptions(args: string[]): any {
    const options: any = {
      target: null,
      deep: false,
      validateSolutions: false,
      includePerformance: false,
      includeMemory: false
    };

    for (let i = 0; i < args.length; i++) {
      if (!args[i].startsWith('--')) {
        options.target = args[i];
      } else {
        switch (args[i]) {
          case '--deep':
            options.deep = true;
            break;
          case '--validate':
            options.validateSolutions = true;
            break;
          case '--performance':
            options.includePerformance = true;
            break;
          case '--memory':
            options.includeMemory = true;
            break;
        }
      }
    }

    return options;
  }

  private async autoDetectIssues(options: any): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    // Check for test failures
    const testIssues = await this.checkTestFailures();
    issues.push(...testIssues);

    // Check for build errors
    const buildIssues = await this.checkBuildErrors();
    issues.push(...buildIssues);

    // Check for runtime errors in logs
    const logIssues = await this.checkLogs();
    issues.push(...logIssues);

    // Check for performance issues if requested
    if (options.includePerformance) {
      const perfIssues = await this.checkPerformance();
      issues.push(...perfIssues);
    }

    // Check for memory issues if requested
    if (options.includeMemory) {
      const memIssues = await this.checkMemory();
      issues.push(...memIssues);
    }

    // Check for dependency issues
    const depIssues = await this.checkDependencies();
    issues.push(...depIssues);

    return issues;
  }

  private async troubleshootTarget(target: string, options: any): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    try {
      const stats = await fs.stat(target);
      
      if (stats.isFile()) {
        // Analyze specific file for issues
        const fileIssues = await this.analyzeFile(target);
        issues.push(...fileIssues);
      } else if (stats.isDirectory()) {
        // Analyze directory
        const dirIssues = await this.analyzeDirectory(target);
        issues.push(...dirIssues);
      }
    } catch (error: any) {
      // Target doesn't exist or can't be accessed
      issues.push({
        type: 'File Access Error',
        description: `Cannot access ${target}: ${error.message}`,
        severity: 'high'
      });
    }

    return issues;
  }

  private async checkTestFailures(): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    try {
      const { stdout, stderr } = await execAsync('npm test 2>&1', { 
        env: { ...process.env, CI: 'true' }
      });
      
      // Parse test output for failures
      const failurePattern = /✖\s+(.+)\n\s+(.+)/g;
      let match;
      
      while ((match = failurePattern.exec(stdout + stderr)) !== null) {
        issues.push({
          type: 'Test Failure',
          description: match[1],
          severity: 'high',
          stackTrace: match[2]
        });
      }
    } catch (error: any) {
      // Tests failed to run
      if (error.stdout || error.stderr) {
        const output = error.stdout + error.stderr;
        
        // Extract specific test failures
        const lines = output.split('\n');
        for (const line of lines) {
          if (line.includes('FAIL') || line.includes('✖')) {
            issues.push({
              type: 'Test Failure',
              description: line.trim(),
              severity: 'high'
            });
          }
        }
      }
    }

    return issues;
  }

  private async checkBuildErrors(): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    try {
      // Try TypeScript compilation
      const { stderr } = await execAsync('npx tsc --noEmit 2>&1');
      
      if (stderr) {
        const errorPattern = /(.+)\((\d+),(\d+)\):\s+error\s+TS\d+:\s+(.+)/g;
        let match;
        
        while ((match = errorPattern.exec(stderr)) !== null) {
          issues.push({
            type: 'TypeScript Error',
            description: match[4],
            severity: 'critical',
            location: {
              file: match[1],
              line: parseInt(match[2])
            }
          });
        }
      }
    } catch (error: any) {
      // Build failed
      if (error.stderr) {
        issues.push({
          type: 'Build Error',
          description: 'TypeScript compilation failed',
          severity: 'critical',
          stackTrace: error.stderr
        });
      }
    }

    return issues;
  }

  private async checkLogs(): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];
    const logFiles = ['error.log', 'debug.log', 'app.log'];

    for (const logFile of logFiles) {
      try {
        const content = await fs.readFile(logFile, 'utf-8');
        const lines = content.split('\n').slice(-100); // Last 100 lines
        
        for (const line of lines) {
          if (line.includes('ERROR') || line.includes('FATAL')) {
            issues.push({
              type: 'Runtime Error',
              description: line.substring(0, 200),
              severity: line.includes('FATAL') ? 'critical' : 'high'
            });
          } else if (line.includes('WARN')) {
            issues.push({
              type: 'Warning',
              description: line.substring(0, 200),
              severity: 'medium'
            });
          }
        }
      } catch {
        // Log file doesn't exist
      }
    }

    return issues;
  }

  private async checkPerformance(): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    try {
      // Run performance profiling
      const { stdout } = await execAsync('npm run perf 2>&1 || echo "No perf script"');
      
      if (!stdout.includes('No perf script')) {
        // Parse performance metrics
        const slowPattern = /Slow operation:\s+(.+)\s+took\s+(\d+)ms/g;
        let match;
        
        while ((match = slowPattern.exec(stdout)) !== null) {
          const duration = parseInt(match[2]);
          if (duration > 1000) {
            issues.push({
              type: 'Performance Issue',
              description: `${match[1]} is slow (${duration}ms)`,
              severity: duration > 5000 ? 'high' : 'medium'
            });
          }
        }
      }
    } catch {
      // Performance check not available
    }

    return issues;
  }

  private async checkMemory(): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    try {
      // Check for memory leaks in heap snapshots
      const heapSnapshot = path.join(process.cwd(), 'heap-snapshot.heapsnapshot');
      const stats = await fs.stat(heapSnapshot);
      
      if (stats.size > 100 * 1024 * 1024) { // > 100MB
        issues.push({
          type: 'Memory Issue',
          description: 'Large heap snapshot detected - possible memory leak',
          severity: 'high'
        });
      }
    } catch {
      // No heap snapshot available
    }

    // Check current memory usage
    const memUsage = process.memoryUsage();
    if (memUsage.heapUsed > 500 * 1024 * 1024) { // > 500MB
      issues.push({
        type: 'Memory Issue',
        description: `High memory usage: ${Math.round(memUsage.heapUsed / 1024 / 1024)}MB`,
        severity: 'medium'
      });
    }

    return issues;
  }

  private async checkDependencies(): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];

    try {
      // Check for outdated dependencies
      const { stdout } = await execAsync('npm outdated --json 2>&1 || echo "{}"');
      const outdated = JSON.parse(stdout);
      
      for (const [pkg, info] of Object.entries(outdated) as any) {
        if (info.wanted !== info.latest) {
          issues.push({
            type: 'Outdated Dependency',
            description: `${pkg}: ${info.current} → ${info.latest}`,
            severity: 'low'
          });
        }
      }

      // Check for vulnerabilities
      const { stdout: auditOut } = await execAsync('npm audit --json 2>&1 || echo "{}"');
      const audit = JSON.parse(auditOut);
      
      if (audit.metadata?.vulnerabilities) {
        const vulns = audit.metadata.vulnerabilities;
        if (vulns.critical > 0) {
          issues.push({
            type: 'Security Vulnerability',
            description: `${vulns.critical} critical vulnerabilities found`,
            severity: 'critical'
          });
        }
        if (vulns.high > 0) {
          issues.push({
            type: 'Security Vulnerability',
            description: `${vulns.high} high severity vulnerabilities found`,
            severity: 'high'
          });
        }
      }
    } catch {
      // Dependency check failed
    }

    return issues;
  }

  private async analyzeFile(file: string): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];
    
    try {
      const content = await fs.readFile(file, 'utf-8');
      const lines = content.split('\n');
      
      // Check for syntax errors
      if (file.endsWith('.js') || file.endsWith('.ts')) {
        try {
          // Try to parse as JavaScript
          new Function(content);
        } catch (error: any) {
          issues.push({
            type: 'Syntax Error',
            description: error.message,
            severity: 'critical',
            location: { file }
          });
        }
      }

      // Check for common issues
      lines.forEach((line, index) => {
        // Infinite loops
        if (line.match(/while\s*\(\s*true\s*\)/) && !line.includes('break')) {
          issues.push({
            type: 'Potential Infinite Loop',
            description: 'while(true) without obvious break condition',
            severity: 'high',
            location: { file, line: index + 1 }
          });
        }

        // Unhandled promises
        if (line.includes('.then(') && !line.includes('.catch(')) {
          issues.push({
            type: 'Unhandled Promise',
            description: 'Promise without error handling',
            severity: 'medium',
            location: { file, line: index + 1 }
          });
        }
      });
    } catch (error: any) {
      issues.push({
        type: 'File Read Error',
        description: error.message,
        severity: 'high',
        location: { file }
      });
    }

    return issues;
  }

  private async analyzeDirectory(dir: string): Promise<DetectedIssue[]> {
    const issues: DetectedIssue[] = [];
    
    try {
      const entries = await fs.readdir(dir, { withFileTypes: true });
      
      for (const entry of entries) {
        if (entry.isFile() && (entry.name.endsWith('.js') || entry.name.endsWith('.ts'))) {
          const filePath = path.join(dir, entry.name);
          const fileIssues = await this.analyzeFile(filePath);
          issues.push(...fileIssues);
        }
      }
    } catch (error: any) {
      issues.push({
        type: 'Directory Read Error',
        description: error.message,
        severity: 'high'
      });
    }

    return issues;
  }

  private async diagnoseIssue(issue: DetectedIssue, options: any): Promise<Diagnosis> {
    let rootCause = 'Unknown';
    let affectedComponents: string[] = [];
    let impact = 'Unknown';
    let confidence = 0.5;

    switch (issue.type) {
      case 'Test Failure':
        rootCause = await this.diagnoseTestFailure(issue);
        affectedComponents = ['Test Suite', 'Implementation'];
        impact = 'CI/CD pipeline blocked';
        confidence = 0.8;
        break;

      case 'TypeScript Error':
        rootCause = 'Type system violation';
        affectedComponents = [issue.location?.file || 'Unknown file'];
        impact = 'Build failure';
        confidence = 0.95;
        break;

      case 'Runtime Error':
        rootCause = await this.diagnoseRuntimeError(issue);
        affectedComponents = this.identifyAffectedComponents(issue);
        impact = 'Application crash or malfunction';
        confidence = 0.7;
        break;

      case 'Performance Issue':
        rootCause = 'Inefficient algorithm or resource usage';
        affectedComponents = ['Performance-critical path'];
        impact = 'Slow response times';
        confidence = 0.6;
        break;

      case 'Memory Issue':
        rootCause = 'Memory leak or excessive allocation';
        affectedComponents = ['Memory management'];
        impact = 'Out of memory errors';
        confidence = 0.65;
        break;

      case 'Security Vulnerability':
        rootCause = 'Vulnerable dependency';
        affectedComponents = ['Dependencies'];
        impact = 'Security risk';
        confidence = 0.9;
        break;

      default:
        rootCause = `${issue.type} detected`;
        confidence = 0.4;
    }

    if (options.deep) {
      // Perform deeper analysis
      const deepAnalysis = await this.performDeepAnalysis(issue);
      if (deepAnalysis.rootCause) rootCause = deepAnalysis.rootCause;
      if (deepAnalysis.confidence) confidence = deepAnalysis.confidence;
    }

    return {
      rootCause,
      affectedComponents,
      impact,
      confidence
    };
  }

  private async diagnoseTestFailure(issue: DetectedIssue): Promise<string> {
    if (issue.stackTrace) {
      if (issue.stackTrace.includes('TypeError')) {
        return 'Type error in test or implementation';
      }
      if (issue.stackTrace.includes('ReferenceError')) {
        return 'Undefined variable or function';
      }
      if (issue.stackTrace.includes('AssertionError')) {
        return 'Assertion failed - expected vs actual mismatch';
      }
    }
    return 'Test expectation not met';
  }

  private async diagnoseRuntimeError(issue: DetectedIssue): Promise<string> {
    const description = issue.description.toLowerCase();
    
    if (description.includes('cannot read property')) {
      return 'Null or undefined reference';
    }
    if (description.includes('connection refused')) {
      return 'Service unavailable or network issue';
    }
    if (description.includes('timeout')) {
      return 'Operation took too long';
    }
    if (description.includes('permission denied')) {
      return 'Insufficient permissions';
    }
    
    return 'Runtime exception';
  }

  private identifyAffectedComponents(issue: DetectedIssue): string[] {
    const components: string[] = [];
    
    if (issue.location?.file) {
      components.push(path.basename(issue.location.file));
    }
    if (issue.location?.function) {
      components.push(issue.location.function);
    }
    
    // Extract components from stack trace
    if (issue.stackTrace) {
      const filePattern = /at\s+.*?\s+\((.+?):\d+:\d+\)/g;
      let match;
      while ((match = filePattern.exec(issue.stackTrace)) !== null) {
        components.push(path.basename(match[1]));
      }
    }
    
    return [...new Set(components)];
  }

  private async performDeepAnalysis(issue: DetectedIssue): Promise<any> {
    // Simulate deep analysis
    const analysis: any = {};
    
    // Try to find related issues
    if (issue.location?.file) {
      try {
        const content = await fs.readFile(issue.location.file, 'utf-8');
        
        // Look for patterns that might indicate root cause
        if (content.includes('TODO') || content.includes('FIXME')) {
          analysis.rootCause = 'Incomplete implementation (TODO/FIXME found)';
          analysis.confidence = 0.75;
        }
      } catch {
        // File not accessible
      }
    }
    
    return analysis;
  }

  private async generateSolutions(
    issue: DetectedIssue,
    diagnosis: Diagnosis,
    options: any
  ): Promise<Solution[]> {
    const solutions: Solution[] = [];

    switch (issue.type) {
      case 'Test Failure':
        solutions.push(...this.generateTestSolutions(issue, diagnosis));
        break;

      case 'TypeScript Error':
        solutions.push(...this.generateTypeScriptSolutions(issue, diagnosis));
        break;

      case 'Runtime Error':
        solutions.push(...this.generateRuntimeSolutions(issue, diagnosis));
        break;

      case 'Performance Issue':
        solutions.push(...this.generatePerformanceSolutions(issue, diagnosis));
        break;

      case 'Memory Issue':
        solutions.push(...this.generateMemorySolutions(issue, diagnosis));
        break;

      case 'Security Vulnerability':
        solutions.push(...this.generateSecuritySolutions(issue, diagnosis));
        break;

      default:
        solutions.push({
          description: 'Manual investigation required',
          steps: [
            `Review ${issue.type}`,
            'Check related documentation',
            'Consult team members'
          ],
          confidence: 0.3,
          estimatedTime: '30min',
          riskLevel: 'low'
        });
    }

    // Sort by confidence
    solutions.sort((a, b) => b.confidence - a.confidence);

    return solutions.slice(0, 3); // Return top 3 solutions
  }

  private generateTestSolutions(issue: DetectedIssue, diagnosis: Diagnosis): Solution[] {
    const solutions: Solution[] = [];

    if (diagnosis.rootCause.includes('Type error')) {
      solutions.push({
        description: 'Fix type mismatch',
        steps: [
          'Check test data types',
          'Verify function signatures',
          'Update test expectations'
        ],
        confidence: 0.8,
        estimatedTime: '15min',
        riskLevel: 'low'
      });
    }

    if (diagnosis.rootCause.includes('Assertion failed')) {
      solutions.push({
        description: 'Update test expectations',
        steps: [
          'Review actual vs expected values',
          'Verify business logic',
          'Update assertions or fix implementation'
        ],
        confidence: 0.75,
        estimatedTime: '20min',
        riskLevel: 'low'
      });
    }

    solutions.push({
      description: 'Debug test in isolation',
      steps: [
        'Run single test with --inspect',
        'Add console.log statements',
        'Use debugger to step through'
      ],
      confidence: 0.6,
      estimatedTime: '30min',
      riskLevel: 'low'
    });

    return solutions;
  }

  private generateTypeScriptSolutions(issue: DetectedIssue, diagnosis: Diagnosis): Solution[] {
    const solutions: Solution[] = [];

    solutions.push({
      description: 'Fix type annotations',
      steps: [
        `Open ${issue.location?.file}`,
        `Go to line ${issue.location?.line}`,
        'Add or correct type annotations',
        'Run tsc to verify'
      ],
      confidence: 0.9,
      estimatedTime: '10min',
      riskLevel: 'low'
    });

    solutions.push({
      description: 'Use type assertion as workaround',
      steps: [
        'Add "as Type" assertion',
        'Document why assertion is needed',
        'Plan proper fix for later'
      ],
      confidence: 0.5,
      estimatedTime: '5min',
      riskLevel: 'medium'
    });

    return solutions;
  }

  private generateRuntimeSolutions(issue: DetectedIssue, diagnosis: Diagnosis): Solution[] {
    const solutions: Solution[] = [];

    if (diagnosis.rootCause.includes('Null or undefined')) {
      solutions.push({
        description: 'Add null checks',
        steps: [
          'Identify nullable variables',
          'Add optional chaining (?.) or null checks',
          'Initialize variables properly'
        ],
        confidence: 0.85,
        estimatedTime: '15min',
        riskLevel: 'low'
      });
    }

    if (diagnosis.rootCause.includes('network')) {
      solutions.push({
        description: 'Implement retry logic',
        steps: [
          'Add exponential backoff',
          'Set reasonable timeout',
          'Add error handling'
        ],
        confidence: 0.7,
        estimatedTime: '30min',
        riskLevel: 'low'
      });
    }

    solutions.push({
      description: 'Add comprehensive error handling',
      steps: [
        'Wrap in try-catch',
        'Log detailed error information',
        'Provide graceful fallback'
      ],
      confidence: 0.6,
      estimatedTime: '20min',
      riskLevel: 'low'
    });

    return solutions;
  }

  private generatePerformanceSolutions(issue: DetectedIssue, diagnosis: Diagnosis): Solution[] {
    return [
      {
        description: 'Optimize algorithm',
        steps: [
          'Profile code to find bottleneck',
          'Use more efficient data structures',
          'Implement caching'
        ],
        confidence: 0.7,
        estimatedTime: '2hr',
        riskLevel: 'medium'
      },
      {
        description: 'Add performance monitoring',
        steps: [
          'Add timing measurements',
          'Set up performance budgets',
          'Create alerts for slowdowns'
        ],
        confidence: 0.6,
        estimatedTime: '1hr',
        riskLevel: 'low'
      }
    ];
  }

  private generateMemorySolutions(issue: DetectedIssue, diagnosis: Diagnosis): Solution[] {
    return [
      {
        description: 'Fix memory leak',
        steps: [
          'Take heap snapshots',
          'Compare allocations',
          'Remove event listeners',
          'Clear caches properly'
        ],
        confidence: 0.65,
        estimatedTime: '3hr',
        riskLevel: 'medium'
      },
      {
        description: 'Optimize memory usage',
        steps: [
          'Use WeakMap for caches',
          'Implement pagination',
          'Stream large data'
        ],
        confidence: 0.6,
        estimatedTime: '2hr',
        riskLevel: 'low'
      }
    ];
  }

  private generateSecuritySolutions(issue: DetectedIssue, diagnosis: Diagnosis): Solution[] {
    return [
      {
        description: 'Update vulnerable dependencies',
        steps: [
          'Run npm audit fix',
          'Update package.json',
          'Test thoroughly',
          'Deploy update'
        ],
        confidence: 0.9,
        estimatedTime: '30min',
        riskLevel: 'low'
      },
      {
        description: 'Apply security patch',
        steps: [
          'Check for patches',
          'Apply patch manually',
          'Verify fix'
        ],
        confidence: 0.7,
        estimatedTime: '1hr',
        riskLevel: 'medium'
      }
    ];
  }

  private generateSummary(results: TroubleshootResult[]): string {
    let summary = `Found ${results.length} issue(s)\n\n`;

    for (const result of results) {
      summary += `[${result.issue.severity.toUpperCase()}] ${result.issue.type}\n`;
      summary += `  ${result.issue.description}\n`;
      summary += `  Root Cause: ${result.diagnosis.rootCause}\n`;
      
      if (result.solutions.length > 0) {
        summary += `  Top Solution: ${result.solutions[0].description} `;
        summary += `(${Math.round(result.solutions[0].confidence * 100)}% confidence)\n`;
      }
      
      summary += '\n';
    }

    // Add summary statistics
    const critical = results.filter(r => r.issue.severity === 'critical').length;
    const high = results.filter(r => r.issue.severity === 'high').length;
    
    if (critical > 0 || high > 0) {
      summary += `⚠️  ${critical} critical, ${high} high severity issues require immediate attention`;
    }

    return summary;
  }
}