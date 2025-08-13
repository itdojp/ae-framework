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
  name = '/ae:troubleshoot';
  description = 'Intelligent debugging and problem diagnosis';
  category = 'utility' as const;
  usage = '/ae:troubleshoot [--error="error message"] [--file=path] [--logs=path] [--validate]';
  aliases = ['/troubleshoot', '/a:troubleshoot'];

  private validator: EvidenceValidator;

  constructor() {
    this.validator = new EvidenceValidator();
  }

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    const options = this.parseOptions(args);

    try {
      const results = await this.performDiagnosis(options, context);
      const summary = this.generateSummary(results);

      // Validate diagnosis with evidence if requested
      if (options.validate && results.length > 0) {
        for (const result of results) {
          const validation = await this.validator.validateClaim(
            `Troubleshooting diagnosis: ${result.diagnosis.rootCause}`,
            JSON.stringify({ issue: result.issue, solutions: result.solutions }),
            { minConfidence: 0.6 }
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
        message: `Troubleshooting failed: ${error.message}`
      };
    }
  }

  private parseOptions(args: string[]): any {
    const options: any = {
      error: null,
      file: null,
      logs: null,
      validate: false,
      auto: true
    };

    for (const arg of args) {
      if (arg.startsWith('--error=')) {
        options.error = arg.split('=')[1];
      } else if (arg.startsWith('--file=')) {
        options.file = arg.split('=')[1];
      } else if (arg.startsWith('--logs=')) {
        options.logs = arg.split('=')[1];
      } else if (arg === '--validate') {
        options.validate = true;
      } else if (arg === '--no-auto') {
        options.auto = false;
      }
    }

    return options;
  }

  private async performDiagnosis(options: any, context: CommandContext): Promise<TroubleshootResult[]> {
    const results: TroubleshootResult[] = [];

    // If no specific issue is provided, perform automatic detection
    if (options.auto && !options.error && !options.file && !options.logs) {
      const autoDetected = await this.autoDetectIssues(context);
      results.push(...autoDetected);
    }

    // If specific error provided, analyze it
    if (options.error) {
      const errorResult = await this.analyzeError(options.error, options.file);
      results.push(errorResult);
    }

    // If specific file provided, analyze it
    if (options.file) {
      const fileResult = await this.analyzeFile(options.file);
      results.push(fileResult);
    }

    // If log file provided, analyze it
    if (options.logs) {
      const logResults = await this.analyzeLogs(options.logs);
      results.push(...logResults);
    }

    return results;
  }

  private async autoDetectIssues(context: CommandContext): Promise<TroubleshootResult[]> {
    const results: TroubleshootResult[] = [];

    try {
      // Check for common Node.js/npm issues
      const packageJsonPath = path.join(context.projectRoot, 'package.json');
      if (await this.fileExists(packageJsonPath)) {
        const packageIssues = await this.checkPackageIssues(packageJsonPath);
        results.push(...packageIssues);
      }

      // Check for TypeScript issues
      const tsConfigPath = path.join(context.projectRoot, 'tsconfig.json');
      if (await this.fileExists(tsConfigPath)) {
        const tsIssues = await this.checkTypeScriptIssues(context.projectRoot);
        results.push(...tsIssues);
      }

      // Check for git issues
      const gitPath = path.join(context.projectRoot, '.git');
      if (await this.fileExists(gitPath)) {
        const gitIssues = await this.checkGitIssues(context.projectRoot);
        results.push(...gitIssues);
      }

      // Check for process/port issues
      const processIssues = await this.checkProcessIssues();
      results.push(...processIssues);

    } catch (error) {
      // Auto-detection failed, but continue
    }

    return results;
  }

  private async analyzeError(errorMessage: string, filePath?: string): Promise<TroubleshootResult> {
    const issue: DetectedIssue = {
      type: this.categorizeError(errorMessage),
      description: errorMessage,
      severity: this.determineSeverity(errorMessage),
      stackTrace: errorMessage
    };

    if (filePath) {
      issue.location = { file: filePath };
    }

    const diagnosis = await this.diagnoseIssue(issue);
    const solutions = await this.generateSolutions(issue, diagnosis);

    return {
      issue,
      diagnosis,
      solutions
    };
  }

  private async analyzeFile(filePath: string): Promise<TroubleshootResult> {
    const content = await fs.readFile(filePath, 'utf-8');
    const issues = this.scanFileForIssues(content, filePath);

    if (issues.length === 0) {
      return {
        issue: {
          type: 'no-issues',
          description: 'No obvious issues detected in the file',
          severity: 'low'
        },
        diagnosis: {
          rootCause: 'File appears to be healthy',
          affectedComponents: [filePath],
          impact: 'None',
          confidence: 0.8
        },
        solutions: []
      };
    }

    // Return the most severe issue found
    const primaryIssue = issues.sort((a, b) => this.getSeverityScore(b.severity) - this.getSeverityScore(a.severity))[0];
    const diagnosis = await this.diagnoseIssue(primaryIssue);
    const solutions = await this.generateSolutions(primaryIssue, diagnosis);

    return {
      issue: primaryIssue,
      diagnosis,
      solutions
    };
  }

  private async analyzeLogs(logPath: string): Promise<TroubleshootResult[]> {
    const results: TroubleshootResult[] = [];
    
    try {
      const logContent = await fs.readFile(logPath, 'utf-8');
      const logLines = logContent.split('\n');
      
      const errors = this.extractErrorsFromLogs(logLines);
      
      for (const error of errors) {
        const issue: DetectedIssue = {
          type: 'log-error',
          description: error.message,
          severity: error.severity,
          location: {
            file: logPath,
            line: error.lineNumber
          }
        };

        const diagnosis = await this.diagnoseIssue(issue);
        const solutions = await this.generateSolutions(issue, diagnosis);

        results.push({
          issue,
          diagnosis,
          solutions
        });
      }
    } catch (error) {
      results.push({
        issue: {
          type: 'log-access-error',
          description: `Unable to read log file: ${error}`,
          severity: 'high'
        },
        diagnosis: {
          rootCause: 'Log file is inaccessible or corrupted',
          affectedComponents: [logPath],
          impact: 'Cannot analyze application logs',
          confidence: 0.9
        },
        solutions: [
          {
            description: 'Check log file permissions and path',
            steps: [
              'Verify the log file path is correct',
              'Check file permissions',
              'Ensure the log file is not locked by another process'
            ],
            confidence: 0.8,
            estimatedTime: '5 minutes',
            riskLevel: 'low'
          }
        ]
      });
    }

    return results;
  }

  private async checkPackageIssues(packageJsonPath: string): Promise<TroubleshootResult[]> {
    const results: TroubleshootResult[] = [];
    
    try {
      const packageContent = await fs.readFile(packageJsonPath, 'utf-8');
      const packageJson = JSON.parse(packageContent);

      // Check for missing node_modules
      const nodeModulesPath = path.join(path.dirname(packageJsonPath), 'node_modules');
      if (!await this.fileExists(nodeModulesPath)) {
        results.push({
          issue: {
            type: 'missing-dependencies',
            description: 'node_modules directory is missing',
            severity: 'high'
          },
          diagnosis: {
            rootCause: 'Dependencies not installed',
            affectedComponents: ['node_modules'],
            impact: 'Application cannot run',
            confidence: 0.95
          },
          solutions: [
            {
              description: 'Install dependencies',
              steps: ['Run npm install or yarn install'],
              confidence: 0.9,
              estimatedTime: '2-5 minutes',
              riskLevel: 'low'
            }
          ]
        });
      }

      // Check for security vulnerabilities
      try {
        const { stdout } = await execAsync('npm audit --json', { 
          cwd: path.dirname(packageJsonPath),
          timeout: 10000 
        });
        const auditResult = JSON.parse(stdout);
        
        if (auditResult.vulnerabilities && Object.keys(auditResult.vulnerabilities).length > 0) {
          results.push({
            issue: {
              type: 'security-vulnerabilities',
              description: `${Object.keys(auditResult.vulnerabilities).length} security vulnerabilities found`,
              severity: 'medium'
            },
            diagnosis: {
              rootCause: 'Outdated or vulnerable dependencies',
              affectedComponents: Object.keys(auditResult.vulnerabilities),
              impact: 'Potential security risks',
              confidence: 0.85
            },
            solutions: [
              {
                description: 'Fix security vulnerabilities',
                steps: [
                  'Run npm audit fix',
                  'Review and update vulnerable packages manually if needed'
                ],
                confidence: 0.8,
                estimatedTime: '5-15 minutes',
                riskLevel: 'low'
              }
            ]
          });
        }
      } catch (auditError) {
        // Audit failed, but continue
      }

    } catch (error) {
      results.push({
        issue: {
          type: 'package-json-error',
          description: 'package.json is malformed or unreadable',
          severity: 'high'
        },
        diagnosis: {
          rootCause: 'Invalid package.json syntax',
          affectedComponents: ['package.json'],
          impact: 'Cannot manage dependencies',
          confidence: 0.9
        },
        solutions: [
          {
            description: 'Fix package.json syntax',
            steps: [
              'Validate JSON syntax',
              'Check for missing commas or quotes',
              'Use a JSON validator tool'
            ],
            confidence: 0.8,
            estimatedTime: '5-10 minutes',
            riskLevel: 'medium'
          }
        ]
      });
    }

    return results;
  }

  private async checkTypeScriptIssues(projectRoot: string): Promise<TroubleshootResult[]> {
    const results: TroubleshootResult[] = [];

    try {
      const { stdout, stderr } = await execAsync('npx tsc --noEmit', { 
        cwd: projectRoot,
        timeout: 30000 
      });

      if (stderr) {
        const errors = this.parseTypeScriptErrors(stderr);
        
        for (const error of errors) {
          results.push({
            issue: {
              type: 'typescript-error',
              description: error.message,
              severity: 'medium',
              location: {
                file: error.file,
                line: error.line
              }
            },
            diagnosis: {
              rootCause: 'TypeScript compilation errors',
              affectedComponents: [error.file || 'unknown'],
              impact: 'Code will not compile',
              confidence: 0.9
            },
            solutions: [
              {
                description: 'Fix TypeScript errors',
                steps: [
                  'Open the affected file',
                  'Review the error message',
                  'Fix type annotations or logic as needed'
                ],
                confidence: 0.7,
                estimatedTime: '5-30 minutes per error',
                riskLevel: 'low'
              }
            ]
          });
        }
      }
    } catch (error) {
      // TypeScript check failed, but this might be expected
    }

    return results;
  }

  private async checkGitIssues(projectRoot: string): Promise<TroubleshootResult[]> {
    const results: TroubleshootResult[] = [];

    try {
      // Check for uncommitted changes
      const { stdout: statusOutput } = await execAsync('git status --porcelain', { 
        cwd: projectRoot,
        timeout: 5000 
      });

      if (statusOutput.trim()) {
        results.push({
          issue: {
            type: 'uncommitted-changes',
            description: 'There are uncommitted changes in the repository',
            severity: 'low'
          },
          diagnosis: {
            rootCause: 'Working directory has modified files',
            affectedComponents: statusOutput.trim().split('\n').map(line => line.substring(3)),
            impact: 'Changes may be lost',
            confidence: 0.95
          },
          solutions: [
            {
              description: 'Commit or stash changes',
              steps: [
                'Review changed files with git status',
                'Add files with git add',
                'Commit with git commit -m "message"',
                'Or stash with git stash'
              ],
              confidence: 0.9,
              estimatedTime: '2-5 minutes',
              riskLevel: 'low'
            }
          ]
        });
      }

      // Check for merge conflicts
      const { stdout: conflictOutput } = await execAsync('git diff --name-only --diff-filter=U', { 
        cwd: projectRoot,
        timeout: 5000 
      });

      if (conflictOutput.trim()) {
        results.push({
          issue: {
            type: 'merge-conflicts',
            description: 'Merge conflicts detected',
            severity: 'high'
          },
          diagnosis: {
            rootCause: 'Unresolved merge conflicts',
            affectedComponents: conflictOutput.trim().split('\n'),
            impact: 'Cannot complete merge operation',
            confidence: 0.95
          },
          solutions: [
            {
              description: 'Resolve merge conflicts',
              steps: [
                'Open conflicted files',
                'Look for conflict markers (<<<<<<< ======= >>>>>>>)',
                'Choose the correct version or merge manually',
                'Remove conflict markers',
                'Add and commit resolved files'
              ],
              confidence: 0.8,
              estimatedTime: '10-30 minutes',
              riskLevel: 'medium'
            }
          ]
        });
      }
    } catch (error) {
      // Git commands failed, repository might not be initialized
    }

    return results;
  }

  private async checkProcessIssues(): Promise<TroubleshootResult[]> {
    const results: TroubleshootResult[] = [];

    try {
      // Check for common port conflicts (3000, 8000, 8080, 5000)
      const commonPorts = [3000, 8000, 8080, 5000];
      
      for (const port of commonPorts) {
        try {
          const { stdout } = await execAsync(`lsof -i :${port}`, { timeout: 5000 });
          if (stdout.trim()) {
            results.push({
              issue: {
                type: 'port-conflict',
                description: `Port ${port} is already in use`,
                severity: 'medium'
              },
              diagnosis: {
                rootCause: `Another process is using port ${port}`,
                affectedComponents: [`port-${port}`],
                impact: 'Application cannot start on this port',
                confidence: 0.9
              },
              solutions: [
                {
                  description: 'Free up the port',
                  steps: [
                    `Find the process using: lsof -i :${port}`,
                    'Kill the process if safe to do so',
                    'Or configure your application to use a different port'
                  ],
                  confidence: 0.8,
                  estimatedTime: '2-5 minutes',
                  riskLevel: 'low'
                }
              ]
            });
          }
        } catch (error) {
          // Port check failed, continue
        }
      }
    } catch (error) {
      // Process checking not available on this system
    }

    return results;
  }

  private categorizeError(errorMessage: string): string {
    if (errorMessage.includes('ENOENT')) return 'file-not-found';
    if (errorMessage.includes('EADDRINUSE')) return 'port-in-use';
    if (errorMessage.includes('EACCES')) return 'permission-denied';
    if (errorMessage.includes('MODULE_NOT_FOUND')) return 'missing-module';
    if (errorMessage.includes('SyntaxError')) return 'syntax-error';
    if (errorMessage.includes('TypeError')) return 'type-error';
    if (errorMessage.includes('ReferenceError')) return 'reference-error';
    if (errorMessage.includes('ECONNREFUSED')) return 'connection-refused';
    if (errorMessage.includes('timeout')) return 'timeout';
    return 'unknown-error';
  }

  private determineSeverity(errorMessage: string): 'critical' | 'high' | 'medium' | 'low' {
    if (errorMessage.includes('FATAL') || errorMessage.includes('CRITICAL')) return 'critical';
    if (errorMessage.includes('ERROR') || errorMessage.includes('FAIL')) return 'high';
    if (errorMessage.includes('WARN') || errorMessage.includes('WARNING')) return 'medium';
    return 'low';
  }

  private async diagnoseIssue(issue: DetectedIssue): Promise<Diagnosis> {
    const diagnosis: Diagnosis = {
      rootCause: 'Unknown',
      affectedComponents: [],
      impact: 'Unknown impact',
      confidence: 0.5
    };

    switch (issue.type) {
      case 'file-not-found':
        diagnosis.rootCause = 'Required file or directory does not exist';
        diagnosis.impact = 'Application cannot access required resources';
        diagnosis.confidence = 0.9;
        break;
      
      case 'port-in-use':
        diagnosis.rootCause = 'Another process is already using the required port';
        diagnosis.impact = 'Application cannot start or bind to network port';
        diagnosis.confidence = 0.95;
        break;
      
      case 'missing-module':
        diagnosis.rootCause = 'Required Node.js module is not installed';
        diagnosis.impact = 'Application cannot import required functionality';
        diagnosis.confidence = 0.9;
        break;
      
      case 'syntax-error':
        diagnosis.rootCause = 'Code contains invalid syntax';
        diagnosis.impact = 'Code cannot be parsed or executed';
        diagnosis.confidence = 0.95;
        break;
      
      case 'type-error':
        diagnosis.rootCause = 'Variable or object is not of expected type';
        diagnosis.impact = 'Runtime error causing application failure';
        diagnosis.confidence = 0.8;
        break;
      
      default:
        diagnosis.rootCause = 'Issue requires manual investigation';
        diagnosis.impact = 'Unknown impact on application functionality';
        diagnosis.confidence = 0.3;
    }

    if (issue.location?.file) {
      diagnosis.affectedComponents.push(issue.location.file);
    }

    return diagnosis;
  }

  private async generateSolutions(issue: DetectedIssue, diagnosis: Diagnosis): Promise<Solution[]> {
    const solutions: Solution[] = [];

    switch (issue.type) {
      case 'file-not-found':
        solutions.push({
          description: 'Create the missing file or directory',
          steps: [
            'Verify the expected file path',
            'Create the missing file or directory',
            'Ensure proper permissions are set'
          ],
          confidence: 0.8,
          estimatedTime: '2-5 minutes',
          riskLevel: 'low'
        });
        break;

      case 'port-in-use':
        solutions.push({
          description: 'Use a different port',
          steps: [
            'Find available port numbers',
            'Update application configuration to use different port',
            'Restart the application'
          ],
          confidence: 0.9,
          estimatedTime: '2-5 minutes',
          riskLevel: 'low'
        });
        solutions.push({
          description: 'Stop the conflicting process',
          steps: [
            'Identify the process using the port',
            'Safely terminate the process if appropriate',
            'Restart your application'
          ],
          confidence: 0.7,
          estimatedTime: '5-10 minutes',
          riskLevel: 'medium'
        });
        break;

      case 'missing-module':
        solutions.push({
          description: 'Install the missing module',
          steps: [
            'Run npm install <module-name>',
            'Or add to package.json and run npm install',
            'Verify installation was successful'
          ],
          confidence: 0.9,
          estimatedTime: '2-5 minutes',
          riskLevel: 'low'
        });
        break;

      case 'syntax-error':
        solutions.push({
          description: 'Fix syntax errors in the code',
          steps: [
            'Open the file mentioned in the error',
            'Go to the line number indicated',
            'Review and correct syntax errors',
            'Use linting tools to catch similar issues'
          ],
          confidence: 0.8,
          estimatedTime: '5-15 minutes',
          riskLevel: 'low'
        });
        break;

      default:
        solutions.push({
          description: 'Manual investigation required',
          steps: [
            'Review error message carefully',
            'Check application logs for more context',
            'Search documentation or online resources',
            'Consider reaching out for additional support'
          ],
          confidence: 0.4,
          estimatedTime: '15-60 minutes',
          riskLevel: 'medium'
        });
    }

    return solutions;
  }

  private scanFileForIssues(content: string, filePath: string): DetectedIssue[] {
    const issues: DetectedIssue[] = [];
    const lines = content.split('\n');

    lines.forEach((line, index) => {
      // Check for common issues
      if (line.includes('console.log') && filePath.includes('prod')) {
        issues.push({
          type: 'debug-code-in-production',
          description: 'Debug console.log found in production code',
          severity: 'medium',
          location: { file: filePath, line: index + 1 }
        });
      }

      if (line.includes('TODO') || line.includes('FIXME')) {
        issues.push({
          type: 'unfinished-code',
          description: 'Unfinished code detected (TODO/FIXME)',
          severity: 'low',
          location: { file: filePath, line: index + 1 }
        });
      }

      if (line.includes('throw new Error') && !line.includes('//')) {
        issues.push({
          type: 'unhandled-error',
          description: 'Potentially unhandled error throw',
          severity: 'medium',
          location: { file: filePath, line: index + 1 }
        });
      }
    });

    return issues;
  }

  private extractErrorsFromLogs(logLines: string[]): Array<{message: string, severity: 'critical' | 'high' | 'medium' | 'low', lineNumber: number}> {
    const errors: Array<{message: string, severity: 'critical' | 'high' | 'medium' | 'low', lineNumber: number}> = [];

    logLines.forEach((line, index) => {
      const lowerLine = line.toLowerCase();
      
      if (lowerLine.includes('error') || lowerLine.includes('exception')) {
        errors.push({
          message: line.trim(),
          severity: 'high',
          lineNumber: index + 1
        });
      } else if (lowerLine.includes('fatal') || lowerLine.includes('critical')) {
        errors.push({
          message: line.trim(),
          severity: 'critical',
          lineNumber: index + 1
        });
      } else if (lowerLine.includes('warn') || lowerLine.includes('warning')) {
        errors.push({
          message: line.trim(),
          severity: 'medium',
          lineNumber: index + 1
        });
      }
    });

    return errors;
  }

  private parseTypeScriptErrors(stderr: string): Array<{message: string, file?: string, line?: number}> {
    const errors: Array<{message: string, file?: string, line?: number}> = [];
    const lines = stderr.split('\n');

    for (const line of lines) {
      const match = line.match(/^(.+?)(\((\d+),(\d+)\))?: error TS\d+: (.+)$/);
      if (match) {
        errors.push({
          message: match[5],
          file: match[1],
          line: match[3] ? parseInt(match[3]) : undefined
        });
      }
    }

    return errors;
  }

  private getSeverityScore(severity: string): number {
    switch (severity) {
      case 'critical': return 4;
      case 'high': return 3;
      case 'medium': return 2;
      case 'low': return 1;
      default: return 0;
    }
  }

  private async fileExists(filePath: string): Promise<boolean> {
    try {
      await fs.access(filePath);
      return true;
    } catch {
      return false;
    }
  }

  private generateSummary(results: TroubleshootResult[]): string {
    if (results.length === 0) {
      return 'No issues detected. System appears to be healthy.';
    }

    let summary = `Found ${results.length} issue(s)\n\n`;

    const severityCounts = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0
    };

    results.forEach(result => {
      severityCounts[result.issue.severity]++;
    });

    if (severityCounts.critical > 0) {
      summary += `🚨 Critical: ${severityCounts.critical}\n`;
    }
    if (severityCounts.high > 0) {
      summary += `🔥 High: ${severityCounts.high}\n`;
    }
    if (severityCounts.medium > 0) {
      summary += `⚠️  Medium: ${severityCounts.medium}\n`;
    }
    if (severityCounts.low > 0) {
      summary += `ℹ️  Low: ${severityCounts.low}\n`;
    }

    const topIssue = results[0];
    summary += `\nTop issue: ${topIssue.issue.description}`;

    return summary;
  }
}