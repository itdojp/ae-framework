/**
 * Unified Troubleshoot Command for ae-framework
 * Provides intelligent debugging and problem diagnosis with unified interface
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { 
  TroubleshootResult, 
  AnalysisTarget, 
  TroubleshootOptions,
  DetectedIssue,
  Diagnosis,
  Solution,
  Issue
} from './types.js';

export class UnifiedTroubleshootCommand extends BaseExtendedCommand {
  constructor() {
    super({
      name: '/ae:troubleshoot',
      description: 'Intelligent debugging and problem diagnosis',
      usage: '/ae:troubleshoot [description] [--auto] [--logs=path] [--error="error message"] [--validate]',
      aliases: ['/troubleshoot', '/a:troubleshoot'],
      category: 'utility'
    });
  }

  protected validateArgs(args: string[]): { isValid: boolean; message?: string } {
    // Troubleshoot can work with or without arguments
    return { isValid: true };
  }

  protected parseOptions(args: string[]): TroubleshootOptions {
    const baseOptions = super.parseOptions(args);
    
    return {
      ...baseOptions,
      auto: args.includes('--auto'),
      logs: args.find(arg => arg.startsWith('--logs='))?.split('=')[1],
      error: args.find(arg => arg.startsWith('--error='))?.split('=')[1],
      interactive: args.includes('--interactive')
    };
  }

  protected async execute(
    args: string[], 
    options: TroubleshootOptions, 
    context: CommandContext
  ): Promise<ExtendedCommandResult<TroubleshootResult>> {
    try {
      // Determine what we're troubleshooting
      const description = this.extractDescription(args);
      const analysisTarget: AnalysisTarget = {
        path: context.projectRoot,
        type: 'directory'
      };

      const result = await this.performTroubleshooting(analysisTarget, description, options, context);
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
        message: `Troubleshooting failed: ${error.message}`,
        metrics: {
          executionTime: 0,
          filesProcessed: 0
        }
      };
    }
  }

  private extractDescription(args: string[]): string {
    // Extract non-option arguments as description
    const description = args
      .filter(arg => !arg.startsWith('--'))
      .join(' ')
      .trim();
    
    return description || 'General troubleshooting';
  }

  private async performTroubleshooting(
    target: AnalysisTarget, 
    description: string, 
    options: TroubleshootOptions,
    context: CommandContext
  ): Promise<TroubleshootResult> {
    const startTime = Date.now();
    
    const detectedIssues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];
    const issues: Issue[] = [];
    const suggestions: any[] = [];

    // Auto-detect common issues if --auto flag is used
    if (options.auto || !description || description === 'General troubleshooting') {
      const autoDetected = await this.autoDetectIssues(target.path, context);
      detectedIssues.push(...autoDetected.issues);
      diagnosis.push(...autoDetected.diagnosis);
      solutions.push(...autoDetected.solutions);
    }

    // Analyze specific error message if provided
    if (options.error) {
      const errorAnalysis = this.analyzeErrorMessage(options.error);
      detectedIssues.push(...errorAnalysis.issues);
      diagnosis.push(...errorAnalysis.diagnosis);
      solutions.push(...errorAnalysis.solutions);
    }

    // Analyze logs if provided
    if (options.logs) {
      const logAnalysis = await this.analyzeLogs(options.logs);
      detectedIssues.push(...logAnalysis.issues);
      diagnosis.push(...logAnalysis.diagnosis);
      solutions.push(...logAnalysis.solutions);
    }

    // Analyze description for known patterns
    if (description && description !== 'General troubleshooting') {
      const descriptionAnalysis = this.analyzeDescription(description);
      detectedIssues.push(...descriptionAnalysis.issues);
      diagnosis.push(...descriptionAnalysis.diagnosis);
      solutions.push(...descriptionAnalysis.solutions);
    }

    return {
      target,
      summary: this.createTroubleshootSummary(detectedIssues.length, solutions.length),
      issues,
      suggestions,
      metrics: {
        lines: 0,
        files: 1,
        complexity: this.calculateComplexityScore(detectedIssues, diagnosis)
      },
      metadata: {
        timestamp: new Date().toISOString(),
        commandType: 'troubleshoot',
        processingTime: Date.now() - startTime
      },
      detectedIssues,
      diagnosis,
      solutions
    };
  }

  private async autoDetectIssues(projectPath: string, context: CommandContext): Promise<{
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  }> {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    try {
      // Check package.json issues
      const packageAnalysis = await this.checkPackageJson(projectPath);
      issues.push(...packageAnalysis.issues);
      diagnosis.push(...packageAnalysis.diagnosis);
      solutions.push(...packageAnalysis.solutions);

      // Check for build/test failures
      const buildAnalysis = await this.checkBuildStatus(projectPath);
      issues.push(...buildAnalysis.issues);
      diagnosis.push(...buildAnalysis.diagnosis);
      solutions.push(...buildAnalysis.solutions);

      // Check common file issues
      const fileAnalysis = await this.checkCommonFileIssues(projectPath);
      issues.push(...fileAnalysis.issues);
      diagnosis.push(...fileAnalysis.diagnosis);
      solutions.push(...fileAnalysis.solutions);

      // Check TypeScript configuration
      const tsAnalysis = await this.checkTypeScriptConfig(projectPath);
      issues.push(...tsAnalysis.issues);
      diagnosis.push(...tsAnalysis.diagnosis);
      solutions.push(...tsAnalysis.solutions);

    } catch (error) {
      // If auto-detection fails, continue with empty results
    }

    return { issues, diagnosis, solutions };
  }

  private async checkPackageJson(projectPath: string): Promise<{
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  }> {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    try {
      const packagePath = path.join(projectPath, 'package.json');
      const packageContent = await fs.readFile(packagePath, 'utf-8');
      const packageJson = JSON.parse(packageContent);

      // Check for missing dependencies
      if (!packageJson.dependencies && !packageJson.devDependencies) {
        issues.push({
          type: 'dependency-issue',
          severity: 'medium',
          message: 'No dependencies found in package.json',
          location: { file: packagePath }
        });
        
        diagnosis.push({
          rootCause: 'Missing or empty dependencies section in package.json',
          affectedComponents: ['Build system', 'Runtime'],
          impact: 'Project cannot run or build without dependencies',
          confidence: 0.8
        });

        solutions.push({
          description: 'Add required dependencies to package.json',
          steps: [
            'Run "npm install <package-name>" to add runtime dependencies',
            'Run "npm install --save-dev <package-name>" to add development dependencies',
            'Check if package-lock.json exists and is not corrupted'
          ],
          confidence: 0.9,
          estimatedTime: '5-10 minutes',
          riskLevel: 'low'
        });
      }

      // Check for security vulnerabilities
      if (packageJson.dependencies) {
        // This is a simplified check - in practice you'd use npm audit or similar
        const outdatedPackages = Object.keys(packageJson.dependencies).filter(dep => 
          packageJson.dependencies[dep].includes('^0.') || packageJson.dependencies[dep].includes('~0.')
        );

        if (outdatedPackages.length > 0) {
          issues.push({
            type: 'security-vulnerability',
            severity: 'high',
            message: `Potentially outdated packages found: ${outdatedPackages.slice(0, 3).join(', ')}`,
            location: { file: packagePath }
          });
        }
      }

    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
        issues.push({
          type: 'missing-file',
          severity: 'critical',
          message: 'package.json not found',
          location: { file: path.join(projectPath, 'package.json') }
        });

        solutions.push({
          description: 'Create package.json file',
          steps: [
            'Run "npm init" to create a new package.json',
            'Answer the prompts or use "npm init -y" for defaults',
            'Add necessary dependencies and scripts'
          ],
          confidence: 0.95,
          estimatedTime: '2-5 minutes',
          riskLevel: 'low'
        });
      }
    }

    return { issues, diagnosis, solutions };
  }

  private async checkBuildStatus(projectPath: string): Promise<{
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  }> {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    try {
      // Check for common build output directories
      const distPath = path.join(projectPath, 'dist');
      const buildPath = path.join(projectPath, 'build');
      const libPath = path.join(projectPath, 'lib');

      let buildOutputExists = false;
      for (const outputPath of [distPath, buildPath, libPath]) {
        try {
          await fs.access(outputPath);
          buildOutputExists = true;
          break;
        } catch {
          // Directory doesn't exist, continue checking
        }
      }

      if (!buildOutputExists) {
        issues.push({
          type: 'build-issue',
          severity: 'medium',
          message: 'No build output directory found (dist, build, or lib)',
          location: { file: projectPath }
        });

        diagnosis.push({
          rootCause: 'Project has not been built or build output was cleared',
          affectedComponents: ['Runtime', 'Deployment'],
          impact: 'Application cannot be run in production',
          confidence: 0.7
        });

        solutions.push({
          description: 'Build the project',
          steps: [
            'Check package.json for build script',
            'Run "npm run build" or equivalent build command',
            'Verify build output is generated',
            'Check for build errors in console output'
          ],
          confidence: 0.8,
          estimatedTime: '2-10 minutes',
          riskLevel: 'low'
        });
      }

      // Check for TypeScript compilation issues
      const tsconfigPath = path.join(projectPath, 'tsconfig.json');
      try {
        await fs.access(tsconfigPath);
        // If tsconfig exists but no build output, likely compilation issue
        if (!buildOutputExists) {
          issues.push({
            type: 'typescript-compilation',
            severity: 'high',
            message: 'TypeScript project detected but no compiled output found',
            location: { file: tsconfigPath }
          });
        }
      } catch {
        // No TypeScript config, skip TS-specific checks
      }

    } catch (error) {
      // Error checking build status, continue
    }

    return { issues, diagnosis, solutions };
  }

  private async checkCommonFileIssues(projectPath: string): Promise<{
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  }> {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    try {
      // Check for node_modules
      const nodeModulesPath = path.join(projectPath, 'node_modules');
      try {
        await fs.access(nodeModulesPath);
      } catch {
        issues.push({
          type: 'missing-dependencies',
          severity: 'critical',
          message: 'node_modules directory not found',
          location: { file: nodeModulesPath }
        });

        diagnosis.push({
          rootCause: 'Dependencies have not been installed',
          affectedComponents: ['All modules', 'Build system', 'Runtime'],
          impact: 'Project cannot run without installed dependencies',
          confidence: 0.95
        });

        solutions.push({
          description: 'Install project dependencies',
          steps: [
            'Run "npm install" to install all dependencies',
            'If using yarn: "yarn install"',
            'Check for any installation errors',
            'Verify node_modules directory is created'
          ],
          confidence: 0.95,
          estimatedTime: '1-5 minutes',
          riskLevel: 'low'
        });
      }

      // Check for common config files
      const configFiles = ['.gitignore', 'README.md', '.env.example'];
      for (const configFile of configFiles) {
        const filePath = path.join(projectPath, configFile);
        try {
          await fs.access(filePath);
        } catch {
          if (configFile === '.gitignore') {
            issues.push({
              type: 'missing-config',
              severity: 'low',
              message: '.gitignore file missing - may commit sensitive files',
              location: { file: filePath }
            });
          }
        }
      }

    } catch (error) {
      // Error checking common files, continue
    }

    return { issues, diagnosis, solutions };
  }

  private async checkTypeScriptConfig(projectPath: string): Promise<{
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  }> {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    try {
      const tsconfigPath = path.join(projectPath, 'tsconfig.json');
      const tsconfigContent = await fs.readFile(tsconfigPath, 'utf-8');
      const tsconfig = JSON.parse(tsconfigContent);

      // Check for common TypeScript configuration issues
      if (!tsconfig.compilerOptions?.target) {
        issues.push({
          type: 'config-issue',
          severity: 'medium',
          message: 'TypeScript target not specified in tsconfig.json',
          location: { file: tsconfigPath }
        });
      }

      if (!tsconfig.compilerOptions?.outDir) {
        issues.push({
          type: 'config-issue',
          severity: 'low',
          message: 'TypeScript output directory not specified',
          location: { file: tsconfigPath }
        });
      }

      if (tsconfig.compilerOptions?.strict === false) {
        issues.push({
          type: 'config-issue',
          severity: 'medium',
          message: 'TypeScript strict mode is disabled - may cause runtime errors',
          location: { file: tsconfigPath }
        });

        solutions.push({
          description: 'Enable TypeScript strict mode',
          steps: [
            'Set "strict": true in tsconfig.json compilerOptions',
            'Fix any type errors that appear',
            'Consider enabling individual strict flags if full strict mode is too restrictive'
          ],
          confidence: 0.8,
          estimatedTime: '10-30 minutes',
          riskLevel: 'medium'
        });
      }

    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT') {
        issues.push({
          type: 'config-issue',
          severity: 'medium',
          message: 'Invalid or malformed tsconfig.json',
          location: { file: path.join(projectPath, 'tsconfig.json') }
        });
      }
    }

    return { issues, diagnosis, solutions };
  }

  private analyzeErrorMessage(errorMessage: string): {
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  } {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    // Common error patterns
    const errorPatterns = [
      {
        pattern: /Cannot find module ['"]([^'"]+)['"]/,
        type: 'module-not-found',
        severity: 'high' as const,
        getDiagnosis: (match: RegExpMatchArray) => ({
          rootCause: `Module "${match[1]}" is not installed or not found`,
          affectedComponents: ['Runtime', 'Build system'],
          impact: 'Application cannot start or build',
          confidence: 0.9
        }),
        getSolution: (match: RegExpMatchArray) => ({
          description: `Install missing module: ${match[1]}`,
          steps: [
            `Run "npm install ${match[1]}" to install the module`,
            'Check if the module name is correct',
            'Verify the module exists in npm registry',
            'Check import/require statement syntax'
          ],
          confidence: 0.9,
          estimatedTime: '2-5 minutes',
          riskLevel: 'low' as const
        })
      },
      {
        pattern: /SyntaxError/,
        type: 'syntax-error',
        severity: 'critical' as const,
        getDiagnosis: () => ({
          rootCause: 'Code contains syntax errors preventing execution',
          affectedComponents: ['Parser', 'Runtime'],
          impact: 'Code cannot be parsed or executed',
          confidence: 0.95
        }),
        getSolution: () => ({
          description: 'Fix syntax errors in code',
          steps: [
            'Check the error location and line number',
            'Look for missing brackets, semicolons, or quotes',
            'Use IDE/editor with syntax highlighting',
            'Run linter to identify syntax issues'
          ],
          confidence: 0.8,
          estimatedTime: '5-15 minutes',
          riskLevel: 'low' as const
        })
      },
      {
        pattern: /port.*already in use|EADDRINUSE/i,
        type: 'port-conflict',
        severity: 'medium' as const,
        getDiagnosis: () => ({
          rootCause: 'Another process is already using the required port',
          affectedComponents: ['Server', 'Network'],
          impact: 'Cannot start server on specified port',
          confidence: 0.9
        }),
        getSolution: () => ({
          description: 'Resolve port conflict',
          steps: [
            'Find process using the port: "lsof -i :PORT" or "netstat -ano | findstr :PORT"',
            'Kill the conflicting process or use a different port',
            'Update configuration to use available port',
            'Consider using PORT environment variable for flexibility'
          ],
          confidence: 0.85,
          estimatedTime: '3-10 minutes',
          riskLevel: 'low' as const
        })
      },
      {
        pattern: /CORS|Cross-Origin/i,
        type: 'cors-error',
        severity: 'medium' as const,
        getDiagnosis: () => ({
          rootCause: 'Cross-Origin Resource Sharing (CORS) policy blocking request',
          affectedComponents: ['Frontend', 'API', 'Browser'],
          impact: 'Frontend cannot communicate with API',
          confidence: 0.8
        }),
        getSolution: () => ({
          description: 'Configure CORS properly',
          steps: [
            'Add appropriate CORS headers to server responses',
            'Install and configure CORS middleware (e.g., cors package)',
            'Ensure frontend and backend domains are properly configured',
            'Check browser developer tools for specific CORS errors'
          ],
          confidence: 0.8,
          estimatedTime: '10-20 minutes',
          riskLevel: 'low' as const
        })
      }
    ];

    // Analyze error message against known patterns
    for (const pattern of errorPatterns) {
      const match = errorMessage.match(pattern.pattern);
      if (match) {
        issues.push({
          type: pattern.type,
          severity: pattern.severity,
          message: errorMessage,
          location: {},
          stackTrace: errorMessage,
          reproducible: true
        });

        diagnosis.push(pattern.getDiagnosis(match));
        solutions.push(pattern.getSolution(match));
        break; // Only match the first pattern
      }
    }

    // If no specific pattern matched, provide generic analysis
    if (issues.length === 0) {
      issues.push({
        type: 'unknown-error',
        severity: 'medium',
        message: errorMessage,
        location: {},
        stackTrace: errorMessage
      });

      diagnosis.push({
        rootCause: 'Unknown error - requires manual analysis',
        affectedComponents: ['Unknown'],
        impact: 'Application behavior may be affected',
        confidence: 0.3
      });

      solutions.push({
        description: 'General troubleshooting steps',
        steps: [
          'Search for the exact error message online',
          'Check recent code changes that might have introduced the issue',
          'Review relevant documentation and logs',
          'Consider creating a minimal reproduction case'
        ],
        confidence: 0.5,
        estimatedTime: '15-30 minutes',
        riskLevel: 'low'
      });
    }

    return { issues, diagnosis, solutions };
  }

  private async analyzeLogs(logsPath: string): Promise<{
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  }> {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    try {
      const logContent = await fs.readFile(logsPath, 'utf-8');
      const lines = logContent.split('\n');

      // Look for error patterns in logs
      const errorLines = lines.filter(line => 
        line.toLowerCase().includes('error') || 
        line.toLowerCase().includes('fail') ||
        line.toLowerCase().includes('exception')
      );

      if (errorLines.length > 0) {
        // Analyze most recent errors
        const recentErrors = errorLines.slice(-5);
        
        for (const errorLine of recentErrors) {
          issues.push({
            type: 'log-error',
            severity: 'medium',
            message: errorLine.trim(),
            location: { file: logsPath },
            frequency: errorLines.filter(line => line.includes(errorLine.split(' ')[0])).length
          });
        }

        diagnosis.push({
          rootCause: 'Multiple errors detected in log files',
          affectedComponents: ['Application runtime'],
          impact: 'Application may be experiencing issues',
          confidence: 0.7
        });

        solutions.push({
          description: 'Investigate log errors',
          steps: [
            'Review the most recent error messages in detail',
            'Check for patterns or recurring errors',
            'Correlate errors with recent code changes',
            'Increase logging level for more detailed information'
          ],
          confidence: 0.6,
          estimatedTime: '10-30 minutes',
          riskLevel: 'low'
        });
      }

    } catch (error) {
      issues.push({
        type: 'log-access-error',
        severity: 'low',
        message: `Cannot access log file: ${logsPath}`,
        location: { file: logsPath }
      });
    }

    return { issues, diagnosis, solutions };
  }

  private analyzeDescription(description: string): {
    issues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
  } {
    const issues: DetectedIssue[] = [];
    const diagnosis: Diagnosis[] = [];
    const solutions: Solution[] = [];

    // Keywords that indicate specific problem categories
    const keywords = {
      performance: ['slow', 'performance', 'lag', 'timeout', 'hang'],
      dependency: ['install', 'dependency', 'module', 'package', 'npm', 'yarn'],
      build: ['build', 'compile', 'webpack', 'rollup', 'vite', 'parcel'],
      test: ['test', 'jest', 'mocha', 'cypress', 'testing'],
      server: ['server', 'port', 'connection', 'network', 'api'],
      database: ['database', 'db', 'sql', 'mongo', 'connection']
    };

    const lowerDescription = description.toLowerCase();

    for (const [category, categoryKeywords] of Object.entries(keywords)) {
      if (categoryKeywords.some(keyword => lowerDescription.includes(keyword))) {
        issues.push({
          type: `${category}-issue`,
          severity: 'medium',
          message: `Potential ${category} related issue: ${description}`,
          location: {}
        });

        diagnosis.push({
          rootCause: `Issue appears to be related to ${category} based on description`,
          affectedComponents: [category.charAt(0).toUpperCase() + category.slice(1)],
          impact: `${category} functionality may be affected`,
          confidence: 0.6
        });

        solutions.push({
          description: `Troubleshoot ${category} issues`,
          steps: this.getCategorySolutions(category),
          confidence: 0.6,
          estimatedTime: '10-30 minutes',
          riskLevel: 'low'
        });
        break; // Only match first category
      }
    }

    return { issues, diagnosis, solutions };
  }

  private getCategorySolutions(category: string): string[] {
    const solutionMap: Record<string, string[]> = {
      performance: [
        'Profile the application to identify bottlenecks',
        'Check for memory leaks or excessive resource usage',
        'Review recent code changes that might affect performance',
        'Monitor system resources (CPU, memory, disk I/O)'
      ],
      dependency: [
        'Check package.json for correct dependencies',
        'Clear node_modules and reinstall: rm -rf node_modules && npm install',
        'Check for version conflicts in package-lock.json',
        'Verify npm/yarn cache is not corrupted'
      ],
      build: [
        'Check build configuration files',
        'Clear build cache and rebuild from scratch',
        'Review build logs for specific error messages',
        'Verify all source files are present and accessible'
      ],
      test: [
        'Check test configuration files',
        'Verify test environment setup',
        'Review test output for specific failures',
        'Update test dependencies if needed'
      ],
      server: [
        'Check server configuration and port settings',
        'Verify network connectivity and firewall rules',
        'Review server logs for error messages',
        'Test with a simple HTTP request to isolate the issue'
      ],
      database: [
        'Verify database connection settings',
        'Check database server status and logs',
        'Test database connectivity with a simple query',
        'Review database migrations and schema changes'
      ]
    };

    return solutionMap[category] || [
      'Review the problem description for more specific details',
      'Check logs and error messages for additional information',
      'Consider creating a minimal reproduction case',
      'Consult relevant documentation and community resources'
    ];
  }

  private calculateComplexityScore(issues: DetectedIssue[], diagnosis: Diagnosis[]): number {
    let score = 0;
    
    // Add points based on issue severity
    for (const issue of issues) {
      switch (issue.severity) {
        case 'critical': score += 5; break;
        case 'high': score += 3; break;
        case 'medium': score += 2; break;
        case 'low': score += 1; break;
      }
    }

    // Add points based on diagnosis confidence (inverse relationship)
    for (const diag of diagnosis) {
      score += Math.round((1 - diag.confidence) * 3);
    }

    return score;
  }

  private calculateOverallConfidence(result: TroubleshootResult): number {
    if (result.diagnosis.length === 0) return 0.5;
    
    const avgConfidence = result.diagnosis.reduce((sum, diag) => sum + diag.confidence, 0) / result.diagnosis.length;
    return avgConfidence;
  }

  private createTroubleshootSummary(issueCount: number, solutionCount: number): string {
    return `Found ${issueCount} issue(s) with ${solutionCount} suggested solution(s)`;
  }

  protected generateValidationClaim(data: TroubleshootResult): string {
    return `Troubleshooting analysis for ${data.target.path}: ${data.detectedIssues.length} issues detected with ${data.solutions.length} solutions provided`;
  }

  protected generateSummary(data: TroubleshootResult): string {
    return data.summary;
  }
}