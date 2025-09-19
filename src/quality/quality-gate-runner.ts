/**
 * Quality Gate Runner
 * Executes quality gates based on centralized policy configuration
 */

import { spawn, exec } from 'child_process';
import { promisify } from 'util';
import * as fs from 'fs';
import * as path from 'path';
import { buildReportMeta } from '../utils/meta-factory.js';
import { QualityPolicyLoader, type QualityGateResult, type QualityReport, type QualityGate } from './policy-loader.js';

type CoverageThreshold = { lines?: number; functions?: number; branches?: number; statements?: number };
type LintThreshold = { maxErrors?: number; maxWarnings?: number };
type SecurityThreshold = { maxCritical?: number; maxHigh?: number; maxMedium?: number };
type PerfThreshold = Record<string, number | undefined>;
type A11yThreshold = Record<string, number | undefined>;

// Mock telemetry for main branch compatibility
type Attributes = Record<string, unknown>;
const mockTelemetry = {
  createTimer: (name: string, attributes?: Attributes) => ({
    end: (additionalAttributes?: Attributes) => Date.now(),
  }),
  recordQualityMetrics: (metrics: Attributes) => {},
  recordCounter: (name: string, value: number, attributes?: Attributes) => {},
};

const TELEMETRY_ATTRIBUTES = {
  SERVICE_COMPONENT: 'service.component',
  SERVICE_OPERATION: 'service.operation',
};

const execAsync = promisify(exec);

export interface QualityGateExecutionOptions {
  environment?: string;
  gates?: string[];
  parallel?: boolean;
  timeout?: number;
  dryRun?: boolean;
  verbose?: boolean;
  outputDir?: string;
}

export class QualityGateRunner {
  private policyLoader: QualityPolicyLoader;
  private results: QualityGateResult[] = [];

  constructor(policyLoader?: QualityPolicyLoader) {
    this.policyLoader = policyLoader || new QualityPolicyLoader();
  }

  /**
   * Execute quality gates for environment
   */
  public async executeGates(options: QualityGateExecutionOptions = {}): Promise<QualityReport> {
    const {
      environment = process.env['NODE_ENV'] || 'development',
      gates: requestedGates,
      parallel = true,
      timeout = 300000, // 5 minutes default
      dryRun = false,
      verbose = false,
      outputDir = 'reports/quality-gates',
    } = options;

    const timer = mockTelemetry.createTimer('quality_gates.execution.total', {
      [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'quality-gates',
      environment,
    });

    try {
      console.log(`🔍 Executing quality gates for environment: ${environment}`);
      
      // Get gates to execute
      const allGates = requestedGates
        ? requestedGates.map(name => {
            const gates = this.policyLoader.getAllGates();
            if (!gates[name]) {
              throw new Error(`Quality gate '${name}' not found`);
            }
            return gates[name];
          })
        : this.policyLoader.getGatesForEnvironment(environment);

      if (allGates.length === 0) {
        console.log('⚠️  No quality gates found for execution');
        return this.generateEmptyReport(environment);
      }

      console.log(`📋 Found ${allGates.length} quality gates to execute`);
      if (verbose) {
        allGates.forEach(gate => {
          console.log(`   • ${gate.name} (${gate.category})`);
        });
      }

      // Execute gates
      this.results = [];
      if (parallel) {
        console.log('🚀 Executing gates in parallel...');
        const promises = allGates.map(gate => this.executeGate(gate, environment, { timeout, dryRun, verbose }));
        this.results = await Promise.all(promises);
      } else {
        console.log('⏭️  Executing gates sequentially...');
        for (const gate of allGates) {
          const result = await this.executeGate(gate, environment, { timeout, dryRun, verbose });
          this.results.push(result);
        }
      }

      // Generate report
      const report = this.policyLoader.generateReport(this.results, environment);
      
      // Save report
      if (!dryRun) {
        await this.saveReport(report, outputDir);
      }

      // Record metrics
      mockTelemetry.recordQualityMetrics({
        score: report.overallScore,
        coverage: (report.passedGates / report.totalGates) * 100,
        phase: 'quality-gates',
        component: 'runner',
      });

      const executionTime = timer.end({
        total_gates: report.totalGates,
        passed_gates: report.passedGates,
        failed_gates: report.failedGates,
        overall_score: report.overallScore,
      });

      // Print summary
      this.printSummary(report, verbose);

      return report;

    } catch (error) {
      timer.end({ result: 'error' });
      console.error('❌ Error executing quality gates:', error);
      throw error;
    }
  }

  /**
   * Execute a single quality gate
   */
  private async executeGate(
    gate: QualityGate,
    environment: string,
    options: { timeout: number; dryRun: boolean; verbose: boolean }
  ): Promise<QualityGateResult> {
    const { timeout, dryRun, verbose } = options;
    
    const gateTimer = mockTelemetry.createTimer('quality_gates.gate.execution', {
      [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'quality-gate',
      gate_name: gate.name,
      gate_category: gate.category,
      environment,
    });

    try {
      if (verbose) {
        console.log(`\n🔍 Executing: ${gate.name}`);
        console.log(`   Description: ${gate.description}`);
        console.log(`   Command: ${gate.commands.test}`);
      }

      const threshold = this.policyLoader.getThreshold(gate.name, environment);
      
      if (dryRun) {
        console.log(`   🔄 DRY RUN: Would execute '${gate.commands.test}'`);
        return {
          gateName: gate.name,
          passed: true,
          score: 100,
          violations: [],
          executionTime: 0,
          environment,
          threshold,
          details: { dryRun: true },
        };
      }

      // Execute the gate command
      const startTime = Date.now();
      const result = await this.executeCommand(gate.commands.test, timeout);
      const executionTime = Date.now() - startTime;

      // Parse result based on gate type
      const gateResult = await this.parseGateResult(
        gate,
        result,
        this.pickNumericThresholds(threshold as unknown as Record<string, unknown>),
        environment,
        executionTime
      );

      gateTimer.end({
        result: gateResult.passed ? 'success' : 'failure',
        score: gateResult.score || 0,
        violations: gateResult.violations.length,
      });

      if (verbose) {
        console.log(`   ${gateResult.passed ? '✅' : '❌'} Result: ${gateResult.passed ? 'PASSED' : 'FAILED'}`);
        if (gateResult.score !== undefined) {
          console.log(`   📊 Score: ${gateResult.score}`);
        }
        if (gateResult.violations.length > 0) {
          console.log(`   ⚠️  Violations: ${gateResult.violations.length}`);
        }
      }

      return gateResult;

    } catch (error) {
      const executionTime = gateTimer.end({ result: 'error' });
      
      console.error(`❌ Error executing gate '${gate.name}':`, error);
      
      return {
        gateName: gate.name,
        passed: false,
        violations: [`Execution error: ${error}`],
        executionTime,
        environment,
        threshold: this.policyLoader.getThreshold(gate.name, environment),
        details: { error: String(error) },
      };
    }
  }

  /**
   * Execute a command with timeout
   */
  private async executeCommand(command: string, timeout: number): Promise<{ stdout: string; stderr: string; code: number }> {
    return new Promise((resolve, reject) => {
      // Check if command needs shell features (pipes, redirects, etc.)
      const needsShell = command.includes('|') || command.includes('>') || command.includes('<') || 
                        command.includes('&&') || command.includes('||') || command.includes('$');
      
      let process: import('child_process').ChildProcessWithoutNullStreams;
      
      if (needsShell) {
        // Use shell for complex commands with enhanced security validation
        this.validateShellCommand(command);
        process = spawn(command, {
          shell: true,
          stdio: ['pipe', 'pipe', 'pipe'],
          timeout,
        });
      } else {
        // Parse command to avoid shell injection for simple commands
        const commandParts = this.parseCommand(command);
        const [execName, ...args] = commandParts as [string, ...string[]];
        process = spawn(execName, args, {
          stdio: ['pipe', 'pipe', 'pipe'],
          timeout,
        });
      }

      let stdout = '';
      let stderr = '';
      let finished = false;

      process.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      process.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      process.on('close', (code) => {
        if (!finished) {
          finished = true;
          clearTimeout(timeoutHandle);
          resolve({ stdout, stderr, code: code || 0 });
        }
      });

      process.on('error', (error) => {
        if (!finished) {
          finished = true;
          clearTimeout(timeoutHandle);
          reject(error);
        }
      });

      // Handle timeout with proper cleanup
      const timeoutHandle = setTimeout(() => {
        if (!finished) {
          finished = true;
          process.kill('SIGTERM');
          reject(new Error(`Command timed out after ${timeout}ms`));
        }
      }, timeout);
    });
  }

  /**
   * Parse command string into executable and arguments safely
   */
  private parseCommand(command: string): string[] {
    // Simple command parsing to avoid shell injection
    // For production use, consider using a proper shell parser library
    const trimmed = command.trim();
    
    // Handle npm/npx commands specially as they are common in quality gates
    if (trimmed.startsWith('npm ') || trimmed.startsWith('npx ')) {
      return trimmed.split(/\s+/);
    }
    
    // For other commands, use a basic splitting approach
    // In a production environment, consider using a library like shell-quote
    const parts = trimmed.split(/\s+/);
    
    // Security validation - use allowlist for common commands, blacklist for dangerous ones
    const executable = parts[0];
    if (!executable) {
      throw new Error('Empty command');
    }
    
    // Allowlist of commonly used quality gate commands
    const allowedCommands = [
      'npm', 'npx', 'yarn', 'pnpm', 'node',
      'jest', 'mocha', 'vitest', 'nyc',
      'eslint', 'prettier', 'tsc', 'tslint',
      'lighthouse', 'axe', 'pa11y',
      'audit', 'license-checker'
    ];
    
    // Dangerous commands that should never be allowed
    const dangerousCommands = [
      'rm', 'rmdir', 'del', 'sudo', 'su',
      'curl', 'wget', 'eval', 'exec',
      'bash', 'sh', 'zsh', 'fish',
      'chmod', 'chown', 'kill', 'killall'
    ];
    
    if (dangerousCommands.includes(executable)) {
      throw new Error(`Command '${executable}' is not allowed for security reasons`);
    }
    
    // For non-allowlisted commands, require they don't start with dangerous prefixes
    if (!allowedCommands.includes(executable)) {
      console.warn(`⚠️ Command '${executable}' is not in the allowlist. Proceeding with caution.`);
      
      // Additional check for suspicious patterns
      if (executable.includes('/') || executable.includes('\\') || executable.startsWith('.')) {
        throw new Error(`Command '${executable}' contains suspicious path characters`);
      }
    }
    return parts;
  }

  /**
   * Validate shell commands for security
   */
  private validateShellCommand(command: string): void {
    // Check for obviously dangerous patterns
    const dangerousPatterns = [
      /rm\s+-rf/,           // Dangerous rm commands
      /sudo\s+/,            // Sudo usage
      /su\s+/,              // Su usage  
      /eval\s+/,            // Eval usage
      /exec\s+/,            // Exec usage
      /\$\(/,               // Command substitution
      /`[^`]*`/,            // Backtick command substitution
      /wget\s+/,            // Network downloads
      /curl\s+.*-o/,        // Curl with output to file
      />\s*\/etc/,          // Writing to system directories
      />\s*\/usr/,
      />\s*\/bin/,
    ];

    for (const pattern of dangerousPatterns) {
      if (pattern.test(command)) {
        throw new Error(`Command contains dangerous pattern: ${pattern.source}`);
      }
    }

    console.log(`ℹ️ Using shell mode for command: ${command.substring(0, 50)}...`);
  }

  private pickNumericThresholds(input: Record<string, unknown>): Record<string, number | undefined> {
    const out: Record<string, number | undefined> = {};
    for (const [k, v] of Object.entries(input)) {
      if (typeof v === 'number') out[k] = v;
    }
    return out;
  }

  /**
   * Parse gate execution result
   */
  private async parseGateResult(
    gate: QualityGate,
    result: { stdout: string; stderr: string; code: number },
    threshold: Record<string, number | undefined>,
    environment: string,
    executionTime: number
  ): Promise<QualityGateResult> {
    const baseResult: QualityGateResult = {
      gateName: gate.name,
      passed: result.code === 0,
      violations: [],
      executionTime,
      environment,
      threshold,
    };

    // Parse based on gate category
    switch (gate.category) {
      case 'testing':
        return this.parseCoverageResult(baseResult, result, this.pickNumericThresholds(threshold));
      
      case 'code-quality':
        return this.parseLintingResult(baseResult, result, threshold as LintThreshold);
      
      case 'security':
        return this.parseSecurityResult(baseResult, result, threshold as SecurityThreshold);
      
      case 'performance':
        return this.parsePerformanceResult(baseResult, result, this.pickNumericThresholds(threshold));
      
      case 'frontend':
        return this.parseAccessibilityResult(baseResult, result, this.pickNumericThresholds(threshold));
      
      default:
        // Generic parsing
        if (result.code !== 0) {
          baseResult.violations.push(`Command failed with exit code ${result.code}`);
          if (result.stderr) {
            baseResult.violations.push(`STDERR: ${result.stderr.trim()}`);
          }
        }
        return baseResult;
    }
  }

  /**
   * Parse coverage results
  */
  private parseCoverageResult(
    baseResult: QualityGateResult,
    result: { stdout: string; stderr?: string; code?: number },
    threshold: Record<string, number | undefined>
  ): QualityGateResult {
    try {
      // Try to find coverage data in stdout
      const coverageMatch = result.stdout.match(/Lines\s*:\s*([\d.]+)%.*Functions\s*:\s*([\d.]+)%.*Branches\s*:\s*([\d.]+)%.*Statements\s*:\s*([\d.]+)%/s);
      
      if (coverageMatch) {
        const [, linesStr = '0', functionsStr = '0', branchesStr = '0', statementsStr = '0'] = coverageMatch as unknown as string[];
        const coverage = {
          lines: parseFloat(linesStr),
          functions: parseFloat(functionsStr),
          branches: parseFloat(branchesStr),
          statements: parseFloat(statementsStr),
        };

        baseResult.details = coverage;
        baseResult.score = Math.round((coverage.lines + coverage.functions + coverage.branches + coverage.statements) / 4);

        // Validate against thresholds
        const validation = this.policyLoader.validateGateResult(baseResult.gateName, baseResult, baseResult.environment);
        baseResult.passed = validation.passed;
        baseResult.violations = validation.violations;
      }
    } catch (error) {
      baseResult.violations.push(`Failed to parse coverage results: ${error}`);
    }

    return baseResult;
  }

  /**
   * Parse linting results
   */
  private parseLintingResult(
    baseResult: QualityGateResult,
    result: { stdout: string; stderr?: string; code?: number },
    threshold: { maxErrors?: number; maxWarnings?: number }
  ): QualityGateResult {
    try {
      // Count errors and warnings
      const errorMatches = result.stdout.match(/(\d+)\s+error/g) || [];
      const warningMatches = result.stdout.match(/(\d+)\s+warning/g) || [];
      
      const errors = errorMatches.reduce((sum, match) => sum + parseInt(match.match(/\d+/)?.[0] || '0'), 0);
      const warnings = warningMatches.reduce((sum, match) => sum + parseInt(match.match(/\d+/)?.[0] || '0'), 0);

      baseResult.details = { errors, warnings };
      
      // Check against thresholds
      if (threshold.maxErrors !== undefined && errors > threshold.maxErrors) {
        baseResult.violations.push(`Too many errors: ${errors} > ${threshold.maxErrors}`);
      }
      
      if (threshold.maxWarnings !== undefined && warnings > threshold.maxWarnings) {
        baseResult.violations.push(`Too many warnings: ${warnings} > ${threshold.maxWarnings}`);
      }

      baseResult.passed = baseResult.violations.length === 0 && result.code === 0;
    } catch (error) {
      baseResult.violations.push(`Failed to parse linting results: ${error}`);
    }

    return baseResult;
  }

  /**
   * Parse security results
   */
  private parseSecurityResult(
    baseResult: QualityGateResult,
    result: { stdout: string; stderr?: string; code?: number },
    threshold: { maxCritical?: number; maxHigh?: number; maxMedium?: number }
  ): QualityGateResult {
    try {
      // Parse npm audit output
      const criticalMatches = result.stdout.match(/(\d+)\s+critical/i);
      const highMatches = result.stdout.match(/(\d+)\s+high/i);
      const mediumMatches = result.stdout.match(/(\d+)\s+moderate/i);

    const critical = parseInt(criticalMatches?.[1] || '0', 10);
    const high = parseInt(highMatches?.[1] || '0', 10);
    const medium = parseInt(mediumMatches?.[1] || '0', 10);

      baseResult.details = { critical, high, medium };
      
      // Check against thresholds
      if (threshold.maxCritical !== undefined && critical > threshold.maxCritical) {
        baseResult.violations.push(`Too many critical vulnerabilities: ${critical} > ${threshold.maxCritical}`);
      }
      
      if (threshold.maxHigh !== undefined && high > threshold.maxHigh) {
        baseResult.violations.push(`Too many high vulnerabilities: ${high} > ${threshold.maxHigh}`);
      }
      
      if (threshold.maxMedium !== undefined && medium > threshold.maxMedium) {
        baseResult.violations.push(`Too many medium vulnerabilities: ${medium} > ${threshold.maxMedium}`);
      }

      baseResult.passed = baseResult.violations.length === 0;
    } catch (error) {
      baseResult.violations.push(`Failed to parse security results: ${error}`);
    }

    return baseResult;
  }

  /**
   * Parse performance results
   */
  private parsePerformanceResult(
    baseResult: QualityGateResult,
    _result: { stdout: string; stderr?: string; code?: number },
    _threshold: Record<string, number | undefined>
  ): QualityGateResult {
    // Placeholder for performance result parsing
    baseResult.details = { performanceTest: true };
    return baseResult;
  }

  /**
   * Parse accessibility results
   */
  private parseAccessibilityResult(
    baseResult: QualityGateResult,
    _result: { stdout: string; stderr?: string; code?: number },
    _threshold: Record<string, number | undefined>
  ): QualityGateResult {
    // Placeholder for accessibility result parsing
    baseResult.details = { accessibilityTest: true };
    return baseResult;
  }

  /**
   * Save quality report to file
   */
  private async saveReport(report: QualityReport, outputDir: string): Promise<void> {
    try {
      // Ensure output directory exists
      if (!fs.existsSync(outputDir)) {
        fs.mkdirSync(outputDir, { recursive: true });
      }

      const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
      const filename = `quality-report-${report.environment}-${timestamp}.json`;
      const filepath = path.join(outputDir, filename);

      const enriched = { ...report, meta: buildReportMeta() };
      fs.writeFileSync(filepath, JSON.stringify(enriched, null, 2));
      console.log(`📝 Quality report saved to: ${filepath}`);

      // Also save as latest
      const latestPath = path.join(outputDir, `quality-report-${report.environment}-latest.json`);
      fs.writeFileSync(latestPath, JSON.stringify(enriched, null, 2));

    } catch (error) {
      console.error('⚠️  Failed to save quality report:', error);
    }
  }

  /**
   * Generate empty report for when no gates are found
   */
  private generateEmptyReport(environment: string): QualityReport {
    return {
      timestamp: new Date().toISOString(),
      environment,
      overallScore: 100,
      totalGates: 0,
      passedGates: 0,
      failedGates: 0,
      results: [],
      summary: {
        byCategory: {},
        executionTime: 0,
        blockers: [],
      },
    };
  }

  /**
   * Print execution summary
   */
  private printSummary(report: QualityReport, verbose: boolean): void {
    console.log('\n' + '='.repeat(60));
    console.log('📊 QUALITY GATES SUMMARY');
    console.log('='.repeat(60));
    console.log(`Environment: ${report.environment}`);
    console.log(`Overall Score: ${report.overallScore}/100`);
    console.log(`Gates: ${report.passedGates}/${report.totalGates} passed`);
    console.log(`Execution Time: ${Math.round(report.summary.executionTime / 1000)}s`);

    if (report.summary.blockers.length > 0) {
      console.log(`\n🚫 BLOCKERS (${report.summary.blockers.length}):`);
      report.summary.blockers.forEach(blocker => {
        console.log(`   • ${blocker}`);
      });
    }

    if (verbose || report.failedGates > 0) {
      console.log('\n📋 DETAILED RESULTS:');
      report.results.forEach(result => {
        const icon = result.passed ? '✅' : '❌';
        const score = result.score !== undefined ? ` (${result.score})` : '';
        console.log(`   ${icon} ${result.gateName}${score}`);
        
        if (!result.passed && result.violations.length > 0) {
          result.violations.forEach(violation => {
            console.log(`      • ${violation}`);
          });
        }
      });
    }

    console.log('='.repeat(60));
    
    if (report.failedGates > 0) {
      console.log('❌ Some quality gates failed. Review the results above.');
    } else {
      console.log('✅ All quality gates passed!');
    }
  }
}

// CLI interface for quality gate runner
export async function runQualityGatesCLI(args: string[]): Promise<void> {
  const runner = new QualityGateRunner();
  
  // Parse command line arguments
  const options: QualityGateExecutionOptions = {
    environment: process.env['NODE_ENV'] || 'development',
    parallel: true,
    verbose: false,
    dryRun: false,
  };

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    switch (arg) {
      case '--env': {
        const val = args[i + 1];
        if (val !== undefined) {
          options.environment = val;
          i++;
        }
        break;
      }
      case '--gates':
        {
          const val = args[i + 1];
          if (val !== undefined) {
            options.gates = val.split(',');
            i++;
          }
        }
        break;
      case '--sequential':
        options.parallel = false;
        break;
      case '--verbose':
        options.verbose = true;
        break;
      case '--dry-run':
        options.dryRun = true;
        break;
      case '--timeout': {
        const val = args[i + 1];
        if (val !== undefined) {
          const n = parseInt(val, 10);
          if (!Number.isNaN(n)) options.timeout = n;
          i++;
        }
        break;
      }
      case '--output': {
        const val = args[i + 1];
        if (val !== undefined) {
          options.outputDir = val;
          i++;
        }
        break;
      }
    }
  }

  try {
    const report = await runner.executeGates(options);
    
    // Exit with error code if gates failed and blocking is enabled
    if (report.summary.blockers.length > 0) {
      const { safeExit } = await import('../utils/safe-exit.js');
      safeExit(1);
    }
  } catch (error) {
    console.error('❌ Quality gates execution failed:', error);
    const { safeExit } = await import('../utils/safe-exit.js');
    safeExit(1);
  }
}
