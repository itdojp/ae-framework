/**
 * Quality Gate Runner
 * Executes quality gates based on centralized policy configuration
 */

import { spawn, exec } from 'child_process';
import { promisify } from 'util';
import * as fs from 'fs';
import * as path from 'path';
import { QualityPolicyLoader, QualityGateResult, QualityReport, QualityGate } from './policy-loader.js';

// Mock telemetry for main branch compatibility
const mockTelemetry = {
  createTimer: (name: string, attributes?: any) => ({
    end: (additionalAttributes?: any) => Date.now(),
  }),
  recordQualityMetrics: (metrics: any) => {},
  recordCounter: (name: string, value: number, attributes?: any) => {},
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
      environment = process.env.NODE_ENV || 'development',
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
      const gateResult = await this.parseGateResult(gate, result, threshold, environment, executionTime);

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
      const process = spawn('sh', ['-c', command], {
        stdio: ['pipe', 'pipe', 'pipe'],
        timeout,
      });

      let stdout = '';
      let stderr = '';

      process.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      process.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      process.on('close', (code) => {
        resolve({ stdout, stderr, code: code || 0 });
      });

      process.on('error', (error) => {
        reject(error);
      });

      // Handle timeout
      setTimeout(() => {
        if (!process.killed) {
          process.kill('SIGTERM');
          reject(new Error(`Command timed out after ${timeout}ms`));
        }
      }, timeout);
    });
  }

  /**
   * Parse gate execution result
   */
  private async parseGateResult(
    gate: QualityGate,
    result: { stdout: string; stderr: string; code: number },
    threshold: any,
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
        return this.parseCoverageResult(baseResult, result, threshold);
      
      case 'code-quality':
        return this.parseLintingResult(baseResult, result, threshold);
      
      case 'security':
        return this.parseSecurityResult(baseResult, result, threshold);
      
      case 'performance':
        return this.parsePerformanceResult(baseResult, result, threshold);
      
      case 'frontend':
        return this.parseAccessibilityResult(baseResult, result, threshold);
      
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
  private parseCoverageResult(baseResult: QualityGateResult, result: any, threshold: any): QualityGateResult {
    try {
      // Try to find coverage data in stdout
      const coverageMatch = result.stdout.match(/Lines\s*:\s*([\d.]+)%.*Functions\s*:\s*([\d.]+)%.*Branches\s*:\s*([\d.]+)%.*Statements\s*:\s*([\d.]+)%/s);
      
      if (coverageMatch) {
        const [, lines, functions, branches, statements] = coverageMatch;
        const coverage = {
          lines: parseFloat(lines),
          functions: parseFloat(functions),
          branches: parseFloat(branches),
          statements: parseFloat(statements),
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
  private parseLintingResult(baseResult: QualityGateResult, result: any, threshold: any): QualityGateResult {
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
  private parseSecurityResult(baseResult: QualityGateResult, result: any, threshold: any): QualityGateResult {
    try {
      // Parse npm audit output
      const criticalMatches = result.stdout.match(/(\d+)\s+critical/i);
      const highMatches = result.stdout.match(/(\d+)\s+high/i);
      const mediumMatches = result.stdout.match(/(\d+)\s+moderate/i);

      const critical = criticalMatches ? parseInt(criticalMatches[1]) : 0;
      const high = highMatches ? parseInt(highMatches[1]) : 0;
      const medium = mediumMatches ? parseInt(mediumMatches[1]) : 0;

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
  private parsePerformanceResult(baseResult: QualityGateResult, result: any, threshold: any): QualityGateResult {
    // Placeholder for performance result parsing
    baseResult.details = { performanceTest: true };
    return baseResult;
  }

  /**
   * Parse accessibility results
   */
  private parseAccessibilityResult(baseResult: QualityGateResult, result: any, threshold: any): QualityGateResult {
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

      fs.writeFileSync(filepath, JSON.stringify(report, null, 2));
      console.log(`📝 Quality report saved to: ${filepath}`);

      // Also save as latest
      const latestPath = path.join(outputDir, `quality-report-${report.environment}-latest.json`);
      fs.writeFileSync(latestPath, JSON.stringify(report, null, 2));

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
    environment: process.env.NODE_ENV || 'development',
    parallel: true,
    verbose: false,
    dryRun: false,
  };

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    switch (arg) {
      case '--env':
        options.environment = args[++i];
        break;
      case '--gates':
        options.gates = args[++i].split(',');
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
      case '--timeout':
        options.timeout = parseInt(args[++i], 10);
        break;
      case '--output':
        options.outputDir = args[++i];
        break;
    }
  }

  try {
    const report = await runner.executeGates(options);
    
    // Exit with error code if gates failed and blocking is enabled
    if (report.summary.blockers.length > 0) {
      process.exit(1);
    }
  } catch (error) {
    console.error('❌ Quality gates execution failed:', error);
    process.exit(1);
  }
}