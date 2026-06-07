/**
 * Quality Gate Runner
 * Executes quality gates based on centralized policy configuration
 */

import { spawn } from 'node:child_process';
import * as fs from 'fs';
import * as path from 'path';
import { QualityPolicyLoader, type QualityGateResult, type QualityReport, type QualityGate } from './policy-loader.js';
import { buildReportMeta } from '../utils/report-meta.js';
import {
  type ApprovedQualityGateCommand,
  createQualityPathContext,
  getApprovedQualityGateCommand,
  getDefaultQualityReportDir,
  isQualityAgentContext,
  isQualityCiContext,
  QUALITY_GATE_EXECUTION_APPROVAL_SCOPE,
  resolveQualityReportOutputDir,
} from './quality-command-policy.js';
import {
  createHighImpactChildEnv,
  evaluateHighImpactActionPolicy,
} from '../utils/high-impact-action-policy.js';

type CoverageThreshold = { lines?: number; functions?: number; branches?: number; statements?: number };
type LintThreshold = { maxErrors?: number; maxWarnings?: number };
type SecurityThreshold = { maxCritical?: number; maxHigh?: number; maxMedium?: number };
type PerfThreshold = Record<string, number | undefined>;
type A11yThreshold = Record<string, number | undefined>;
type QualityGateExecutionRecord = {
  gate: QualityGate;
  key: string;
  command: ApprovedQualityGateCommand;
};

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

export interface QualityGateExecutionOptions {
  environment?: string;
  gates?: string[];
  parallel?: boolean;
  timeout?: number;
  dryRun?: boolean;
  apply?: boolean;
  approvalScope?: string;
  verbose?: boolean;
  outputDir?: string;
  noHistory?: boolean;
  printSummary?: boolean;
  silent?: boolean;
}

export interface QualityGateRunnerOptions {
  spawnProcess?: typeof spawn;
}

export class QualityGateRunner {
  private policyLoader: QualityPolicyLoader;
  private spawnProcess: typeof spawn;
  private results: QualityGateResult[] = [];
  private silent = false;

  constructor(policyLoader?: QualityPolicyLoader, options: QualityGateRunnerOptions = {}) {
    this.policyLoader = policyLoader || new QualityPolicyLoader();
    this.spawnProcess = options.spawnProcess ?? spawn;
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
      apply = false,
      approvalScope,
      verbose = false,
      noHistory = false,
      printSummary = true,
      silent = false,
    } = options;
    this.silent = silent;
    const pathContext = createQualityPathContext();
    const outputDir = options.outputDir ?? getDefaultQualityReportDir(pathContext);
    const resolvedOutputDir = resolveQualityReportOutputDir(outputDir, pathContext);
    const agentContext = isQualityAgentContext();
    const ciContext = isQualityCiContext();
    const protectedContext = agentContext;
    // The runner preserves trusted local/CI compatibility; the CLI reconcile path
    // opts CI into approval enforcement when needed via protectCi.
    const requestedApply = apply || !protectedContext;
    const executionDecision = evaluateHighImpactActionPolicy({
      actionKind: 'package-manager',
      actionName: 'quality-gate-runner',
      apply: requestedApply,
      dryRun,
      approvalScope,
      requiredApprovalScope: QUALITY_GATE_EXECUTION_APPROVAL_SCOPE,
      agentContext,
      ciContext,
      blockAmbientSecrets: false,
      enforceApproval: protectedContext,
    });
    if (executionDecision.approvalRequired || executionDecision.blocked) {
      throw new Error(
        `Quality gate execution requires approval scope '${QUALITY_GATE_EXECUTION_APPROVAL_SCOPE}' when --apply is used in an agent context`
      );
    }
    const effectiveDryRun = executionDecision.dryRun;

    const timer = mockTelemetry.createTimer('quality_gates.execution.total', {
      [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'quality-gates',
      environment,
    });

    try {
      this.log(`🔍 Executing quality gates for environment: ${environment}`);
      
      // Get gates to execute
      const allGateMap = this.policyLoader.getAllGates();
      const composites: Record<string, string[]> = {};
      let gateRecords: Array<{ gate: QualityGate; key: string }> = [];
      if (requestedGates) {
        const gateKeys = new Set<string>();
        for (const name of requestedGates) {
          const composite = this.policyLoader.getCompositeGate(name);
          if (composite) {
            const compositeKeys: string[] = [];
            composite.gates.forEach(gateName => {
              const key = this.policyLoader.resolveGateKey(gateName);
              const gate = allGateMap[key];
              if (!gate) {
                throw new Error(`Quality gate '${gateName}' not found`);
              }
              if (gate.enabled) {
                gateKeys.add(key);
                compositeKeys.push(key);
              }
            });
            composites[name] = compositeKeys;
            continue;
          }
          const key = this.policyLoader.resolveGateKey(name);
          const gate = allGateMap[key];
          if (!gate) {
            throw new Error(`Quality gate '${name}' not found`);
          }
          if (gate.enabled) {
            gateKeys.add(key);
          }
        }
        gateRecords = Array.from(gateKeys)
          .map(key => {
            const gate = allGateMap[key];
            if (!gate) {
              return null;
            }
            return { gate, key };
          })
          .filter((record): record is { gate: QualityGate; key: string } => record !== null);
      } else {
        const compositeForEnv = this.policyLoader.getCompositeGateForEnvironment(environment);
        if (compositeForEnv) {
          const compositeKeys = compositeForEnv.gate.gates
            .map(gateName => this.policyLoader.resolveGateKey(gateName))
            .filter(key => allGateMap[key]?.enabled);
          composites[compositeForEnv.key] = compositeKeys;
        }
        gateRecords = this.policyLoader.getGatesForEnvironment(environment).map(gate => ({
          gate,
          key: this.policyLoader.resolveGateKey(gate.name),
        }));
      }

      if (gateRecords.length === 0) {
        this.log('⚠️  No quality gates found for execution');
        return this.generateEmptyReport(environment);
      }
      const executionRecords: QualityGateExecutionRecord[] = gateRecords.map(({ gate, key }) => ({
        gate,
        key,
        command: getApprovedQualityGateCommand(key, gate),
      }));

      this.log(`📋 Found ${executionRecords.length} quality gates to execute`);
      if (verbose) {
        executionRecords.forEach(({ gate, key, command }) => {
          this.log(`   • ${gate.name} (${gate.category}) [${key}]`);
          this.log(`     Command: ${command.displayCommand}`);
        });
      }

      // Execute gates
      this.results = [];
      if (parallel) {
        this.log('🚀 Executing gates in parallel...');
        const promises = executionRecords.map(({ gate, key, command }) =>
          this.executeGate(gate, key, command, environment, { timeout, dryRun: effectiveDryRun, verbose, silent })
        );
        this.results = await Promise.all(promises);
      } else {
        this.log('⏭️  Executing gates sequentially...');
        for (const { gate, key, command } of executionRecords) {
          const result = await this.executeGate(gate, key, command, environment, { timeout, dryRun: effectiveDryRun, verbose, silent });
          this.results.push(result);
        }
      }

      // Generate report
      const report = this.policyLoader.generateReport(this.results, environment);
      if (Object.keys(composites).length > 0) {
        report.composites = {};
        Object.entries(composites).forEach(([name, gates]) => {
          const resolvedGates = gates;
          const failed = resolvedGates.filter(key => {
            const result = this.results.find(item => item.gateKey === key);
            return !result || !result.passed;
          });
          report.composites![name] = {
            gates: resolvedGates,
            passed: failed.length === 0,
            failedGates: failed,
          };
        });
      }
      
      // Save report
      if (!effectiveDryRun) {
        await this.saveReport(report, resolvedOutputDir.workspaceRelativePath, { noHistory });
      }

      // Record metrics
      mockTelemetry.recordQualityMetrics({
        score: report.overallScore,
        coverage: (report.passedGates / report.totalGates) * 100,
        phase: 'quality-gates',
        component: 'runner',
      });

      timer.end({
        total_gates: report.totalGates,
        passed_gates: report.passedGates,
        failed_gates: report.failedGates,
        overall_score: report.overallScore,
      });

      // Print summary
      if (printSummary) {
        this.printSummary(report, verbose);
      }

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
    gateKey: string,
    approvedCommand: ApprovedQualityGateCommand,
    environment: string,
    options: { timeout: number; dryRun: boolean; verbose: boolean; silent: boolean }
  ): Promise<QualityGateResult> {
    const { timeout, dryRun, verbose, silent } = options;
    
    const gateTimer = mockTelemetry.createTimer('quality_gates.gate.execution', {
      [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'quality-gate',
      gate_name: gate.name,
      gate_key: gateKey,
      gate_category: gate.category,
      environment,
    });

    try {
      if (verbose) {
        this.log(`\n🔍 Executing: ${gate.name}`);
        this.log(`   Description: ${gate.description}`);
      }

      const threshold = this.policyLoader.getThreshold(gateKey, environment);
      if (verbose) {
        this.log(`   Command: ${approvedCommand.displayCommand}`);
      }
      
      if (dryRun) {
        this.log(`   🔄 DRY RUN: Would execute '${approvedCommand.displayCommand}'`);
        return {
          gateKey,
          gateName: gate.name,
          passed: true,
          score: 100,
          violations: [],
          executionTime: 0,
          environment,
          threshold,
          details: {
            dryRun: true,
            command: approvedCommand.displayCommand,
          },
        };
      }

      // Execute the gate command
      const startTime = Date.now();
      const result = await this.executeCommand(approvedCommand, timeout);
      const executionTime = Date.now() - startTime;

      // Parse result based on gate type
      const gateResult = await this.parseGateResult(
        gate,
        gateKey,
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
        this.log(`   ${gateResult.passed ? '✅' : '❌'} Result: ${gateResult.passed ? 'PASSED' : 'FAILED'}`);
        if (gateResult.score !== undefined) {
          this.log(`   📊 Score: ${gateResult.score}`);
        }
        if (gateResult.violations.length > 0) {
          this.log(`   ⚠️  Violations: ${gateResult.violations.length}`);
        }
      }

      return gateResult;

    } catch (error) {
      const executionTime = gateTimer.end({ result: 'error' });
      
      console.error(`❌ Error executing gate '${gate.name}':`, error);
      
      return {
        gateKey,
        gateName: gate.name,
        passed: false,
        violations: [`Execution error: ${error}`],
        executionTime,
        environment,
        threshold: this.policyLoader.getThreshold(gateKey, environment),
        details: { error: String(error) },
      };
    }
  }

  /**
   * Execute an allowlisted command with timeout.
   */
  private async executeCommand(
    command: ApprovedQualityGateCommand,
    timeout: number
  ): Promise<{ stdout: string; stderr: string; code: number }> {
    return new Promise((resolve, reject) => {
      const child = this.spawnProcess(command.executable, [...command.args], {
        stdio: ['pipe', 'pipe', 'pipe'],
        timeout,
        env: createHighImpactChildEnv(),
        shell: false,
      });

      let stdout = '';
      let stderr = '';
      let finished = false;

      child.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('close', (code) => {
        if (!finished) {
          finished = true;
          clearTimeout(timeoutHandle);
          resolve({ stdout, stderr, code: command.allowNonZeroExit ? 0 : (code || 0) });
        }
      });

      child.on('error', (error) => {
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
          child.kill('SIGTERM');
          reject(new Error(`Command timed out after ${timeout}ms`));
        }
      }, timeout);
    });
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
    gateKey: string,
    result: { stdout: string; stderr: string; code: number },
    threshold: Record<string, number | undefined>,
    environment: string,
    executionTime: number
  ): Promise<QualityGateResult> {
    const baseResult: QualityGateResult = {
      gateKey,
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
        const validation = this.policyLoader.validateGateResult(baseResult.gateKey, baseResult, baseResult.environment);
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
      const combinedOutput = `${result.stdout}\n${result.stderr ?? ''}`;
      // Count errors and warnings
      const errorMatches = combinedOutput.match(/(\d+)\s+error/g) || [];
      const warningMatches = combinedOutput.match(/(\d+)\s+warning/g) || [];
      
      const errors = errorMatches.reduce((sum, match) => sum + parseInt(match.match(/\d+/)?.[0] || '0'), 0);
      const warnings = warningMatches.reduce((sum, match) => sum + parseInt(match.match(/\d+/)?.[0] || '0'), 0);

      baseResult.details = { errors, warnings };

      const exitCode = result.code ?? 0;
      const hasCounts = errorMatches.length > 0 || warningMatches.length > 0;
      if (exitCode !== 0 && !hasCounts) {
        baseResult.violations.push(`Linting command failed with exit code ${exitCode}`);
      }
      
      // Check against thresholds
      if (threshold.maxErrors !== undefined && errors > threshold.maxErrors) {
        baseResult.violations.push(`Too many errors: ${errors} > ${threshold.maxErrors}`);
      }
      
      if (threshold.maxWarnings !== undefined && warnings > threshold.maxWarnings) {
        baseResult.violations.push(`Too many warnings: ${warnings} > ${threshold.maxWarnings}`);
      }

      baseResult.passed = baseResult.violations.length === 0;
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
      const combinedOutput = `${result.stdout}\n${result.stderr ?? ''}`.trim();
      const parseJsonPayload = (payload: string): Record<string, unknown> | null => {
        const trimmed = payload.trim();
        if (trimmed.length === 0) return null;

        try {
          return JSON.parse(trimmed) as Record<string, unknown>;
        } catch {
          // Fall through to best-effort extraction from mixed stdout/stderr logs.
        }

        const start = trimmed.indexOf('{');
        const end = trimmed.lastIndexOf('}');
        if (start >= 0 && end > start) {
          const candidate = trimmed.slice(start, end + 1);
          try {
            return JSON.parse(candidate) as Record<string, unknown>;
          } catch {
            return null;
          }
        }

        return null;
      };

      let critical = 0;
      let high = 0;
      let medium = 0;
      let hasCounts = false;
      let transientAuditError: { code: string; message: string } | null = null;

      const jsonPayloads = [result.stdout, result.stderr ?? '']
        .map((segment) => segment.trim())
        .filter((segment) => segment.length > 0);
      for (const payload of jsonPayloads) {
        const parsed = parseJsonPayload(payload) as {
          metadata?: { vulnerabilities?: { critical?: number; high?: number; moderate?: number } };
          error?: { code?: string; message?: string };
        } | null;
        if (!parsed) {
          continue;
        }

        const vulnerabilities = parsed.metadata?.vulnerabilities;
        if (vulnerabilities) {
          critical = Number(vulnerabilities.critical ?? 0);
          high = Number(vulnerabilities.high ?? 0);
          medium = Number(vulnerabilities.moderate ?? 0);
          hasCounts = true;
          break;
        }

        const errorCode = parsed.error?.code;
        const errorMessage = parsed.error?.message;
        if (
          errorCode === 'ERR_PNPM_AUDIT_BAD_RESPONSE' &&
          typeof errorMessage === 'string' &&
          /responded with (429|5\d\d)/i.test(errorMessage)
        ) {
          transientAuditError = { code: errorCode, message: errorMessage };
        }
      }

      if (!hasCounts) {
        const criticalMatches = combinedOutput.match(/(\d+)\s+critical/i);
        const highMatches = combinedOutput.match(/(\d+)\s+high/i);
        const mediumMatches = combinedOutput.match(/(\d+)\s+moderate/i);

        critical = parseInt(criticalMatches?.[1] || '0', 10);
        high = parseInt(highMatches?.[1] || '0', 10);
        medium = parseInt(mediumMatches?.[1] || '0', 10);
        hasCounts = Boolean(criticalMatches || highMatches || mediumMatches);
      }

      baseResult.details = {
        critical,
        high,
        medium,
        ...(transientAuditError
          ? {
              auditTransientErrorCode: transientAuditError.code,
              auditTransientErrorMessage: transientAuditError.message,
            }
          : {}),
      };

      const exitCode = result.code ?? 0;
      if (exitCode !== 0 && !hasCounts) {
        if (!transientAuditError) {
          baseResult.violations.push(`Security scan failed with exit code ${exitCode}`);
        }
      }
      
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
  private async saveReport(
    report: QualityReport,
    outputDir: string,
    options: { noHistory?: boolean } = {}
  ): Promise<void> {
    try {
      const pathContext = createQualityPathContext();
      const safeOutputDir = resolveQualityReportOutputDir(outputDir, pathContext).resolvedPath;
      // Ensure output directory exists
      if (!fs.existsSync(safeOutputDir)) {
        fs.mkdirSync(safeOutputDir, { recursive: true });
      }

      if (!options.noHistory) {
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
        const filename = `quality-report-${report.environment}-${timestamp}.json`;
        const filepath = path.join(safeOutputDir, filename);

        fs.writeFileSync(filepath, JSON.stringify(report, null, 2));
        this.log(`📝 Quality report saved to: ${filepath}`);
      }

      // Also save as latest
      const latestPath = path.join(safeOutputDir, `quality-report-${report.environment}-latest.json`);
      fs.writeFileSync(latestPath, JSON.stringify(report, null, 2));
      this.log(`📝 Quality report latest updated: ${latestPath}`);

    } catch (error) {
      console.error('⚠️  Failed to save quality report:', error);
    }
  }

  /**
   * Generate empty report for when no gates are found
   */
  private generateEmptyReport(environment: string): QualityReport {
    const timestamp = new Date().toISOString();
    return {
      timestamp,
      environment,
      meta: buildReportMeta({ createdAt: timestamp }),
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
    this.log('\n' + '='.repeat(60));
    this.log('📊 QUALITY GATES SUMMARY');
    this.log('='.repeat(60));
    this.log(`Environment: ${report.environment}`);
    this.log(`Overall Score: ${report.overallScore}/100`);
    this.log(`Gates: ${report.passedGates}/${report.totalGates} passed`);
    this.log(`Execution Time: ${Math.round(report.summary.executionTime / 1000)}s`);

    if (report.summary.blockers.length > 0) {
      this.log(`\n🚫 BLOCKERS (${report.summary.blockers.length}):`);
      report.summary.blockers.forEach(blocker => {
        this.log(`   • ${blocker}`);
      });
    }

    if (report.composites && Object.keys(report.composites).length > 0) {
      this.log('\n🧩 COMPOSITES:');
      Object.entries(report.composites).forEach(([name, composite]) => {
        const icon = composite.passed ? '✅' : '❌';
        this.log(`   ${icon} ${name} (${composite.gates.join(', ')})`);
        if (!composite.passed && composite.failedGates.length > 0) {
          this.log(`      Failed: ${composite.failedGates.join(', ')}`);
        }
      });
    }

    if (verbose || report.failedGates > 0) {
      this.log('\n📋 DETAILED RESULTS:');
      report.results.forEach(result => {
        const icon = result.passed ? '✅' : '❌';
        const score = result.score !== undefined ? ` (${result.score})` : '';
        this.log(`   ${icon} ${result.gateName}${score}`);
        
        if (!result.passed && result.violations.length > 0) {
          result.violations.forEach(violation => {
            this.log(`      • ${violation}`);
          });
        }
      });
    }

    this.log('='.repeat(60));
    
    if (report.failedGates > 0) {
      this.log('❌ Some quality gates failed. Review the results above.');
    } else {
      this.log('✅ All quality gates passed!');
    }
  }

  private log(message: string): void {
    if (!this.silent) {
      console.log(message);
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
      case '--apply':
        options.apply = true;
        break;
      case '--approval-scope': {
        const val = args[i + 1];
        if (val !== undefined) {
          options.approvalScope = val;
          i++;
        }
        break;
      }
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
      case '--no-history':
        options.noHistory = true;
        break;
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
