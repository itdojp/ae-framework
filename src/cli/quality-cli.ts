/**
 * Quality CLI commands for the AE-Framework
 * Provides commands to execute and manage quality gates
 */

import { Command } from 'commander';
import chalk from 'chalk';
import { qualityPolicy } from '../quality/policy-loader.js';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import { QualityGateRunner } from '../quality/quality-gate-runner.js';
import { AutoFixEngine } from '../cegis/auto-fix-engine.js';
import type { FailureArtifact as EngineFailureArtifact, FailureCategory as EngineFailureCategory } from '../cegis/types.js';
import { FailureArtifactSchema as EngineFailureArtifactSchema } from '../cegis/types.js';
import type { FailureArtifact as LegacyFailureArtifact, FailureArtifactCollection as LegacyFailureArtifactCollection } from '../cegis/failure-artifact-schema.js';
import { validateFailureArtifact, validateFailureArtifactCollection } from '../cegis/failure-artifact-schema.js';
import * as fs from 'fs';
import * as path from 'path';

const isErrnoException = (value: unknown): value is NodeJS.ErrnoException => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  if (!('code' in value)) {
    return false;
  }
  return typeof (value as { code?: unknown }).code === 'string';
};

const readFileIfExists = (filePath: string): string | null => {
  try {
    return fs.readFileSync(filePath, 'utf8');
  } catch (error) {
    if (isErrnoException(error) && error.code === 'ENOENT') {
      return null;
    }
    throw error;
  }
};

const readDirIfExists = (dirPath: string): string[] | null => {
  try {
    return fs.readdirSync(dirPath);
  } catch (error) {
    if (isErrnoException(error) && error.code === 'ENOENT') {
      return null;
    }
    throw error;
  }
};

const COMMON_FAILURE_PATHS = [
  '.ae/failures.json',
  'failure-artifacts.json',
  'failures.json',
  '.ae/auto-fix/failures.json',
];

const mapLegacyCategory = (category: LegacyFailureArtifact['category']): EngineFailureCategory => {
  switch (category) {
    case 'contract_violation':
      return 'contract_violation';
    case 'test_failure':
      return 'test_failure';
    case 'type_error':
      return 'type_error';
    case 'runtime_error':
      return 'runtime_error';
    case 'performance_regression':
      return 'performance_issue';
    case 'security_violation':
      return 'security_violation';
    case 'quality_gate_failure':
      return 'build_error';
    case 'drift_detection':
      return 'build_error';
    case 'specification_mismatch':
    default:
      return 'contract_violation';
  }
};

const normalizePhase = (phase?: string): 'intent' | 'formal' | 'test' | 'code' | 'verify' | 'operate' | undefined => {
  if (!phase) return undefined;
  const allowed = ['intent', 'formal', 'test', 'code', 'verify', 'operate'] as const;
  return allowed.includes(phase as (typeof allowed)[number]) ? (phase as (typeof allowed)[number]) : undefined;
};

const convertLegacyFailureArtifact = (legacy: LegacyFailureArtifact): EngineFailureArtifact => {
  const now = new Date().toISOString();
  const createdAt = legacy.createdAt ?? legacy.context.timestamp ?? now;
  const updatedAt = legacy.updatedAt ?? legacy.context.timestamp ?? createdAt;
  const metrics = legacy.evidence.metrics
    ? Object.fromEntries(Object.entries(legacy.evidence.metrics).filter(([, value]) => typeof value === 'number'))
    : {};

  const location = legacy.location?.file
    ? {
        filePath: legacy.location.file,
        startLine: legacy.location.line ?? 1,
        endLine: legacy.location.line ?? 1,
        startColumn: legacy.location.column ?? undefined,
        endColumn: legacy.location.column ?? undefined,
        functionName: legacy.location.function ?? undefined,
        className: legacy.location.module ?? undefined,
      }
    : undefined;

  return EngineFailureArtifactSchema.parse({
    id: legacy.id,
    title: legacy.title,
    description: legacy.description,
    severity: legacy.severity,
    category: mapLegacyCategory(legacy.category),
    location,
    context: {
      environment: legacy.context.environment ?? 'development',
      timestamp: legacy.context.timestamp ?? now,
      phase: normalizePhase(legacy.context.phase),
      command: legacy.context.component,
      gitCommit: legacy.context.commitHash,
      gitBranch: legacy.context.branch,
    },
    evidence: {
      stackTrace: legacy.evidence.stackTrace,
      errorMessage: legacy.description,
      logs: legacy.evidence.logs ?? [],
      metrics,
      dependencies: [],
      relatedFiles: [],
    },
    suggestedActions: [],
    relatedArtifacts: legacy.childFailureIds ?? [],
    metadata: {
      createdAt,
      updatedAt,
      version: legacy.schemaVersion ?? '1.0.0',
      tags: legacy.tags ?? [],
      source: legacy.context.component ?? 'failure-artifact-schema',
    },
  });
};

const normalizeFailureArtifact = (item: unknown): EngineFailureArtifact => {
  try {
    return EngineFailureArtifactSchema.parse(item);
  } catch {
    const legacy = validateFailureArtifact(item);
    return convertLegacyFailureArtifact(legacy);
  }
};

const loadFailureArtifacts = (inputPath?: string): EngineFailureArtifact[] => {
  let resolvedPath = inputPath;
  if (!resolvedPath) {
    for (const tryPath of COMMON_FAILURE_PATHS) {
      if (fs.existsSync(tryPath)) {
        resolvedPath = tryPath;
        console.log(chalk.gray(`📁 Found failure artifacts at: ${tryPath}`));
        break;
      }
    }
  }

  if (!resolvedPath) {
    throw new Error(
      'No input file specified and no failure artifacts found in common locations.\n' +
        'Use --fix-input to specify input file, or run "ae-fix demo" to generate test data.'
    );
  }

  if (!fs.existsSync(resolvedPath)) {
    throw new Error(`Input file not found: ${resolvedPath}`);
  }

  const data = JSON.parse(fs.readFileSync(resolvedPath, 'utf8')) as unknown;
  if (Array.isArray(data)) {
    return data.map((item) => normalizeFailureArtifact(item));
  }
  if (data && typeof data === 'object' && 'failures' in data) {
    const legacyCollection = validateFailureArtifactCollection(data as LegacyFailureArtifactCollection);
    return legacyCollection.failures.map((failure) => convertLegacyFailureArtifact(failure));
  }
  return [normalizeFailureArtifact(data)];
};

export function createQualityCommand(): Command {
  const quality = new Command('quality');
  quality.description('Quality gates and policy management');

  // Run quality gates
  quality
    .command('run')
    .description('Execute quality gates for current environment')
    .option('-e, --env <environment>', 'Target environment', process.env['NODE_ENV'] || 'development')
    .option('-g, --gates <gates>', 'Comma-separated list of specific gates to run')
    .option('--sequential', 'Run gates sequentially instead of in parallel')
    .option('--dry-run', 'Show what would be executed without running')
    .option('-v, --verbose', 'Verbose output with detailed results')
    .option('-t, --timeout <ms>', 'Timeout for each gate in milliseconds', '300000')
    .option('-o, --output <dir>', 'Output directory for reports', 'reports/quality-gates')
    .option('--no-history', 'Skip timestamped history report and write latest report only')
    .action(async (options) => {
      try {
        console.log(chalk.blue(`🔍 Running quality gates for ${options.env} environment`));
        
        const runner = new QualityGateRunner();
        const report = await runner.executeGates({
          environment: options.env,
          gates: options.gates ? options.gates.split(',').map((g: string) => g.trim()) : undefined,
          parallel: !options.sequential,
          dryRun: options.dryRun,
          verbose: options.verbose,
          timeout: parseInt(options.timeout),
          outputDir: options.output,
          noHistory: options.history === false,
        });

        // Exit with appropriate code
        if (report.summary.blockers.length > 0) {
          console.log(chalk.red(`\n❌ ${report.summary.blockers.length} blocking quality gate(s) failed`));
          safeExit(1);
        } else if (report.failedGates > 0) {
          console.log(chalk.yellow(`\n⚠️  ${report.failedGates} quality gate(s) failed (non-blocking)`));
        } else {
          console.log(chalk.green('\n✅ All quality gates passed!'));
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error running quality gates: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  quality
    .command('reconcile')
    .description('Run quality gates and auto-fix until pass or max rounds')
    .option('-e, --env <environment>', 'Target environment', process.env['NODE_ENV'] || 'development')
    .option('-g, --gates <gates>', 'Comma-separated list of specific gates to run')
    .option('--sequential', 'Run gates sequentially instead of in parallel')
    .option('--dry-run', 'Show what would be executed without running')
    .option('-v, --verbose', 'Verbose output with detailed results')
    .option('-t, --timeout <ms>', 'Timeout for each gate in milliseconds', '300000')
    .option('-o, --output <dir>', 'Output directory for reports', 'reports/quality-gates')
    .option('--no-history', 'Skip timestamped history report and write latest report only')
    .option('--max-rounds <number>', 'Maximum reconciliation rounds', '3')
    .option('--fix-input <path>', 'Failure artifacts JSON file for auto-fix')
    .option('--fix-output <dir>', 'Output directory for auto-fix', '.ae/auto-fix')
    .option('--fix-iterations <number>', 'Auto-fix max iterations', '10')
    .option('--fix-confidence <threshold>', 'Auto-fix confidence threshold', '0.7')
    .action(async (options) => {
      try {
        const maxRounds = Math.max(1, parseInt(options.maxRounds, 10) || 1);
        const runner = new QualityGateRunner();
        let lastReport: Awaited<ReturnType<QualityGateRunner['executeGates']>> | null = null;

        let passed = false;
        for (let round = 1; round <= maxRounds; round += 1) {
          console.log(chalk.blue(`🔁 Reconciliation round ${round}/${maxRounds}`));
          console.log(chalk.blue(`🔍 Running quality gates for ${options.env} environment`));

          const report = await runner.executeGates({
            environment: options.env,
            gates: options.gates ? options.gates.split(',').map((g: string) => g.trim()) : undefined,
            parallel: !options.sequential,
            dryRun: options.dryRun,
            verbose: options.verbose,
            timeout: parseInt(options.timeout, 10) || 300000,
            outputDir: options.output,
            noHistory: options.history === false,
          });

          lastReport = report;

          if (report.summary.blockers.length > 0) {
            console.log(chalk.red(`\n❌ ${report.summary.blockers.length} blocking quality gate(s) failed`));
          } else if (report.failedGates > 0) {
            console.log(chalk.yellow(`\n⚠️  ${report.failedGates} quality gate(s) failed (non-blocking)`));
          } else {
            console.log(chalk.green('\n✅ All quality gates passed!'));
            passed = true;
            break;
          }

          if (options.dryRun) {
            console.log(chalk.yellow('ℹ️  Dry-run mode enabled; skipping auto-fix.'));
            break;
          }

          if (report.summary.blockers.length === 0) {
            console.log(chalk.yellow('ℹ️  No blocking gates failed; stopping reconciliation.'));
            break;
          }

          if (round >= maxRounds) {
            console.log(chalk.yellow('ℹ️  Max rounds reached; stopping reconciliation.'));
            break;
          }

          let failures: EngineFailureArtifact[];
          try {
            failures = loadFailureArtifacts(options.fixInput);
          } catch (error) {
            console.error(chalk.red('\n❌ Unable to load failure artifacts for auto-fix.'));
            console.error(chalk.yellow('ℹ️  Generate failure artifacts (for example, `ae-fix demo`).'));
            console.error(chalk.yellow(`   Details: ${toMessage(error)}`));
            console.log(chalk.yellow('ℹ️  Stopping reconciliation. Quality gates remain failed.'));
            break;
          }

          const engine = new AutoFixEngine();
          const fixResult = await engine.executeFixes(failures, {
            outputDir: options.fixOutput,
            maxIterations: parseInt(options.fixIterations, 10) || 10,
            confidenceThreshold: parseFloat(options.fixConfidence) || 0.7,
          });

          const appliedFixCount = fixResult.appliedFixes?.length ?? 0;
          if (appliedFixCount === 0) {
            console.log(chalk.yellow('⚠️  Auto-fix did not apply any changes. Stopping reconciliation.'));
            break;
          }
          console.log(chalk.green(`✅ Auto-fix applied ${appliedFixCount} change(s).`));
        }

        if (passed) {
          return;
        }

        if (lastReport && lastReport.summary.blockers.length > 0) {
          safeExit(1);
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error running reconciliation: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // List available quality gates
  quality
    .command('list')
    .description('List available quality gates and their configuration')
    .option('-e, --env <environment>', 'Show configuration for specific environment', 'development')
    .option('--all', 'Show all gates regardless of environment')
    .option('--format <format>', 'Output format (table, json, summary)', 'table')
    .action(async (options) => {
      try {
        const gates = options.all 
          ? Object.values(qualityPolicy.getAllGates())
          : qualityPolicy.getGatesForEnvironment(options.env);

        if (options.format === 'json') {
          console.log(JSON.stringify(gates, null, 2));
          return;
        }

        console.log(chalk.blue(`📋 Quality Gates for ${options.env} environment\n`));
        
        if (gates.length === 0) {
          console.log(chalk.yellow('No quality gates found for this environment'));
          return;
        }

        if (options.format === 'summary') {
          gates.forEach(gate => {
            // Find the gate key in policy
            const allGates = qualityPolicy.getAllGates();
            const gateKey = Object?.keys(allGates)?.find(key => allGates[key]?.name === gate?.name) || gate?.name;
            
            const shouldBlock = qualityPolicy.shouldBlock(gateKey, options.env);
            
            console.log(chalk.cyan(`${gate.name}:`));
            console.log(`  Description: ${gate.description}`);
            console.log(`  Category: ${gate.category}`);
            console.log(`  Enabled: ${gate.enabled ? '✅' : '❌'}`);
            console.log(`  Blocking: ${shouldBlock ? '🚫' : '⚠️ '}`);
            console.log(`  Command: ${gate.commands.test}`);
            console.log();
          });
        } else {
          // Table format
          console.log('Name'.padEnd(20) + 'Category'.padEnd(15) + 'Enabled'.padEnd(10) + 'Blocking'.padEnd(10) + 'Description');
          console.log('-'.repeat(80));
          
          gates.forEach(gate => {
            // Find the gate key in policy
            const allGates = qualityPolicy.getAllGates();
            const gateKey = Object?.keys(allGates)?.find(key => allGates[key]?.name === gate?.name) || gate?.name;
            
            const shouldBlock = qualityPolicy.shouldBlock(gateKey, options.env);
            const enabled = gate.enabled ? '✅' : '❌';
            const blocking = shouldBlock ? '🚫' : '⚠️ ';
            
            console.log(
              gate.name.padEnd(20) +
              gate.category.padEnd(15) +
              enabled.padEnd(10) +
              blocking.padEnd(10) +
              gate.description.substring(0, 40) + (gate.description.length > 40 ? '...' : '')
            );
          });
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error listing quality gates: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Show policy configuration
  quality
    .command('policy')
    .description('Show quality policy configuration')
    .option('-e, --env <environment>', 'Show specific environment configuration')
    .option('-g, --gate <gate>', 'Show specific gate configuration')
    .option('--format <format>', 'Output format (json, yaml, summary)', 'summary')
    .action(async (options) => {
      try {
        if (options.gate) {
          // Show specific gate
          const gates = qualityPolicy.getAllGates();
          const gate = gates[options.gate];
          
          if (!gate) {
            console.error(chalk.red(`❌ Quality gate '${options.gate}' not found`));
            safeExit(1);
            return;
          }

          console.log(chalk.blue(`📋 Quality Gate: ${gate.name}\n`));
          console.log(JSON.stringify(gate, null, 2));
          
        } else if (options.env) {
          // Show environment configuration
          const envConfig = qualityPolicy.getEnvironmentConfig(options.env);
          const gates = qualityPolicy.getGatesForEnvironment(options.env);
          
          console.log(chalk.blue(`🌍 Environment: ${options.env}\n`));
          console.log(`Description: ${envConfig.description}`);
          console.log(`Enforcement Level: ${envConfig.enforcementLevel}`);
          console.log(`Quality Gates: ${gates.length}`);
          console.log(`Gate Names: ${gates.map(g => g.name).join(', ')}`);
          
        } else {
          // Show full policy
          const allowed: Array<'json' | 'yaml' | 'summary'> = ['json', 'yaml', 'summary'];
          const fmt = allowed.includes(options.format) ? options.format as 'json' | 'yaml' | 'summary' : 'json';
          const policy = qualityPolicy.exportPolicy(fmt);
          console.log(policy);
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error showing policy: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Validate policy configuration
  quality
    .command('validate')
    .description('Validate quality policy configuration')
    .option('--fix', 'Attempt to fix validation issues')
    .action(async (options) => {
      try {
        console.log(chalk.blue('🔍 Validating quality policy configuration...'));
        
        // Load and validate policy
        const policy = qualityPolicy.loadPolicy();
        
        const issues: string[] = [];
        
        // Check for missing commands
        Object.entries(policy.qualityGates).forEach(([name, gate]) => {
          if (!gate.commands.test) {
            issues.push(`Gate '${name}' missing test command`);
          }
        });

        // Check for missing thresholds
        Object.entries(policy.qualityGates).forEach(([name, gate]) => {
          Object.keys(policy.environments).forEach(env => {
            if (!gate.thresholds[env]) {
              issues.push(`Gate '${name}' missing threshold for environment '${env}'`);
            }
          });
        });

        // Check composite gate references
        Object.entries(policy.compositeGates).forEach(([name, composite]) => {
          composite.gates.forEach(gateName => {
            if (!policy.qualityGates[gateName]) {
              issues.push(`Composite gate '${name}' references unknown gate '${gateName}'`);
            }
          });
        });

        if (issues.length === 0) {
          console.log(chalk.green('✅ Quality policy configuration is valid'));
        } else {
          console.log(chalk.yellow(`⚠️  Found ${issues.length} validation issues:`));
          issues.forEach(issue => {
            console.log(chalk.yellow(`   • ${issue}`));
          });
          
          if (options.fix) {
            console.log(chalk.blue('\n🔧 Attempting to fix issues...'));
            // Implement basic fixes here
            console.log(chalk.yellow('⚠️  Automatic fixes not yet implemented'));
          }
        }
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error validating policy: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Show quality reports
  quality
    .command('report')
    .description('Show quality gate reports')
    .option('-e, --env <environment>', 'Environment to show reports for', 'development')
    .option('-l, --latest', 'Show only the latest report')
    .option('-d, --days <days>', 'Show reports from last N days', '7')
    .option('--format <format>', 'Output format (json, summary)', 'summary')
    .action(async (options) => {
      try {
        const reportsDir = path.join(process.cwd(), 'reports', 'quality-gates');
        const reportFiles = readDirIfExists(reportsDir);
        if (!reportFiles) {
          console.log(chalk.yellow('⚠️  No quality reports found'));
          return;
        }

        if (options.latest) {
          // Show latest report
          const latestFile = path.join(reportsDir, `quality-report-${options.env}-latest.json`);

          const latestRaw = readFileIfExists(latestFile);
          if (!latestRaw) {
            console.log(chalk.yellow(`⚠️  No latest report found for environment '${options.env}'`));
            return;
          }
          const report = JSON.parse(latestRaw);
          
          if (options.format === 'json') {
            console.log(JSON.stringify(report, null, 2));
          } else {
            console.log(chalk.blue(`📊 Latest Quality Report - ${options.env}\n`));
            console.log(`Timestamp: ${report.timestamp}`);
            console.log(`Overall Score: ${report.overallScore}/100`);
            console.log(`Gates Passed: ${report.passedGates}/${report.totalGates}`);
            console.log(`Execution Time: ${Math.round(report.summary.executionTime / 1000)}s`);
            
            if (report.summary.blockers.length > 0) {
              console.log(chalk.red(`\nBlockers: ${report.summary.blockers.join(', ')}`));
            }
          }
        } else {
          // List available reports
          const files = reportFiles
            .filter(f => f.startsWith(`quality-report-${options.env}-`) && f.endsWith('.json') && !f.includes('latest'))
            .sort()
            .reverse();

          const dayFilter = parseInt(options.days);
          const cutoffDate = new Date(Date.now() - dayFilter * 24 * 60 * 60 * 1000);

          console.log(chalk.blue(`📋 Quality Reports for ${options.env} (last ${options.days} days)\n`));
          
          files.forEach(file => {
            const filePath = path.join(reportsDir, file);
            const stats = fs.statSync(filePath);
            
            if (stats.mtime >= cutoffDate) {
              const report = JSON.parse(fs.readFileSync(filePath, 'utf8'));
              const timestamp = new Date(report.timestamp).toLocaleString();
              const score = report.overallScore;
              const status = report.failedGates === 0 ? '✅' : (report.summary.blockers.length > 0 ? '❌' : '⚠️ ');
              
              console.log(`${status} ${timestamp} - Score: ${score}/100 (${report.passedGates}/${report.totalGates} gates)`);
            }
          });
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error showing reports: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Initialize quality configuration
  quality
    .command('init')
    .description('Initialize quality policy configuration')
    .option('--force', 'Overwrite existing configuration')
    .action(async (options) => {
      try {
        const configPath = path.join(process.cwd(), 'config', 'quality-policy.json');
        const existingConfig = readFileIfExists(configPath);
        if (existingConfig !== null && !options.force) {
          console.log(chalk.yellow('⚠️  Quality policy already exists. Use --force to overwrite.'));
          return;
        }

        // Ensure config directory exists
        const configDir = path.dirname(configPath);
        if (readDirIfExists(configDir) === null) {
          fs.mkdirSync(configDir, { recursive: true });
        }

        console.log(chalk.blue('🔧 Initializing quality policy configuration...'));
        console.log(`📁 Creating: ${configPath}`);
        
        // The config is already created in the file, just confirm it exists
        if (readFileIfExists(configPath) !== null) {
          console.log(chalk.green('✅ Quality policy configuration initialized successfully'));
          console.log(chalk.cyan('\nNext steps:'));
          console.log('  • Review and customize the policy in config/quality-policy.json');
          console.log('  • Run "npm run quality:run" to execute quality gates');
          console.log('  • Add quality gates to your CI/CD pipeline');
        } else {
          console.log(chalk.red('❌ Failed to create quality policy configuration'));
          safeExit(1);
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error initializing quality configuration: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  return quality;
}

export default createQualityCommand;
