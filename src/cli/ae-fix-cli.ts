#!/usr/bin/env node
/**
 * AE-Framework Auto-Fix CLI
 * 
 * Command-line interface for CEGIS-based automated repair
 * Implements `ae fix` command for specification/code repair
 */

import { Command } from 'commander';
import * as fs from 'fs';
import * as path from 'path';
import chalk from 'chalk';
import type { FailureArtifact, FailureArtifactCollection } from '../cegis/failure-artifact-schema.js';
import { validateFailureArtifact, validateFailureArtifactCollection, FailureArtifactFactory } from '../cegis/failure-artifact-schema.js';
import { AutoFixEngine } from '../cegis/auto-fix-engine.js';
import type { AutoFixOptions } from '../cegis/auto-fix-engine.js';
import { FailureArtifactSchema as EngineFailureArtifactSchema } from '../cegis/types.js';
import type { FailureArtifact as EngineFailureArtifact, RepairAction as EngineRepairAction } from '../cegis/types.js';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';

const program = new Command();

type LoadedFailureArtifacts = FailureArtifact[] | FailureArtifactCollection;

interface AutoFixCliOptions {
  input?: string;
  output?: string;
  dryRun?: boolean;
  maxIterations?: string;
  confidence?: string;
  noBackup?: boolean;
  verbose?: boolean;
}

interface AnalysisCliOptions {
  input?: string;
  output?: string;
  verbose?: boolean;
}

interface CreateArtifactCliOptions {
  title?: string;
  description?: string;
  severity?: FailureArtifact['severity'];
  category?: FailureArtifact['category'];
  file?: string;
  line?: string;
  output: string;
}

interface ValidateCliOptions {
  input?: string;
}

interface HistoryCliOptions {
  count?: string;
}

interface DemoCliOptions {
  output: string;
  count?: string;
}

program
  .name('ae-fix')
  .description('AE-Framework Auto-Fix CLI - CEGIS-based automated repair')
  .version('1.0.0');

// Main fix command
program
  .command('fix')
  .description('Analyze and fix failure artifacts')
  .option('-i, --input <path>', 'Input failure artifacts file (JSON)')
  .option('-o, --output <dir>', 'Output directory for fixes', '.ae/auto-fix')
  .option('--dry-run', 'Analyze without making changes', false)
  .option('--max-iterations <number>', 'Maximum fix iterations', '10')
  .option('--confidence <threshold>', 'Minimum confidence threshold (0-1)', '0.7')
  .option('--no-backup', 'Skip backup of original files')
  .option('--verbose', 'Verbose output', false)
  .action(async (options: AutoFixCliOptions) => {
    try {
      await executeAutoFix(options);
    } catch (error: unknown) {
      console.error(chalk.red('❌ Auto-fix failed:'), toMessage(error));
      safeExit(1);
    }
  });

// Analyze command (analysis only)
program
  .command('analyze')
  .description('Analyze failure artifacts without fixing')
  .option('-i, --input <path>', 'Input failure artifacts file (JSON)')
  .option('-o, --output <dir>', 'Output directory for analysis', '.ae/analysis')
  .option('--verbose', 'Verbose output', false)
  .action(async (options: AnalysisCliOptions) => {
    try {
      await executeAnalysis(options);
    } catch (error: unknown) {
      console.error(chalk.red('❌ Analysis failed:'), toMessage(error));
      safeExit(1);
    }
  });

// Create failure artifact command
program
  .command('create-artifact')
  .description('Create a failure artifact from error information')
  .option('-t, --title <title>', 'Failure title')
  .option('-d, --description <desc>', 'Failure description')
  .option('-s, --severity <level>', 'Severity level (critical|major|minor|info)', 'major')
  .option('-c, --category <cat>', 'Failure category')
  .option('-f, --file <path>', 'Source file location')
  .option('-l, --line <number>', 'Line number')
  .option('-o, --output <path>', 'Output file path', 'failure-artifact.json')
  .action(async (options: CreateArtifactCliOptions) => {
    try {
      await createFailureArtifact(options);
    } catch (error: unknown) {
      console.error(chalk.red('❌ Failed to create artifact:'), toMessage(error));
      safeExit(1);
    }
  });

// Validate failure artifacts
program
  .command('validate')
  .description('Validate failure artifact schema')
  .option('-i, --input <path>', 'Input failure artifacts file (JSON)')
  .action(async (options: ValidateCliOptions) => {
    try {
      await validateArtifacts(options);
    } catch (error: unknown) {
      console.error(chalk.red('❌ Validation failed:'), toMessage(error));
      safeExit(1);
    }
  });

// List fix history
program
  .command('history')
  .description('Show auto-fix execution history')
  .option('-n, --count <number>', 'Number of recent fixes to show', '10')
  .action(async (options: HistoryCliOptions) => {
    try {
      await showFixHistory(options);
    } catch (error: unknown) {
      console.error(chalk.red('❌ Failed to show history:'), toMessage(error));
      safeExit(1);
    }
  });

// Demo command for testing
program
  .command('demo')
  .description('Generate demo failure artifacts for testing')
  .option('-o, --output <path>', 'Output file path', 'demo-failures.json')
  .option('--count <number>', 'Number of demo failures', '5')
  .action(async (options: DemoCliOptions) => {
    try {
      await generateDemoArtifacts(options);
    } catch (error: unknown) {
      console.error(chalk.red('❌ Demo generation failed:'), toMessage(error));
      process.exit(1);
    }
  });

// Execute auto-fix
const toFailureArtifactArray = (artifacts: LoadedFailureArtifacts): FailureArtifact[] =>
  Array.isArray(artifacts) ? artifacts : artifacts.failures;

const SOURCE_TO_ENGINE_CATEGORY: Record<FailureArtifact['category'], EngineFailureArtifact['category']> = {
  specification_mismatch: 'runtime_error',
  contract_violation: 'contract_violation',
  type_error: 'type_error',
  runtime_error: 'runtime_error',
  performance_regression: 'performance_issue',
  security_violation: 'security_violation',
  quality_gate_failure: 'lint_error',
  drift_detection: 'dependency_issue',
  test_failure: 'test_failure',
};

const SOURCE_TO_ENGINE_ACTION_TYPE: Record<
  FailureArtifact['suggestedActions'][number]['type'],
  EngineRepairAction['type']
> = {
  code_change: 'code_change',
  spec_update: 'validation_update',
  config_change: 'config_change',
  dependency_update: 'dependency_update',
  test_update: 'test_update',
  documentation_update: 'documentation_update',
};

const toEnginePhase = (phase: FailureArtifact['context']['phase']): EngineFailureArtifact['context']['phase'] => {
  switch (phase) {
    case 'intent':
    case 'formal':
    case 'test':
    case 'code':
    case 'verify':
    case 'operate':
      return phase;
    default:
      return undefined;
  }
};

const toEngineMetrics = (metrics: FailureArtifact['evidence']['metrics']): Record<string, number> => {
  const normalized: Record<string, number> = {};
  if (!metrics) {
    return normalized;
  }
  for (const [key, value] of Object.entries(metrics)) {
    if (typeof value === 'number' && Number.isFinite(value)) {
      normalized[key] = value;
      continue;
    }
    if (typeof value === 'boolean') {
      normalized[key] = value ? 1 : 0;
    }
  }
  return normalized;
};

const toRiskLevel = (severity: FailureArtifact['severity']): EngineRepairAction['riskLevel'] => {
  switch (severity) {
    case 'critical':
      return 5;
    case 'major':
      return 4;
    case 'minor':
      return 2;
    case 'info':
    default:
      return 1;
  }
};

const toEngineSuggestedActions = (
  actions: FailureArtifact['suggestedActions'],
  severity: FailureArtifact['severity'],
): EngineFailureArtifact['suggestedActions'] =>
  actions.map((action) => ({
    type: SOURCE_TO_ENGINE_ACTION_TYPE[action.type],
    description: action.description,
    confidence: action.confidence,
    riskLevel: toRiskLevel(severity),
    estimatedEffort: 'medium',
    ...(action.targetFile ? { filePath: action.targetFile } : {}),
    dependencies: [],
    prerequisites: action.prerequisites,
  }));

const toEngineFailureArtifact = (artifact: FailureArtifact): EngineFailureArtifact => {
  const filePath = artifact.location?.file ?? 'unknown';
  const line = artifact.location?.line ?? 1;
  const phase = toEnginePhase(artifact.context.phase);
  const converted: EngineFailureArtifact = {
    id: artifact.id,
    title: artifact.title,
    description: artifact.description,
    severity: artifact.severity,
    category: SOURCE_TO_ENGINE_CATEGORY[artifact.category],
    ...(artifact.location
      ? {
          location: {
            filePath,
            startLine: line,
            endLine: line,
            ...(artifact.location.column !== undefined
              ? { startColumn: artifact.location.column, endColumn: artifact.location.column }
              : {}),
            ...(artifact.location.function ? { functionName: artifact.location.function } : {}),
            ...(artifact.location.module ? { className: artifact.location.module } : {}),
          },
        }
      : {}),
    context: {
      environment: artifact.context.environment,
      timestamp: artifact.context.timestamp,
      ...(phase ? { phase } : {}),
      ...(artifact.context.commitHash ? { gitCommit: artifact.context.commitHash } : {}),
      ...(artifact.context.branch ? { gitBranch: artifact.context.branch } : {}),
    },
    evidence: {
      ...(artifact.evidence.stackTrace ? { stackTrace: artifact.evidence.stackTrace } : {}),
      errorMessage: artifact.description,
      errorType: artifact.category,
      logs: artifact.evidence.logs,
      metrics: toEngineMetrics(artifact.evidence.metrics),
      dependencies: [],
      relatedFiles: artifact.location?.file ? [artifact.location.file] : [],
    },
    ...(artifact.rootCause
      ? {
          rootCause: {
            primaryCause: artifact.rootCause.hypothesis,
            contributingFactors: artifact.rootCause.evidence,
            confidence: artifact.rootCause.confidence,
            reasoning: artifact.rootCause.hypothesis,
            suggestedActions: artifact.rootCause.relatedFailures,
          },
        }
      : {}),
    suggestedActions: toEngineSuggestedActions(artifact.suggestedActions, artifact.severity),
    relatedArtifacts: artifact.childFailureIds,
    metadata: {
      createdAt: artifact.createdAt,
      updatedAt: artifact.updatedAt,
      version: artifact.schemaVersion,
      tags: artifact.tags,
      ...(artifact.evidence.environmentInfo ? { environment: artifact.evidence.environmentInfo } : {}),
      source: 'ae-fix-cli',
    },
  };

  return EngineFailureArtifactSchema.parse(converted);
};

const toEngineFailureArtifactArray = (artifacts: LoadedFailureArtifacts): EngineFailureArtifact[] =>
  toFailureArtifactArray(artifacts).map(toEngineFailureArtifact);

const hasFailureCollectionShape = (value: unknown): value is { failures: unknown[] } => {
  if (typeof value !== 'object' || value === null || !('failures' in value)) {
    return false;
  }
  const failures = (value as { failures?: unknown }).failures;
  return Array.isArray(failures);
};

async function executeAutoFix(options: AutoFixCliOptions): Promise<void> {
  console.log(chalk.blue('🔧 AE-Framework Auto-Fix Engine'));
  console.log(chalk.gray('====================================='));

  // Load failure artifacts
  const artifacts = await loadFailureArtifacts(options.input);
  console.log(chalk.green(`📥 Loaded ${Array.isArray(artifacts) ? artifacts.length : artifacts.failures.length} failure artifacts`));

  // Configure fix options
  const fixOptions: AutoFixOptions = {
    dryRun: options.dryRun || false,
    maxIterations: Number.parseInt(options.maxIterations ?? '10', 10) || 10,
    confidenceThreshold: Number.parseFloat(options.confidence ?? '0.7') || 0.7,
    outputDir: options.output || '.ae/auto-fix',
  };

  if (fixOptions.dryRun) {
    console.log(chalk.yellow('🔍 Running in dry-run mode'));
  }

  console.log(chalk.gray(`Settings: max-iterations=${fixOptions.maxIterations}, confidence≥${fixOptions.confidenceThreshold}`));

  // Execute fixes
  const engine = new AutoFixEngine();
  const artifactArray = toEngineFailureArtifactArray(artifacts);
  const result = await engine.executeFixes(artifactArray, fixOptions);

  // Display results
  console.log(chalk.gray('\n🎯 Fix Results:'));
  console.log(`${result.success ? '✅' : '❌'} Overall Success: ${result.success}`);
  console.log(`🔧 Applied Actions: ${result.appliedActions.length}`);
  console.log(`📁 Generated Files: ${result.generatedFiles.length}`);
  console.log(`💾 Backup Files: ${result.backupFiles.length}`);

  if (result.errors.length > 0) {
    console.log(chalk.red(`\n❌ Errors (${result.errors.length}):`));
    for (const error of result.errors) {
      console.log(chalk.red(`  • ${error}`));
    }
  }

  if (result.recommendations.length > 0) {
    console.log(chalk.yellow(`\n💡 Recommendations (${result.recommendations.length}):`));
    for (const rec of result.recommendations) {
      console.log(chalk.yellow(`  • ${rec}`));
    }
  }

  if (options.verbose) {
    console.log(chalk.gray('\n📋 Applied Actions:'));
    for (const action of result.appliedActions) {
      console.log(`  • ${action.type}: ${action.description}`);
      if (action.targetFile) {
        console.log(`    📁 File: ${action.targetFile}`);
      }
      console.log(`    🎯 Confidence: ${((action.confidence || 0) * 100).toFixed(1)}%`);
    }
  }

  console.log(chalk.green(`\n✨ Auto-fix completed! Check ${fixOptions.outputDir} for results.`));
}

// Execute analysis only
async function executeAnalysis(options: AnalysisCliOptions): Promise<void> {
  console.log(chalk.blue('🔍 AE-Framework Failure Analysis'));
  console.log(chalk.gray('=================================='));

  const artifacts = await loadFailureArtifacts(options.input);
  console.log(chalk.green(`📥 Loaded ${Array.isArray(artifacts) ? artifacts.length : artifacts.failures.length} failure artifacts`));

  const engine = new AutoFixEngine();
  const artifactArray = toEngineFailureArtifactArray(artifacts);
  const analysis = await engine.executeFixes(artifactArray, {
    outputDir: options.output || '.ae/analysis',
    dryRun: true,
  });

  console.log(chalk.cyan('\n📊 Analysis Results:'));
  console.log(analysis.analysis);

  console.log(chalk.cyan('\n🔧 Proposed Fixes:'));
  for (const fix of (analysis.proposedFixes || []).slice(0, 10)) { // Show top 10
    console.log(`  • ${fix.type}: ${fix.description}`);
    console.log(`    🎯 Confidence: ${(fix.confidence * 100).toFixed(1)}%`);
  }

  if ((analysis.proposedFixes || []).length > 10) {
    console.log(chalk.gray(`    ... and ${(analysis.proposedFixes || []).length - 10} more`));
  }

  console.log(chalk.yellow('\n⚠️ Risk Assessment:'));
  console.log(analysis.riskAssessment);

  // Save analysis to file
  const outputDir = options.output || '.ae/analysis';
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }

  const analysisPath = path.join(outputDir, 'analysis-report.md');
  const fullReport = `${analysis.analysis}\n\n${analysis.riskAssessment}`;
  fs.writeFileSync(analysisPath, fullReport);

  console.log(chalk.green(`\n✨ Analysis completed! Report saved to ${analysisPath}`));
}

// Create failure artifact
async function createFailureArtifact(options: CreateArtifactCliOptions): Promise<void> {
  console.log(chalk.blue('📝 Creating Failure Artifact'));

  if (!options.title || !options.description) {
    throw new Error('Title and description are required');
  }

  const artifact = FailureArtifactFactory.create({
    title: options.title,
    description: options.description,
    ...(options.severity ? { severity: options.severity } : {}),
    category: options.category || 'runtime_error',
    ...(options.file ? {
      location: {
        file: options.file,
        line: options.line ? Number.parseInt(options.line, 10) : undefined,
      },
    } : {}),
  });

  fs.writeFileSync(options.output, JSON.stringify(artifact, null, 2));
  
  console.log(chalk.green(`✅ Failure artifact created: ${options.output}`));
  console.log(chalk.gray(`   ID: ${artifact.id}`));
  console.log(chalk.gray(`   Title: ${artifact.title}`));
  console.log(chalk.gray(`   Severity: ${artifact.severity}`));
  console.log(chalk.gray(`   Category: ${artifact.category}`));
}

// Validate artifacts
async function validateArtifacts(options: ValidateCliOptions): Promise<void> {
  console.log(chalk.blue('✅ Validating Failure Artifacts'));

  if (!options.input) {
    throw new Error('Input file path is required');
  }

  const data: unknown = JSON.parse(fs.readFileSync(options.input, 'utf8'));
  
  try {
    if (Array.isArray(data)) {
      // Validate each artifact
      for (let i = 0; i < data.length; i++) {
        validateFailureArtifact(data[i]);
      }
      console.log(chalk.green(`✅ All ${data.length} artifacts are valid`));
    } else if (hasFailureCollectionShape(data)) {
      // Validate collection
      validateFailureArtifactCollection(data);
      console.log(chalk.green(`✅ Collection with ${data.failures.length} artifacts is valid`));
    } else {
      // Validate single artifact
      validateFailureArtifact(data);
      console.log(chalk.green('✅ Single artifact is valid'));
    }
  } catch (error: unknown) {
    console.error(chalk.red('❌ Validation failed:'), toMessage(error));
    safeExit(1);
  }
}

// Show fix history
async function showFixHistory(_options: HistoryCliOptions): Promise<void> {
  console.log(chalk.blue('📚 Auto-Fix History'));
  console.log(chalk.gray('==================='));

  // In a real implementation, this would load from persistent storage
  console.log(chalk.yellow('📝 Note: History is not persisted in this demo version'));
  console.log(chalk.gray('History would show recent auto-fix executions, success rates, and patterns'));
}

// Generate demo artifacts
async function generateDemoArtifacts(options: DemoCliOptions): Promise<void> {
  console.log(chalk.blue('🎪 Generating Demo Failure Artifacts'));

  const count = Number.parseInt(options.count ?? '5', 10) || 5;
  const artifacts: FailureArtifact[] = [];

  // Generate various types of demo failures
  artifacts.push(FailureArtifactFactory.fromError(
    new Error('Contract validation failed for user registration'),
    { environment: 'staging', component: 'auth-service' }
  ));

  artifacts.push(FailureArtifactFactory.fromTestFailure(
    'should validate email format',
    'Expected email validation to pass but got rejection',
    { file: 'tests/auth.test.ts', line: 42 }
  ));

  artifacts.push(FailureArtifactFactory.fromContractViolation(
    'UserProfile',
    { email: 'string', age: 'number' },
    { email: 'user@example.com', age: '25' },
    { file: 'src/models/user.ts', line: 15 }
  ));

  // Add more demo artifacts as needed
  while (artifacts.length < count) {
    artifacts.push(FailureArtifactFactory.create({
      title: `Demo Failure ${artifacts.length + 1}`,
      description: `This is a demo failure artifact for testing purposes`,
      severity: (['critical', 'major', 'minor'][Math.floor(Math.random() * 3)] as 'critical' | 'major' | 'minor'),
      category: 'runtime_error',
    }));
  }

  const collection: FailureArtifactCollection = {
    failures: artifacts,
    metadata: {
      generatedAt: new Date().toISOString(),
      totalCount: artifacts.length,
      environment: 'demo',
      source: 'ae-fix demo command',
    },
    schemaVersion: '1.0.0',
  };

  fs.writeFileSync(options.output, JSON.stringify(collection, null, 2));
  
  console.log(chalk.green(`✅ Generated ${count} demo failure artifacts: ${options.output}`));
  console.log(chalk.gray('You can now test auto-fix with: ae-fix fix -i ' + options.output));
}

// Utility function to load failure artifacts
async function loadFailureArtifacts(inputPath?: string): Promise<FailureArtifact[] | FailureArtifactCollection> {
  if (!inputPath) {
    // Try to find failure artifacts in common locations
    const commonPaths = [
      '.ae/failures.json',
      'failure-artifacts.json',
      'failures.json',
      '.ae/auto-fix/failures.json',
    ];

    for (const tryPath of commonPaths) {
      if (fs.existsSync(tryPath)) {
        inputPath = tryPath;
        console.log(chalk.gray(`📁 Found failure artifacts at: ${tryPath}`));
        break;
      }
    }

    if (!inputPath) {
      throw new Error('No input file specified and no failure artifacts found in common locations.\n' +
                     'Use -i option to specify input file, or run "ae-fix demo" to generate test data.');
    }
  }

  if (!fs.existsSync(inputPath)) {
    throw new Error(`Input file not found: ${inputPath}`);
  }

  const data = JSON.parse(fs.readFileSync(inputPath, 'utf8'));
  
  // Validate the data
  if (Array.isArray(data)) {
    return data.map(validateFailureArtifact);
  } else if (data.failures) {
    return validateFailureArtifactCollection(data);
  } else {
    return [validateFailureArtifact(data)];
  }
}

// Main execution
if (import.meta.url === `file://${process.argv[1]}`) {
  program.parse();
}
