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
import { 
  FailureArtifact, 
  FailureArtifactCollection,
  validateFailureArtifact,
  validateFailureArtifactCollection,
  FailureArtifactFactory
} from '../cegis/failure-artifact-schema.js';
import { AutoFixEngine, AutoFixOptions } from '../cegis/auto-fix-engine.js';

const program = new Command();

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
  .action(async (options) => {
    try {
      await executeAutoFix(options);
    } catch (error) {
      console.error(chalk.red('❌ Auto-fix failed:'), error);
      process.exit(1);
    }
  });

// Analyze command (analysis only)
program
  .command('analyze')
  .description('Analyze failure artifacts without fixing')
  .option('-i, --input <path>', 'Input failure artifacts file (JSON)')
  .option('-o, --output <dir>', 'Output directory for analysis', '.ae/analysis')
  .option('--verbose', 'Verbose output', false)
  .action(async (options) => {
    try {
      await executeAnalysis(options);
    } catch (error) {
      console.error(chalk.red('❌ Analysis failed:'), error);
      process.exit(1);
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
  .action(async (options) => {
    try {
      await createFailureArtifact(options);
    } catch (error) {
      console.error(chalk.red('❌ Failed to create artifact:'), error);
      process.exit(1);
    }
  });

// Validate failure artifacts
program
  .command('validate')
  .description('Validate failure artifact schema')
  .option('-i, --input <path>', 'Input failure artifacts file (JSON)')
  .action(async (options) => {
    try {
      await validateArtifacts(options);
    } catch (error) {
      console.error(chalk.red('❌ Validation failed:'), error);
      process.exit(1);
    }
  });

// List fix history
program
  .command('history')
  .description('Show auto-fix execution history')
  .option('-n, --count <number>', 'Number of recent fixes to show', '10')
  .action(async (options) => {
    try {
      await showFixHistory(options);
    } catch (error) {
      console.error(chalk.red('❌ Failed to show history:'), error);
      process.exit(1);
    }
  });

// Demo command for testing
program
  .command('demo')
  .description('Generate demo failure artifacts for testing')
  .option('-o, --output <path>', 'Output file path', 'demo-failures.json')
  .option('--count <number>', 'Number of demo failures', '5')
  .action(async (options) => {
    try {
      await generateDemoArtifacts(options);
    } catch (error) {
      console.error(chalk.red('❌ Demo generation failed:'), error);
      process.exit(1);
    }
  });

// Execute auto-fix
async function executeAutoFix(options: any): Promise<void> {
  console.log(chalk.blue('🔧 AE-Framework Auto-Fix Engine'));
  console.log(chalk.gray('====================================='));

  // Load failure artifacts
  const artifacts = await loadFailureArtifacts(options.input);
  console.log(chalk.green(`📥 Loaded ${Array.isArray(artifacts) ? artifacts.length : artifacts.failures.length} failure artifacts`));

  // Configure fix options
  const fixOptions: AutoFixOptions = {
    dryRun: options.dryRun || false,
    maxIterations: parseInt(options.maxIterations) || 10,
    confidenceThreshold: parseFloat(options.confidence) || 0.7,
    // backupOriginals: !options.noBackup, // TODO: Verify property exists in interface
    outputDir: options.output || '.ae/auto-fix',
  };

  if (fixOptions.dryRun) {
    console.log(chalk.yellow('🔍 Running in dry-run mode'));
  }

  console.log(chalk.gray(`Settings: max-iterations=${fixOptions.maxIterations}, confidence≥${fixOptions.confidenceThreshold}`));

  // Execute fixes
  const engine = new AutoFixEngine();
  const artifactArray = Array.isArray(artifacts) ? artifacts : artifacts.failures;
  const transformedArtifacts = artifactArray.map(transformArtifactLocation);
  const result = await engine.executeFixes(transformedArtifacts, fixOptions);

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
async function executeAnalysis(options: any): Promise<void> {
  console.log(chalk.blue('🔍 AE-Framework Failure Analysis'));
  console.log(chalk.gray('=================================='));

  const artifacts = await loadFailureArtifacts(options.input);
  console.log(chalk.green(`📥 Loaded ${Array.isArray(artifacts) ? artifacts.length : artifacts.failures.length} failure artifacts`));

  const engine = new AutoFixEngine();
  const artifactArray = Array.isArray(artifacts) ? artifacts : artifacts.failures;
  const transformedArtifacts = artifactArray.map(transformArtifactLocation);
  const analysis = await engine.executeFixes(transformedArtifacts, {
    outputDir: options.output || '.ae/analysis',
    dryRun: true,
  });

  console.log(chalk.cyan('\n📊 Analysis Results:'));
  console.log(analysis.analysis);

  console.log(chalk.cyan('\n🔧 Proposed Fixes:'));
  for (const fix of analysis.proposedFixes.slice(0, 10)) { // Show top 10
    console.log(`  • ${fix.type}: ${fix.description}`);
    console.log(`    🎯 Confidence: ${(fix.confidence * 100).toFixed(1)}%`);
  }

  if (analysis.proposedFixes.length > 10) {
    console.log(chalk.gray(`    ... and ${analysis.proposedFixes.length - 10} more`));
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
async function createFailureArtifact(options: any): Promise<void> {
  console.log(chalk.blue('📝 Creating Failure Artifact'));

  if (!options.title || !options.description) {
    throw new Error('Title and description are required');
  }

  const artifact = FailureArtifactFactory.create({
    title: options.title,
    description: options.description,
    severity: options.severity,
    category: options.category || 'runtime_error',
    location: options.file ? {
      file: options.file,
      line: options.line ? parseInt(options.line) : undefined,
    } : undefined,
  });

  fs.writeFileSync(options.output, JSON.stringify(artifact, null, 2));
  
  console.log(chalk.green(`✅ Failure artifact created: ${options.output}`));
  console.log(chalk.gray(`   ID: ${artifact.id}`));
  console.log(chalk.gray(`   Title: ${artifact.title}`));
  console.log(chalk.gray(`   Severity: ${artifact.severity}`));
  console.log(chalk.gray(`   Category: ${artifact.category}`));
}

// Transform artifact location properties to expected format
interface TransformedArtifactLocation {
  filePath?: string;
  startLine?: number;
  endLine?: number;
  startColumn?: number;
  endColumn?: number;
  functionName?: string;
  className?: string;
}

interface SourceArtifactLocation {
  file?: string;
  line?: number;
  column?: number;
  function?: string;
  module?: string;
}

interface SourceFailureArtifact {
  location?: SourceArtifactLocation;
  [key: string]: any;
}

interface TransformedFailureArtifact {
  location?: TransformedArtifactLocation;
  [key: string]: any;
}

function transformArtifactLocation(artifact: SourceFailureArtifact): TransformedFailureArtifact {
  if (artifact.location) {
    const { location, ...rest } = artifact;
    return {
      ...rest,
      location: {
        filePath: location.file,
        startLine: location.line,
        endLine: location.line,
        startColumn: location.column,
        endColumn: location.column,
        functionName: location.function,
        className: location.module
      }
    };
  }
  return artifact;
}

// Validate artifacts
async function validateArtifacts(options: any): Promise<void> {
  console.log(chalk.blue('✅ Validating Failure Artifacts'));

  if (!options.input) {
    throw new Error('Input file path is required');
  }

  const data = JSON.parse(fs.readFileSync(options.input, 'utf8'));
  
  try {
    if (Array.isArray(data)) {
      // Validate each artifact
      for (let i = 0; i < data.length; i++) {
        validateFailureArtifact(data[i]);
      }
      console.log(chalk.green(`✅ All ${data.length} artifacts are valid`));
    } else if (data.failures) {
      // Validate collection
      validateFailureArtifactCollection(data);
      console.log(chalk.green(`✅ Collection with ${data.failures.length} artifacts is valid`));
    } else {
      // Validate single artifact
      validateFailureArtifact(data);
      console.log(chalk.green('✅ Single artifact is valid'));
    }
  } catch (error) {
    console.error(chalk.red('❌ Validation failed:'));
    console.error(chalk.red(error instanceof Error ? error.message : String(error)));
    process.exit(1);
  }
}

// Show fix history
async function showFixHistory(options: any): Promise<void> {
  console.log(chalk.blue('📚 Auto-Fix History'));
  console.log(chalk.gray('==================='));

  // In a real implementation, this would load from persistent storage
  console.log(chalk.yellow('📝 Note: History is not persisted in this demo version'));
  console.log(chalk.gray('History would show recent auto-fix executions, success rates, and patterns'));
}

// Generate demo artifacts
async function generateDemoArtifacts(options: any): Promise<void> {
  console.log(chalk.blue('🎪 Generating Demo Failure Artifacts'));

  const count = parseInt(options.count) || 5;
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
      severity: ['critical', 'major', 'minor'][Math.floor(Math.random() * 3)] as any,
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