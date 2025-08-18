#!/usr/bin/env node

/**
 * Code Generation CLI
 * Command-line interface for deterministic code generation and drift detection
 */

import { Command } from 'commander';
import { resolve, join } from 'path';
import chalk from 'chalk';
import { DeterministicCodeGenerator } from '../codegen/deterministic-generator.js';
import { DriftDetector } from '../codegen/drift-detector.js';

export function createCodegenCommand(): Command {
  const codegen = new Command('codegen');
  codegen.description('Deterministic code generation and drift detection');

  codegen
    .command('generate')
    .description('Generate code from AE-IR specification')
    .requiredOption('-i, --input <file>', 'Input AE-IR JSON file')
    .requiredOption('-o, --output <dir>', 'Output directory for generated code')
    .requiredOption('-t, --target <type>', 'Target type (typescript|react|api|database)')
    .option('--template-dir <dir>', 'Template directory')
    .option('--no-drift-detection', 'Disable drift detection')
    .option('--no-preserve-changes', 'Do not preserve manual changes')
    .option('--hash-algorithm <algo>', 'Hash algorithm (sha256|md5)', 'sha256')
    .action(async (options) => {
      try {
        console.log(chalk.blue('🏗️  Starting code generation...'));
        console.log(chalk.gray(`   Input: ${options.input}`));
        console.log(chalk.gray(`   Output: ${options.output}`));
        console.log(chalk.gray(`   Target: ${options.target}`));

        const generator = new DeterministicCodeGenerator({
          inputPath: resolve(options.input),
          outputDir: resolve(options.output),
          target: options.target,
          templateDir: options.templateDir ? resolve(options.templateDir) : undefined,
          enableDriftDetection: options.driftDetection,
          preserveManualChanges: options.preserveChanges,
          hashAlgorithm: options.hashAlgorithm,
        });

        const manifest = await generator.generate();

        console.log(chalk.green('✅ Code generation completed!'));
        console.log(chalk.gray(`   Files generated: ${manifest.files.length}`));
        console.log(chalk.gray(`   Manifest: ${join(options.output, '.codegen-manifest.json')}`));

        // Display generated files summary
        const filesByType = manifest.files.reduce((acc, file) => {
          const ext = file.filePath.split('.').pop() || 'unknown';
          acc[ext] = (acc[ext] || 0) + 1;
          return acc;
        }, {} as Record<string, number>);

        console.log(chalk.blue('\n📁 Generated files by type:'));
        Object.entries(filesByType).forEach(([ext, count]) => {
          console.log(chalk.gray(`   ${ext}: ${count} files`));
        });

      } catch (error) {
        console.error(chalk.red(`❌ Code generation failed: ${(error as Error).message}`));
        process.exit(1);
      }
    });

  codegen
    .command('drift')
    .description('Detect drift in generated code')
    .requiredOption('-d, --code-dir <dir>', 'Directory containing generated code')
    .requiredOption('-s, --spec <file>', 'AE-IR specification file')
    .option('-m, --manifest <file>', 'Codegen manifest file')
    .option('--ignore <patterns...>', 'Ignore patterns for drift detection')
    .option('-v, --verbose', 'Enable verbose output')
    .option('--auto-fix', 'Auto-fix minor drift issues')
    .option('--format <type>', 'Output format (text|json)', 'text')
    .action(async (options) => {
      try {
        console.log(chalk.blue('🔍 Starting drift detection...'));
        console.log(chalk.gray(`   Code directory: ${options.codeDir}`));
        console.log(chalk.gray(`   Specification: ${options.spec}`));

        const detector = new DriftDetector({
          codeDir: resolve(options.codeDir),
          specPath: resolve(options.spec),
          manifestPath: options.manifest ? resolve(options.manifest) : undefined,
          ignorePatterns: options.ignore,
          verbose: options.verbose,
          autoFix: options.autoFix,
        });

        const report = await detector.detectDrift();

        if (options.format === 'json') {
          console.log(JSON.stringify(report, null, 2));
        } else {
          // Report already printed in verbose mode
          if (!options.verbose) {
            const statusColors = {
              'no_drift': chalk.green,
              'minor_drift': chalk.yellow,
              'major_drift': chalk.red,
              'critical_drift': chalk.red.bold,
            };

            console.log(chalk.blue('\n🎯 Drift Detection Results:'));
            console.log(`Status: ${statusColors[report.status](report.status.replace('_', ' ').toUpperCase())}`);
            console.log(`Files checked: ${report.summary.totalFiles}`);
            console.log(`Changes detected: ${report.changes.length}`);

            if (report.recommendations.length > 0) {
              console.log(chalk.blue('\n💡 Recommendations:'));
              report.recommendations.slice(0, 3).forEach(rec => {
                console.log(`  ${rec}`);
              });
              if (report.recommendations.length > 3) {
                console.log(chalk.gray(`  ... and ${report.recommendations.length - 3} more`));
              }
            }
          }
        }

        // Exit with appropriate code
        const exitCodes = {
          'no_drift': 0,
          'minor_drift': 1,
          'major_drift': 2,
          'critical_drift': 3,
        };
        process.exit(exitCodes[report.status]);

      } catch (error) {
        console.error(chalk.red(`❌ Drift detection failed: ${(error as Error).message}`));
        process.exit(1);
      }
    });

  codegen
    .command('watch')
    .description('Watch for specification changes and auto-regenerate')
    .requiredOption('-i, --input <file>', 'Input AE-IR JSON file')
    .requiredOption('-o, --output <dir>', 'Output directory for generated code')
    .requiredOption('-t, --target <type>', 'Target type (typescript|react|api|database)')
    .option('--debounce <ms>', 'Debounce time for file changes (ms)', '1000')
    .option('--template-dir <dir>', 'Template directory')
    .action(async (options) => {
      try {
        console.log(chalk.blue('👀 Starting watch mode...'));
        console.log(chalk.yellow('  Press Ctrl+C to stop'));
        
        const { watch } = await import('chokidar');
        
        let timeout: NodeJS.Timeout;
        const debounceMs = parseInt(options.debounce);

        const regenerate = async () => {
          try {
            console.log(chalk.blue('\n🔄 Specification changed, regenerating...'));
            
            const generator = new DeterministicCodeGenerator({
              inputPath: resolve(options.input),
              outputDir: resolve(options.output),
              target: options.target,
              templateDir: options.templateDir ? resolve(options.templateDir) : undefined,
              enableDriftDetection: true,
              preserveManualChanges: true,
            });

            const manifest = await generator.generate();
            console.log(chalk.green(`✅ Regenerated ${manifest.files.length} files`));
            
          } catch (error) {
            console.error(chalk.red(`❌ Regeneration failed: ${(error as Error).message}`));
          }
        };

        const watcher = watch(options.input, {
          persistent: true,
          ignoreInitial: true,
        });

        watcher.on('change', () => {
          clearTimeout(timeout);
          timeout = setTimeout(regenerate, debounceMs);
        });

        // Keep process alive
        process.on('SIGINT', () => {
          console.log(chalk.yellow('\n👋 Stopping watch mode...'));
          watcher.close();
          process.exit(0);
        });

        // Initial generation
        await regenerate();

      } catch (error) {
        console.error(chalk.red(`❌ Watch mode failed: ${(error as Error).message}`));
        process.exit(1);
      }
    });

  codegen
    .command('status')
    .description('Show current generation status and statistics')
    .requiredOption('-d, --code-dir <dir>', 'Directory containing generated code')
    .option('-m, --manifest <file>', 'Codegen manifest file')
    .action(async (options) => {
      try {
        const manifestPath = options.manifest || join(options.codeDir, '.codegen-manifest.json');
        
        if (!require('fs').existsSync(manifestPath)) {
          console.log(chalk.yellow('⚠️  No generation manifest found'));
          console.log(chalk.gray('   Run "codegen generate" first'));
          return;
        }

        const manifest = JSON.parse(require('fs').readFileSync(manifestPath, 'utf-8'));
        
        console.log(chalk.blue('📊 Code Generation Status'));
        console.log(chalk.blue('========================='));
        console.log(`Generated: ${new Date(manifest.metadata.generatedAt).toLocaleString()}`);
        console.log(`Spec hash: ${manifest.metadata.specHash.substring(0, 8)}...`);
        console.log(`Target: ${manifest.metadata.options.target}`);
        console.log(`Total files: ${manifest.files.length}`);

        // File type breakdown
        const filesByType = manifest.files.reduce((acc: Record<string, number>, file: any) => {
          const ext = file.filePath.split('.').pop() || 'unknown';
          acc[ext] = (acc[ext] || 0) + 1;
          return acc;
        }, {});

        console.log(chalk.blue('\n📁 File breakdown:'));
        Object.entries(filesByType).forEach(([ext, count]) => {
          console.log(`  ${ext}: ${count} files`);
        });

        // Recent files
        const recentFiles = manifest.files
          .sort((a: any, b: any) => new Date(b.timestamp).getTime() - new Date(a.timestamp).getTime())
          .slice(0, 5);

        console.log(chalk.blue('\n🕒 Recent files:'));
        recentFiles.forEach((file: any) => {
          console.log(`  ${file.filePath}`);
        });

      } catch (error) {
        console.error(chalk.red(`❌ Status check failed: ${(error as Error).message}`));
        process.exit(1);
      }
    });

  return codegen;
}

export default createCodegenCommand;