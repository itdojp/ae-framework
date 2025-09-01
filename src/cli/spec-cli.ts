#!/usr/bin/env node

/**
 * AE-Framework Spec CLI Integration
 * Integrates spec-compiler into main ae-framework CLI
 */

import { Command } from 'commander';
import { AESpecCompiler } from '../../packages/spec-compiler/src/index.js';
import { resolve } from 'path';
import { readFileSync } from 'fs';
import chalk from 'chalk';

export function createSpecCommand(): Command {
  const spec = new Command('spec');
  spec.description('AE-Spec compilation and validation commands');

  spec
    .command('compile')
    .description('Compile AE-Spec markdown to AE-IR JSON')
    .requiredOption('-i, --input <file>', 'Input markdown file')
    .option('-o, --output <file>', 'Output JSON file (default: .ae/ae-ir.json)')
    .option('--no-validate', 'Skip validation during compilation')
    .action(async (options) => {
      try {
        console.log(chalk.blue('🔄 Compiling AE-Spec...'));
        
        const compiler = new AESpecCompiler();
        const outputPath = options.output || '.ae/ae-ir.json';
        
        const ir = await compiler.compile({
          inputPath: resolve(options.input),
          outputPath: resolve(outputPath),
          validate: options.validate,
        });
        
        console.log(chalk.green('✅ AE-Spec compiled successfully!'));
        console.log(chalk.gray(`   Input:  ${options.input}`));
        console.log(chalk.gray(`   Output: ${outputPath}`));
        console.log(chalk.gray(`   Entities: ${ir.domain.length}`));
        console.log(chalk.gray(`   APIs: ${ir.api.length}`));
        console.log(chalk.gray(`   Use Cases: ${ir.usecases.length}`));
        
      } catch (error) {
        console.error(chalk.red(`❌ Compilation failed: ${(error as Error).message}`));
        process.exit(1);
      }
    });

  spec
    .command('lint')
    .description('Lint AE-IR for quality issues')
    .option('-i, --input <file>', 'Input AE-IR JSON file', '.ae/ae-ir.json')
    .option('--max-errors <n>', 'Maximum allowed errors', parseInt, 0)
    .option('--max-warnings <n>', 'Maximum allowed warnings', parseInt, 10)
    .action(async (options) => {
      try {
        const inputPath = options.input || '.ae/ae-ir.json';
        console.log(chalk.blue(`🔍 Linting ${inputPath}...`));
        
        const irContent = readFileSync(resolve(inputPath), 'utf-8');
        const ir = JSON.parse(irContent);
        
        const compiler = new AESpecCompiler();
        const result = await compiler.lint(ir);
        
        console.log(chalk.blue('\n📊 Lint Results:'));
        console.log(`   ${result.summary.errors > 0 ? chalk.red('❌') : chalk.green('✅')} Errors: ${result.summary.errors}`);
        console.log(`   ${result.summary.warnings > 0 ? chalk.yellow('⚠️ ') : chalk.green('✅')} Warnings: ${result.summary.warnings}`);
        console.log(`   ${chalk.blue('ℹ️ ')} Info: ${result.summary.infos}`);
        
        if (result.issues.length > 0) {
          console.log('\n📋 Issues:');
          for (const issue of result.issues.slice(0, 10)) {
            const icon = issue.severity === 'error' ? chalk.red('❌') : 
                        issue.severity === 'warn' ? chalk.yellow('⚠️ ') : 
                        chalk.blue('ℹ️ ');
            const location = issue.location?.section ? 
              chalk.gray(` [${issue.location.section}]`) : '';
            
            console.log(`${icon} ${chalk.bold(issue.id)}: ${issue.message}${location}`);
            if (issue.suggestion) {
              console.log(chalk.gray(`   💡 ${issue.suggestion}`));
            }
          }
          
          if (result.issues.length > 10) {
            console.log(chalk.gray(`\n   ... and ${result.issues.length - 10} more issues`));
          }
        }
        
        // Check thresholds
        const failed = 
          result.summary.errors > options.maxErrors ||
          result.summary.warnings > options.maxWarnings;
        
        if (failed) {
          console.log(chalk.red('\n❌ Quality thresholds exceeded'));
          process.exit(1);
        } else {
          console.log(chalk.green('\n✅ All quality checks passed'));
        }
        
      } catch (error) {
        console.error(chalk.red(`❌ Linting failed: ${(error as Error).message}`));
        process.exit(1);
      }
    });

  spec
    .command('validate')
    .description('Validate AE-Spec file (compile + lint)')
    .requiredOption('-i, --input <file>', 'Input markdown file')
    .option('--output <file>', 'Output JSON file (default: .ae/ae-ir.json)')
    .option('--max-errors <n>', 'Maximum allowed errors', parseInt, 0)
    .option('--max-warnings <n>', 'Maximum allowed warnings', parseInt, 10)
    .option('--relaxed', 'Relax strict schema errors to warnings')
    .option('--desc-max <n>', 'Override description max length (e.g., 1000)', parseInt)
    .action(async (options) => {
      try {
        console.log(chalk.blue(`🔍 Validating ${options.input}...`));
        
        const compiler = new AESpecCompiler();
        const outputPath = options.output || '.ae/ae-ir.json';
        // Set relaxed/configurable limits via env for spec-compiler
        if (options.relaxed) process.env.AE_SPEC_RELAXED = '1';
        if (typeof options.descMax === 'number' && Number.isFinite(options.descMax) && options.descMax > 0) {
          process.env.AE_SPEC_DESC_MAX = String(options.descMax);
          process.env.AE_SPEC_INVARIANT_DESC_MAX = String(options.descMax);
          process.env.AE_SPEC_DOMAIN_DESC_MAX = String(options.descMax);
          process.env.AE_SPEC_FIELD_DESC_MAX = String(options.descMax);
        }
        
        // Compile
        console.log(chalk.blue('📝 Compiling...'));
        const ir = await compiler.compile({
          inputPath: resolve(options.input),
          outputPath: resolve(outputPath),
          validate: false, // We'll lint separately
        });
        
        console.log(chalk.green('✅ Compilation successful'));
        
        // Lint
        console.log(chalk.blue('🔍 Linting...'));
        const lintResult = await compiler.lint(ir);
        
        console.log(chalk.blue('\n📊 Validation Results:'));
        console.log(`   ${lintResult.summary.errors > 0 ? chalk.red('❌') : chalk.green('✅')} Errors: ${lintResult.summary.errors}`);
        console.log(`   ${lintResult.summary.warnings > 0 ? chalk.yellow('⚠️ ') : chalk.green('✅')} Warnings: ${lintResult.summary.warnings}`);
        console.log(`   ${chalk.blue('ℹ️ ')} Info: ${lintResult.summary.infos}`);
        
        if (lintResult.issues.length > 0) {
          console.log('\n📋 Top Issues:');
          for (const issue of lintResult.issues.slice(0, 5)) {
            const icon = issue.severity === 'error' ? chalk.red('❌') : 
                        issue.severity === 'warn' ? chalk.yellow('⚠️ ') : 
                        chalk.blue('ℹ️ ');
            console.log(`${icon} ${issue.message}`);
          }
          
          if (lintResult.issues.length > 5) {
            console.log(chalk.gray(`\n   ... and ${lintResult.issues.length - 5} more issues`));
          }
        }
        
        const failed = 
          lintResult.summary.errors > options.maxErrors ||
          lintResult.summary.warnings > options.maxWarnings;
        
        if (failed) {
          console.log(chalk.red('\n❌ Validation failed - quality thresholds exceeded'));
          console.log(chalk.red(`   Max errors allowed: ${options.maxErrors}, found: ${lintResult.summary.errors}`));
          console.log(chalk.red(`   Max warnings allowed: ${options.maxWarnings}, found: ${lintResult.summary.warnings}`));
          process.exit(1);
        } else {
          console.log(chalk.green('\n✅ Validation passed successfully'));
          console.log(chalk.gray(`   AE-IR saved to: ${outputPath}`));
        }
        
      } catch (error) {
        console.error(chalk.red(`❌ Validation failed: ${(error as Error).message}`));
        process.exit(1);
      }
    });

  return spec;
}

export default createSpecCommand;
