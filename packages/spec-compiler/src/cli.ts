#!/usr/bin/env node

import { Command } from 'commander';
import { AESpecCompiler } from './compiler.js';
import { readFileSync } from 'fs';
import { resolve } from 'path';

const program = new Command();

program
  .name('ae-spec')
  .description('AE-Spec compiler for ae-framework')
  .version('1.0.0');

program
  .command('compile')
  .description('Compile AE-Spec markdown to AE-IR JSON')
  .requiredOption('-i, --input <file>', 'Input markdown file')
  .option('-o, --output <file>', 'Output JSON file (default: stdout)')
  .option('--no-validate', 'Skip validation during compilation')
  .option('--source-map', 'Include source location information')
  .action(async (options) => {
    try {
      const compiler = new AESpecCompiler();
      const ir = await compiler.compile({
        inputPath: resolve(options.input),
        outputPath: options.output ? resolve(options.output) : undefined,
        validate: options.validate,
        sourceMap: options.sourceMap,
      });
      
      if (!options.output) {
        console.log(JSON.stringify(ir, null, 2));
      } else {
        console.log(`✅ Compiled successfully: ${options.input} → ${options.output}`);
      }
    } catch (error) {
      console.error(`❌ Compilation failed: ${(error as Error).message}`);
      process.exit(1);
    }
  });

program
  .command('lint')
  .description('Lint AE-IR for quality issues')
  .requiredOption('-i, --input <file>', 'Input AE-IR JSON file')
  .option('--max-errors <n>', 'Maximum allowed errors', parseInt, 0)
  .option('--max-warnings <n>', 'Maximum allowed warnings', parseInt, -1)
  .option('--format <type>', 'Output format', 'table')
  .action(async (options) => {
    try {
      const irContent = readFileSync(resolve(options.input), 'utf-8');
      const ir = JSON.parse(irContent);
      
      const compiler = new AESpecCompiler();
      const result = await compiler.lint(ir);
      
      console.log(`\n📊 Lint Results for ${options.input}:`);
      console.log(`   Errors: ${result.summary.errors}`);
      console.log(`   Warnings: ${result.summary.warnings}`);
      console.log(`   Info: ${result.summary.infos}\n`);
      
      if (result.issues.length > 0) {
        for (const issue of result.issues) {
          const icon = issue.severity === 'error' ? '❌' : 
                      issue.severity === 'warn' ? '⚠️' : 'ℹ️';
          const location = issue.location?.section ? 
            ` [${issue.location.section}]` : '';
          
          console.log(`${icon} ${issue.id}: ${issue.message}${location}`);
          if (issue.suggestion) {
            console.log(`   💡 ${issue.suggestion}`);
          }
        }
      } else {
        console.log('✅ No issues found!');
      }
      
      // Check thresholds
      const failed = 
        result.summary.errors > options.maxErrors ||
        (options.maxWarnings >= 0 && result.summary.warnings > options.maxWarnings);
      
      if (failed) {
        console.log('\n❌ Quality thresholds exceeded');
        process.exit(1);
      } else {
        console.log('\n✅ All quality checks passed');
      }
      
    } catch (error) {
      console.error(`❌ Linting failed: ${(error as Error).message}`);
      process.exit(1);
    }
  });

program
  .command('validate')
  .description('Validate an AE-Spec file (compile + lint)')
  .requiredOption('-i, --input <file>', 'Input markdown file')
  .option('--max-errors <n>', 'Maximum allowed errors', parseInt, 0)
  .option('--max-warnings <n>', 'Maximum allowed warnings', parseInt, 10)
  .action(async (options) => {
    try {
      console.log(`🔍 Validating ${options.input}...`);
      
      const compiler = new AESpecCompiler();
      const ir = await compiler.compile({
        inputPath: resolve(options.input),
        validate: false, // We'll lint separately for better reporting
      });
      
      console.log('✅ Compilation successful');
      
      const lintResult = await compiler.lint(ir);
      
      console.log(`\n📊 Validation Results:`);
      console.log(`   Errors: ${lintResult.summary.errors}`);
      console.log(`   Warnings: ${lintResult.summary.warnings}`);
      console.log(`   Info: ${lintResult.summary.infos}\n`);
      
      if (lintResult.issues.length > 0) {
        for (const issue of lintResult.issues.slice(0, 10)) { // Show first 10
          const icon = issue.severity === 'error' ? '❌' : 
                      issue.severity === 'warn' ? '⚠️' : 'ℹ️';
          console.log(`${icon} ${issue.message}`);
        }
        
        if (lintResult.issues.length > 10) {
          console.log(`\n... and ${lintResult.issues.length - 10} more issues`);
        }
      }
      
      const failed = 
        lintResult.summary.errors > options.maxErrors ||
        lintResult.summary.warnings > options.maxWarnings;
      
      if (failed) {
        console.log('\n❌ Validation failed - quality thresholds exceeded');
        process.exit(1);
      } else {
        console.log('\n✅ Validation passed successfully');
      }
      
    } catch (error) {
      console.error(`❌ Validation failed: ${(error as Error).message}`);
      process.exit(1);
    }
  });

// Handle unknown commands
program.on('command:*', () => {
  console.error('Invalid command: %s\nSee --help for a list of available commands.', program.args.join(' '));
  process.exit(1);
});

if (process.argv.length < 3) {
  program.help();
} else {
  program.parse();
}