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
import { toMessage } from '../utils/error-utils.js';

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
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Compilation failed: ${toMessage(error)}`));
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
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Linting failed: ${toMessage(error)}`));
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
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Validation failed: ${toMessage(error)}`));
        process.exit(1);
      }
    });

  // New: Natural language → AE-Spec synthesis with iterative refinement
  spec
    .command('synth')
    .description('Synthesize AE-Spec from natural-language requirements and iteratively refine to strict compliance')
    .requiredOption('-i, --input <file>', 'Input natural-language requirements (.md/.txt)')
    .option('-o, --output <file>', 'Output AE-Spec file (default: spec/generated-<ts>.ae-spec.md)')
    .option('-n, --iterations <n>', 'Max refinement iterations', parseInt, 5)
    .option('--relaxed-first', 'Start in relaxed mode (recommended)', true)
    .option('--max-warnings <n>', 'Allowed warnings in final strict validation', parseInt, 10)
    .action(async (options) => {
      const { input, iterations, maxWarnings } = options;
      const out = options.output || `spec/generated-${Date.now()}.ae-spec.md`;
      const artifactsDir = 'artifacts/spec-synthesis';
      const { mkdirSync, readFileSync, writeFileSync } = await import('fs');
      const { resolve, dirname, join } = await import('path');
      const chalkMod = await import('chalk');
      const chalk = chalkMod.default;
      const { AESpecCompiler } = await import('../../packages/spec-compiler/src/index.js');
      const { loadLLM } = await import('../providers/index.js');

      try {
        mkdirSync(artifactsDir, { recursive: true });
        mkdirSync(dirname(out), { recursive: true });
        const reqText = readFileSync(resolve(input), 'utf-8');
        const llm = await loadLLM();
        const compiler = new AESpecCompiler();

        let currentSpec = '';
        let lastIssues: string[] = [];

        for (let iter = 1; iter <= iterations; iter++) {
          console.log(chalk.blue(`\n🧠 Synthesizing AE-Spec (iteration ${iter}/${iterations}) using ${llm.name}...`));
          const system = 'You convert natural-language product requirements into AE-Spec markdown with sections: Glossary, Domain (with entities and typed fields), Invariants, Use Cases, API, UI Requirements, Non-Functional Requirements. Be concise and consistent.';
          const prompt = [
            'Natural-language requirements:\n\n',
            reqText,
            '\n\nConstraints:',
            '- Output valid AE-Spec markdown with the sections listed above.',
            '- Use field types from: string|number|boolean|date|uuid|email|url|json|array|object.',
            '- Domain entities must have at least 1 field; mark key fields as required.',
            '- API lines as bullet list: "- METHOD /path - summary".',
            lastIssues.length ? `\nKnown issues to fix from previous compile:\n- ${lastIssues.join('\n- ')}` : ''
          ].join('');

          const draft = await llm.complete({ system, prompt, temperature: 0.2 });
          currentSpec = draft;
          const iterPath = join(artifactsDir, `iter-${String(iter).padStart(2,'0')}.md`);
          writeFileSync(iterPath, currentSpec, 'utf-8');
          console.log(chalk.gray(`   Saved draft: ${iterPath}`));

          // Compile (lenient for intermediate)
          const prevRelaxed = process.env.AE_SPEC_RELAXED;
          process.env.AE_SPEC_RELAXED = '1';
          const ir = await compiler.compile({ inputPath: resolve(iterPath), validate: false });
          const lint = await compiler.lint(ir);
          lastIssues = lint.issues.slice(0, 10).map(i => `${i.message} [${i.location?.section||'root'}]`);
          console.log(chalk.blue(`   Lint summary: errors=${lint.summary.errors}, warnings=${lint.summary.warnings}`));
          process.env.AE_SPEC_RELAXED = prevRelaxed;

          // If no errors in lenient pass, attempt strict validation
          if (lint.summary.errors === 0 && lint.summary.warnings <= maxWarnings) {
            try {
              const strictIr = await compiler.compile({ inputPath: resolve(iterPath), validate: true });
              // Strict pass → finalize
              writeFileSync(resolve(out), currentSpec, 'utf-8');
              writeFileSync('.ae/ae-ir.json', JSON.stringify(strictIr, null, 2), 'utf-8');
              console.log(chalk.green(`\n✅ Strict validation passed. Wrote AE-Spec: ${out}`));
              console.log(chalk.green(`✅ Wrote AE-IR: .ae/ae-ir.json`));
              // Optional: run quick codegen
              await import('child_process').then(({ spawnSync }) => {
                const run = (args: string[]) => spawnSync(process.execPath, ['dist/src/cli/index.js', ...args], { stdio: 'inherit' });
                run(['codegen', 'generate', '-i', '.ae/ae-ir.json', '-o', 'generated/typescript', '-t', 'typescript']);
                run(['codegen', 'generate', '-i', '.ae/ae-ir.json', '-o', 'generated/api', '-t', 'api']);
                run(['codegen', 'generate', '-i', '.ae/ae-ir.json', '-o', 'generated/database', '-t', 'database']);
              });
              console.log(chalk.green('✅ Code generation completed (typescript/api/database).'));
              return;
            } catch (e) {
              console.log(chalk.yellow('Strict validation attempt failed; continuing iterations...'));
            }
          }
        }

        // If not converged, write last draft as output (lenient) for manual follow-up
        writeFileSync(resolve(out), currentSpec || '# Draft AE-Spec (empty)', 'utf-8');
        console.log(chalk.yellow(`\n⚠️  Did not converge within ${iterations} iterations. Last draft saved to: ${out}`));
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Synthesis failed: ${toMessage(error)}`));
        process.exit(1);
      }
    });

  return spec;
}

export default createSpecCommand;
