#!/usr/bin/env node

/**
 * AE-Framework Spec CLI Integration
 * Integrates spec-compiler into main ae-framework CLI
 */

import { Command } from 'commander';
import { AESpecCompiler } from '../../packages/spec-compiler/src/index.js';
import { dirname, resolve } from 'path';
import { mkdirSync, readFileSync, writeFileSync } from 'fs';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import { exportKiroSpec } from './spec-exporter.js';
import type { SpecLintIssue, SpecLintReport } from '../../packages/spec-compiler/src/types.js';

type SpecOutputFormat = 'text' | 'json';
type SpecIssueSeverity = 'error' | 'warning' | 'info';

interface SpecCommandReportIssue {
  ruleId: string;
  severity: SpecIssueSeverity;
  message: string;
  category?: string;
  location?: SpecLintIssue['location'];
  suggestion?: string;
}

interface SpecCommandReport {
  command: 'lint' | 'validate';
  status: 'pass' | 'fail';
  summary: {
    errors: number;
    warnings: number;
    info: number;
  };
  issues: SpecCommandReportIssue[];
  input: string;
  aeIrOutput?: string;
  thresholds: {
    maxErrors: number;
    maxWarnings: number;
  };
  generatedAt: string;
}

interface SpecCommandErrorPayload {
  error: true;
  code: 'SPEC_INVALID_INPUT' | 'SPEC_INTERNAL_ERROR';
  message: string;
  details: {
    command: 'lint' | 'validate';
    input?: string;
  };
  ts: string;
  command: 'lint' | 'validate';
}

const normalizeSpecOutputFormat = (rawFormat: string | undefined): SpecOutputFormat => {
  const normalized = (rawFormat ?? 'text').toLowerCase();
  if (normalized === 'text' || normalized === 'json') {
    return normalized;
  }
  throw new Error(`Unsupported --format: ${rawFormat}. Expected one of: text, json`);
};

const detectFormatHint = (rawFormat: string | undefined): SpecOutputFormat => {
  const normalized = (rawFormat ?? 'text').toLowerCase();
  return normalized === 'json' ? 'json' : 'text';
};

const isSpecInvalidInputError = (error: unknown): boolean => {
  const message = toMessage(error).toLowerCase();
  return message.includes('unsupported --format')
    || message.includes('enoent')
    || message.includes('no such file')
    || message.includes('eisdir')
    || message.includes('unexpected token');
};

const emitSpecCommandError = (params: {
  command: 'lint' | 'validate';
  format: SpecOutputFormat;
  input?: string;
  error: unknown;
}): void => {
  const message = toMessage(params.error);
  const invalidInput = isSpecInvalidInputError(params.error);
  const exitCode = invalidInput ? 2 : 1;

  if (params.format === 'json') {
    const details: { command: 'lint' | 'validate'; input?: string } = {
      command: params.command,
      ...(params.input !== undefined ? { input: params.input } : {}),
    };
    const payload: SpecCommandErrorPayload = {
      error: true,
      code: invalidInput ? 'SPEC_INVALID_INPUT' : 'SPEC_INTERNAL_ERROR',
      message,
      details,
      ts: new Date().toISOString(),
      command: params.command,
    };
    console.log(JSON.stringify(payload, null, 2));
  } else {
    const label = params.command === 'lint' ? 'Linting failed' : 'Validation failed';
    console.error(chalk.red(`❌ ${label}: ${message}`));
  }

  safeExit(exitCode);
};

const normalizeIssueSeverity = (severity: SpecLintIssue['severity']): SpecIssueSeverity => {
  if (severity === 'warn') {
    return 'warning';
  }
  return severity;
};

const detectIssueCategory = (issue: SpecLintIssue): string | undefined => {
  if (issue.location?.section) {
    return issue.location.section.toLowerCase();
  }
  const prefix = issue.id.match(/^([A-Z]+)/)?.[1];
  if (!prefix) {
    return undefined;
  }
  const categoryMap: Record<string, string> = {
    STRUCT: 'structure',
    BIZ: 'business',
    CONS: 'consistency',
    COMP: 'completeness',
    SCHEMA: 'schema',
    PARSE: 'parse',
    COMPILER: 'compiler',
  };
  return categoryMap[prefix];
};

const createSpecCommandReport = (params: {
  command: 'lint' | 'validate';
  lintResult: SpecLintReport;
  failed: boolean;
  input: string;
  maxErrors: number;
  maxWarnings: number;
  aeIrOutput?: string;
}): SpecCommandReport => {
  const {
    command,
    lintResult,
    failed,
    input,
    maxErrors,
    maxWarnings,
    aeIrOutput,
  } = params;

  const report: SpecCommandReport = {
    command,
    status: failed ? 'fail' : 'pass',
    summary: {
      errors: lintResult.summary.errors,
      warnings: lintResult.summary.warnings,
      info: lintResult.summary.infos,
    },
    issues: lintResult.issues.map((issue) => {
      const normalizedIssue: SpecCommandReportIssue = {
        ruleId: issue.id,
        severity: normalizeIssueSeverity(issue.severity),
        message: issue.message,
      };
      const category = detectIssueCategory(issue);
      if (category !== undefined) {
        normalizedIssue.category = category;
      }
      if (issue.location !== undefined) {
        normalizedIssue.location = issue.location;
      }
      if (issue.suggestion !== undefined) {
        normalizedIssue.suggestion = issue.suggestion;
      }
      return normalizedIssue;
    }),
    input,
    thresholds: {
      maxErrors,
      maxWarnings,
    },
    generatedAt: new Date().toISOString(),
  };
  if (aeIrOutput !== undefined) {
    report.aeIrOutput = aeIrOutput;
  }
  return report;
};

const writeCommandOutput = (outputPath: string, content: string): void => {
  mkdirSync(dirname(outputPath), { recursive: true });
  writeFileSync(outputPath, content, 'utf8');
};

const formatIssueIcon = (severity: SpecLintIssue['severity']) => {
  if (severity === 'error') {
    return chalk.red('❌');
  }
  if (severity === 'warn') {
    return chalk.yellow('⚠️ ');
  }
  return chalk.blue('ℹ️ ');
};

const renderSpecCommandReportText = (report: SpecCommandReport, maxIssues: number): string => {
  const lines: string[] = [];
  lines.push(`# ${report.command} report`);
  lines.push(`status: ${report.status}`);
  lines.push(`input: ${report.input}`);
  if (report.aeIrOutput) {
    lines.push(`aeIrOutput: ${report.aeIrOutput}`);
  }
  lines.push(`generatedAt: ${report.generatedAt}`);
  lines.push(
    `summary: errors=${report.summary.errors}, warnings=${report.summary.warnings}, info=${report.summary.info}`
  );
  lines.push(
    `thresholds: maxErrors=${report.thresholds.maxErrors}, maxWarnings=${report.thresholds.maxWarnings}`
  );
  lines.push('');
  lines.push('issues:');
  if (report.issues.length === 0) {
    lines.push('  - none');
    return lines.join('\n');
  }
  report.issues.slice(0, maxIssues).forEach((issue) => {
    const category = issue.category ? ` [${issue.category}]` : '';
    lines.push(`  - (${issue.severity}) ${issue.ruleId}: ${issue.message}${category}`);
  });
  if (report.issues.length > maxIssues) {
    lines.push(`  - ... and ${report.issues.length - maxIssues} more issues`);
  }
  return lines.join('\n');
};

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
        console.log(chalk.gray(`   APIs: ${ir.api?.length ?? 0}`));
        console.log(chalk.gray(`   Use Cases: ${ir.usecases?.length ?? 0}`));
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Compilation failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  spec
    .command('lint')
    .description('Lint AE-IR for quality issues')
    .option('-i, --input <file>', 'Input AE-IR JSON file', '.ae/ae-ir.json')
    .option('--max-errors <n>', 'Maximum allowed errors', parseInt, 0)
    .option('--max-warnings <n>', 'Maximum allowed warnings', parseInt, 10)
    .option('--format <format>', 'Output format (text|json)', 'text')
    .option('--output <file>', 'Write lint report to file')
    .action(async (options) => {
      const formatHint = detectFormatHint(options.format);
      const inputPath = options.input || '.ae/ae-ir.json';
      try {
        const format = normalizeSpecOutputFormat(options.format);
        const printText = format === 'text';
        if (printText) {
          console.log(chalk.blue(`🔍 Linting ${inputPath}...`));
        }
        
        const irContent = readFileSync(resolve(inputPath), 'utf-8');
        const ir = JSON.parse(irContent);
        
        const compiler = new AESpecCompiler();
        const result = await compiler.lint(ir);

        const failed = 
          result.summary.errors > options.maxErrors ||
          result.summary.warnings > options.maxWarnings;

        const report = createSpecCommandReport({
          command: 'lint',
          lintResult: result,
          failed,
          input: inputPath,
          maxErrors: options.maxErrors,
          maxWarnings: options.maxWarnings,
        });

        if (format === 'json') {
          const payload = JSON.stringify(report, null, 2);
          if (options.output) {
            writeCommandOutput(resolve(options.output), payload);
          }
          console.log(payload);
        } else {
          console.log(chalk.blue('\n📊 Lint Results:'));
          console.log(`   ${result.summary.errors > 0 ? chalk.red('❌') : chalk.green('✅')} Errors: ${result.summary.errors}`);
          console.log(`   ${result.summary.warnings > 0 ? chalk.yellow('⚠️ ') : chalk.green('✅')} Warnings: ${result.summary.warnings}`);
          console.log(`   ${chalk.blue('ℹ️ ')} Info: ${result.summary.infos}`);

          if (result.issues.length > 0) {
            console.log('\n📋 Issues:');
            for (const issue of result.issues.slice(0, 10)) {
              const location = issue.location?.section ?
                chalk.gray(` [${issue.location.section}]`) : '';

              console.log(`${formatIssueIcon(issue.severity)} ${chalk.bold(issue.id)}: ${issue.message}${location}`);
              if (issue.suggestion) {
                console.log(chalk.gray(`   💡 ${issue.suggestion}`));
              }
            }

            if (result.issues.length > 10) {
              console.log(chalk.gray(`\n   ... and ${result.issues.length - 10} more issues`));
            }
          }

          if (options.output) {
            writeCommandOutput(resolve(options.output), renderSpecCommandReportText(report, 10));
          }

          if (failed) {
            console.log(chalk.red('\n❌ Quality thresholds exceeded'));
          } else {
            console.log(chalk.green('\n✅ All quality checks passed'));
          }
        }

        if (failed) {
          safeExit(1);
        }
        
      } catch (error: unknown) {
        emitSpecCommandError({
          command: 'lint',
          format: formatHint,
          input: inputPath,
          error,
        });
      }
    });

  spec
    .command('validate')
    .description('Validate AE-Spec file (compile + lint)')
    .requiredOption('-i, --input <file>', 'Input markdown file')
    .option('--output <file>', 'Output JSON file (default: .ae/ae-ir.json)')
    .option('--report-output <file>', 'Output validation report file (default: stdout only)')
    .option('--format <format>', 'Validation report format (text|json)', 'text')
    .option('--max-errors <n>', 'Maximum allowed errors', parseInt, 0)
    .option('--max-warnings <n>', 'Maximum allowed warnings', parseInt, 10)
    .option('--relaxed', 'Relax strict schema errors to warnings')
    .option('--desc-max <n>', 'Override description max length (e.g., 1000)', parseInt)
    .action(async (options) => {
      const formatHint = detectFormatHint(options.format);
      try {
        const format = normalizeSpecOutputFormat(options.format);
        const printText = format === 'text';
        if (printText) {
          console.log(chalk.blue(`🔍 Validating ${options.input}...`));
        }
        
        const compiler = new AESpecCompiler();
        const outputPath = options.output || '.ae/ae-ir.json';
        // Set relaxed/configurable limits via env for spec-compiler
        if (options.relaxed) process.env['AE_SPEC_RELAXED'] = '1';
        if (typeof options.descMax === 'number' && Number.isFinite(options.descMax) && options.descMax > 0) {
          process.env['AE_SPEC_DESC_MAX'] = String(options.descMax);
          process.env['AE_SPEC_INVARIANT_DESC_MAX'] = String(options.descMax);
          process.env['AE_SPEC_DOMAIN_DESC_MAX'] = String(options.descMax);
          process.env['AE_SPEC_FIELD_DESC_MAX'] = String(options.descMax);
        }
        
        // Compile
        if (printText) {
          console.log(chalk.blue('📝 Compiling...'));
        }
        const ir = await compiler.compile({
          inputPath: resolve(options.input),
          outputPath: resolve(outputPath),
          validate: false, // We'll lint separately
        });
        
        if (printText) {
          console.log(chalk.green('✅ Compilation successful'));
        }
        
        // Lint
        if (printText) {
          console.log(chalk.blue('🔍 Linting...'));
        }
        const lintResult = await compiler.lint(ir);

        const failed = 
          lintResult.summary.errors > options.maxErrors ||
          lintResult.summary.warnings > options.maxWarnings;

        const report = createSpecCommandReport({
          command: 'validate',
          lintResult,
          failed,
          input: options.input,
          aeIrOutput: outputPath,
          maxErrors: options.maxErrors,
          maxWarnings: options.maxWarnings,
        });

        if (format === 'json') {
          const payload = JSON.stringify(report, null, 2);
          if (options.reportOutput) {
            writeCommandOutput(resolve(options.reportOutput), payload);
          }
          console.log(payload);
        } else {
          console.log(chalk.blue('\n📊 Validation Results:'));
          console.log(`   ${lintResult.summary.errors > 0 ? chalk.red('❌') : chalk.green('✅')} Errors: ${lintResult.summary.errors}`);
          console.log(`   ${lintResult.summary.warnings > 0 ? chalk.yellow('⚠️ ') : chalk.green('✅')} Warnings: ${lintResult.summary.warnings}`);
          console.log(`   ${chalk.blue('ℹ️ ')} Info: ${lintResult.summary.infos}`);

          if (lintResult.issues.length > 0) {
            console.log('\n📋 Top Issues:');
            for (const issue of lintResult.issues.slice(0, 5)) {
              console.log(`${formatIssueIcon(issue.severity)} ${issue.message}`);
            }

            if (lintResult.issues.length > 5) {
              console.log(chalk.gray(`\n   ... and ${lintResult.issues.length - 5} more issues`));
            }
          }

          if (options.reportOutput) {
            writeCommandOutput(resolve(options.reportOutput), renderSpecCommandReportText(report, 5));
          }

          if (failed) {
            console.log(chalk.red('\n❌ Validation failed - quality thresholds exceeded'));
            console.log(chalk.red(`   Max errors allowed: ${options.maxErrors}, found: ${lintResult.summary.errors}`));
            console.log(chalk.red(`   Max warnings allowed: ${options.maxWarnings}, found: ${lintResult.summary.warnings}`));
          } else {
            console.log(chalk.green('\n✅ Validation passed successfully'));
            console.log(chalk.gray(`   AE-IR saved to: ${outputPath}`));
          }
        }

        if (failed) {
          safeExit(1);
        }
        
      } catch (error: unknown) {
        emitSpecCommandError({
          command: 'validate',
          format: formatHint,
          input: options.input,
          error,
        });
      }
    });

  spec
    .command('export')
    .description('Export AE-IR to external spec formats (default: kiro)')
    .option('-i, --input <file>', 'Input AE-IR JSON file', '.ae/ae-ir.json')
    .option('-f, --format <format>', 'Export format', 'kiro')
    .option('-o, --out <dir>', 'Output directory (default: .kiro/specs/<spec-id>/)')
    .option('--spec-id <id>', 'Spec identifier override')
    .action(async (options) => {
      try {
        const result = exportKiroSpec({
          inputPath: resolve(options.input),
          format: options.format,
          outputDir: options.out ? resolve(options.out) : options.out,
          specId: options.specId,
        });
        console.log(chalk.green('✅ Spec export completed'));
        console.log(chalk.gray(`   Format: ${options.format}`));
        console.log(chalk.gray(`   Spec ID: ${result.specId}`));
        console.log(chalk.gray(`   Output: ${result.outputDir}`));
        console.log(chalk.gray(`   Files: ${result.files.join(', ')}`));
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Spec export failed: ${toMessage(error)}`));
        safeExit(1);
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
        const prevRelaxed = process.env['AE_SPEC_RELAXED'];
        process.env['AE_SPEC_RELAXED'] = '1';
          const ir = await compiler.compile({ inputPath: resolve(iterPath), validate: false });
          const lint = await compiler.lint(ir);
          lastIssues = lint.issues.slice(0, 10).map(i => `${i.message} [${i.location?.section||'root'}]`);
          console.log(chalk.blue(`   Lint summary: errors=${lint.summary.errors}, warnings=${lint.summary.warnings}`));
        process.env['AE_SPEC_RELAXED'] = prevRelaxed as any;

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
