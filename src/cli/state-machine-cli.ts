#!/usr/bin/env node

import { Command } from 'commander';
import { mkdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import chalk from 'chalk';
import { glob } from 'glob';
import { safeExit } from '../utils/safe-exit.js';
import { toMessage } from '../utils/error-utils.js';
import {
  type StateMachineIssue,
  type StateMachineSummary,
  validateStateMachineDefinition
} from '../state-machine/validator.js';
import { renderMermaidStateMachine } from '../state-machine/render.js';
import type { StateMachineDefinition } from '../state-machine/types.js';

function looksLikeGlob(value: string) {
  return /[*?\[\]{}()]/.test(value);
}

async function resolveFiles(inputs: string[]): Promise<string[]> {
  const files = new Set<string>();

  for (const input of inputs) {
    const resolved = path.resolve(input);
    try {
      const stats = statSync(resolved);
      if (stats.isDirectory()) {
        const matches = await glob('**/*.sm.json', { cwd: resolved, absolute: true, nodir: true });
        matches.forEach((match) => files.add(match));
        continue;
      }
      if (stats.isFile()) {
        files.add(resolved);
        continue;
      }
    } catch {
      if (looksLikeGlob(input)) {
        const matches = await glob(input, { absolute: true, nodir: true });
        matches.forEach((match) => files.add(match));
        continue;
      }
      throw new Error(`Path not found: ${input}`);
    }
  }

  return Array.from(files).sort();
}

function renderText(
  results: Array<{ file: string; ok: boolean; issues: StateMachineIssue[]; summary: StateMachineSummary }>
) {
  let hasErrors = false;
  for (const result of results) {
    if (result.ok) {
      console.log(chalk.green(`✅ ${result.file}`));
      continue;
    }
    hasErrors = true;
    console.log(chalk.red(`❌ ${result.file}`));
    for (const issue of result.issues) {
      const marker = issue.severity === 'error' ? chalk.red('error') : chalk.yellow('warn');
      const location = issue.location?.jsonPointer ? ` (${issue.location.jsonPointer})` : '';
      console.log(`  - [${marker}] ${issue.code}: ${issue.message}${location}`);
    }
  }
  if (hasErrors) {
    safeExit(1);
  }
}

function renderIssues(file: string, issues: StateMachineIssue[]) {
  console.log(chalk.red(`❌ ${file}`));
  for (const issue of issues) {
    const marker = issue.severity === 'error' ? chalk.red('error') : chalk.yellow('warn');
    const location = issue.location?.jsonPointer ? ` (${issue.location.jsonPointer})` : '';
    console.log(`  - [${marker}] ${issue.code}: ${issue.message}${location}`);
  }
}

function sanitizeOutputSegment(value: string) {
  const base = path.basename(value);
  const sanitized = base.replace(/[^A-Za-z0-9._-]/g, '-').replace(/-+/g, '-');
  const trimmed = sanitized.replace(/^[-.]+/, '').replace(/[-.]+$/, '');
  if (!trimmed || trimmed === '.' || trimmed === '..') {
    return '';
  }
  return trimmed;
}

function resolveOutputName(machine: StateMachineDefinition, file: string) {
  if (typeof machine.id === 'string' && machine.id.trim().length > 0) {
    const safeId = sanitizeOutputSegment(machine.id.trim());
    if (safeId) {
      return `${safeId}.mmd`;
    }
  }
  const base = path.basename(file).replace(/\\.sm\\.json$/i, '');
  const safeBase = sanitizeOutputSegment(base) || 'state-machine';
  return `${safeBase}.mmd`;
}

export function createStateMachineCommand(): Command {
  const sm = new Command('sm');
  sm.description('State machine validation commands');

  sm
    .command('validate')
    .description('Validate state machine specs (.sm.json)')
    .argument('<paths...>', 'Files, directories, or glob patterns')
    .option('--format <format>', 'Output format: text|json', 'text')
    .action(async (paths: string[], options: { format: string }) => {
      try {
        const files = await resolveFiles(paths);
        if (files.length === 0) {
          console.log(chalk.yellow('⚠️  No state machine files found'));
          safeExit(1);
          return;
        }

        const results = files.map((file) => {
          const raw = readFileSync(file, 'utf8');
          let data: unknown;
          try {
            data = JSON.parse(raw);
          } catch (error: unknown) {
            const issues: StateMachineIssue[] = [
              {
                code: 'PARSE_ERROR',
                severity: 'error',
                message: `Failed to parse JSON: ${toMessage(error)}`
              }
            ];
            return {
              file,
              ok: false,
              issues,
              summary: { states: 0, events: 0, transitions: 0 }
            };
          }

          const validation = validateStateMachineDefinition(data);
          return {
            file,
            ok: validation.ok,
            issues: validation.issues,
            summary: validation.summary
          };
        });

        if (options.format === 'json') {
          const payload = {
            ok: results.every((result) => result.ok),
            tool: { name: 'ae-framework', command: 'sm validate' },
            results
          };
          console.log(JSON.stringify(payload, null, 2));
          if (!payload.ok) {
            safeExit(1);
          }
          return;
        }

        renderText(results);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ State machine validation failed: ${toMessage(error)}`));
        safeExit(2);
      }
    });

  sm
    .command('render')
    .description('Render state machine specs to Mermaid diagrams (.mmd)')
    .argument('<paths...>', 'Files, directories, or glob patterns')
    .option('--format <format>', 'Output format: mermaid', 'mermaid')
    .option('--out <dir>', 'Output directory', 'docs/diagrams/state-machines')
    .option('--check', 'Fail if rendered output differs from existing files', false)
    .action(async (paths: string[], options: { format: string; out: string; check: boolean }) => {
      try {
        if (options.format !== 'mermaid') {
          console.error(chalk.red(`❌ Unsupported format: ${options.format}`));
          safeExit(3);
          return;
        }

        const files = await resolveFiles(paths);
        if (files.length === 0) {
          console.log(chalk.yellow('⚠️  No state machine files found'));
          safeExit(1);
          return;
        }

        const invalidResults: Array<{
          file: string;
          ok: boolean;
          issues: StateMachineIssue[];
          summary: StateMachineSummary;
        }> = [];
        const machines: Array<{ file: string; data: StateMachineDefinition }> = [];

        for (const file of files) {
          const raw = readFileSync(file, 'utf8');
          let data: unknown;
          try {
            data = JSON.parse(raw);
          } catch (error: unknown) {
            invalidResults.push({
              file,
              ok: false,
              issues: [
                {
                  code: 'PARSE_ERROR',
                  severity: 'error',
                  message: `Failed to parse JSON: ${toMessage(error)}`
                }
              ],
              summary: { states: 0, events: 0, transitions: 0 }
            });
            continue;
          }

          const validation = validateStateMachineDefinition(data);
          if (!validation.ok) {
            invalidResults.push({
              file,
              ok: false,
              issues: validation.issues,
              summary: validation.summary
            });
            continue;
          }

          machines.push({ file, data: data as StateMachineDefinition });
        }

        if (invalidResults.length > 0) {
          // renderText handles reporting validation errors and calling safeExit(1).
          renderText(invalidResults);
          return;
        }

        const outDir = path.resolve(options.out);
        if (!options.check) {
          mkdirSync(outDir, { recursive: true });
        }

        const renderIssuesList: Array<{ file: string; issues: StateMachineIssue[] }> = [];

        for (const machine of machines) {
          const outputName = resolveOutputName(machine.data, machine.file);
          const outputPath = path.join(outDir, outputName);
          const rendered = renderMermaidStateMachine(machine.data);

          if (options.check) {
            try {
              const existing = readFileSync(outputPath, 'utf8');
              if (existing !== rendered) {
                renderIssuesList.push({
                  file: machine.file,
                  issues: [
                    {
                      code: 'MERMAID_OUT_OF_DATE',
                      severity: 'error',
                      message: `Rendered output differs: ${outputPath}`
                    }
                  ]
                });
              }
            } catch {
              renderIssuesList.push({
                file: machine.file,
                issues: [
                  {
                    code: 'MERMAID_MISSING',
                    severity: 'error',
                    message: `Rendered output missing: ${outputPath}`
                  }
                ]
              });
            }
            continue;
          }

          writeFileSync(outputPath, rendered, 'utf8');
          console.log(chalk.green(`✅ ${outputPath}`));
        }

        if (renderIssuesList.length > 0) {
          for (const item of renderIssuesList) {
            renderIssues(item.file, item.issues);
          }
          safeExit(1);
        }
        safeExit(0);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ State machine rendering failed: ${toMessage(error)}`));
        safeExit(2);
      }
    });

  return sm;
}
