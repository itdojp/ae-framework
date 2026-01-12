#!/usr/bin/env node

import { Command } from 'commander';
import { readFileSync, statSync } from 'node:fs';
import path from 'node:path';
import chalk from 'chalk';
import { glob } from 'glob';
import { safeExit } from '../utils/safe-exit.js';
import { toMessage } from '../utils/error-utils.js';
import { validateStateMachineDefinition } from '../state-machine/validator.js';

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

function renderText(results: Array<{ file: string; ok: boolean; issues: any[] }>) {
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
          const data = JSON.parse(raw);
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

  return sm;
}
