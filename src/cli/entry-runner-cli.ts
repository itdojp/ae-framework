/**
 * Entry Runner CLI commands for the AE-Framework
 * Provides commands to route to consolidated runner entry points.
 */

import { Command } from 'commander';
import chalk from 'chalk';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { safeExit } from '../utils/safe-exit.js';

type RunnerKey = 'test' | 'quality' | 'verify' | 'flake' | 'security';

const RUNNER_MAP: Record<RunnerKey, string> = {
  test: 'scripts/test/run.mjs',
  quality: 'scripts/quality/run.mjs',
  verify: 'scripts/verify/run.mjs',
  flake: 'scripts/flake/run.mjs',
  security: 'scripts/security/run.mjs',
};

const normalizeCategory = (value: string): RunnerKey | null => {
  const key = value.trim().toLowerCase() as RunnerKey;
  return RUNNER_MAP[key] ? key : null;
};

export function createEntryRunnerCommand(): Command {
  const entry = new Command('entry');
  entry
    .description('Run consolidated runner entry points (test/quality/verify/flake/security)')
    .addHelpText(
      'after',
      `\nExamples:\n  $ ae entry test --profile fast\n  $ ae entry quality --list\n  $ ae entry verify --dry-run --profile lite\n`
    )
    .argument('<category>', 'Runner category (test, quality, verify, flake, security)')
    .option('-p, --profile <name>', 'Profile name to run')
    .option('--list', 'List available profiles')
    .option('--dry-run', 'Print resolved commands without executing')
    .option('--root <path>', 'Project root (default: cwd)', process.cwd())
    .action((category: string, options: { profile?: string; list?: boolean; dryRun?: boolean; root?: string }) => {
      const normalized = normalizeCategory(category);
      if (!normalized) {
        console.error(chalk.red(`❌ Unknown category: ${category}`));
        console.error(chalk.yellow('Available categories: test, quality, verify, flake, security'));
        safeExit(2);
        return;
      }

      const root = path.resolve(options.root || process.cwd());
      const runnerPath = path.join(root, RUNNER_MAP[normalized]);
      if (!fs.existsSync(runnerPath)) {
        console.error(chalk.red(`❌ Runner entry not found: ${runnerPath}`));
        safeExit(2);
        return;
      }

      const args: string[] = [runnerPath];
      if (options.profile) {
        args.push('--profile', options.profile);
      }
      if (options.list) {
        args.push('--list');
      }
      if (options.dryRun) {
        args.push('--dry-run');
      }

      if (!options.list && !options.dryRun) {
        console.log(chalk.blue(`▶ Running entry: ${normalized} (${runnerPath})`));
      }

      const result = spawnSync(process.execPath, args, {
        stdio: 'inherit',
        env: process.env,
        cwd: root,
      });

      if (result.error) {
        console.error(
          chalk.red(
            `❌ Failed to spawn runner: ${result.error.message ?? String(result.error)}`
          )
        );
        const errorCode = (result.error as NodeJS.ErrnoException).code;
        safeExit(errorCode === 'ENOENT' ? 127 : 1);
        return;
      }

      safeExit(result.status !== null ? result.status : 1);
    });

  return entry;
}
