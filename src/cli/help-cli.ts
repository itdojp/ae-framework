/**
 * Help CLI commands for the AE-Framework
 * Provides parity with `pnpm run help` output.
 */

import { Command } from 'commander';
import chalk from 'chalk';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { safeExit } from '../utils/safe-exit.js';

export function createHelpCommand(): Command {
  const help = new Command('help');
  help
    .description('Show script groups and consolidated runners')
    .option('--root <path>', 'Project root (default: cwd)', process.cwd())
    .action((options: { root?: string }) => {
      const root = path.resolve(options.root || process.cwd());
      const scriptPath = path.join(root, 'scripts', 'project', 'help.mjs');

      if (!fs.existsSync(scriptPath)) {
        console.error(chalk.red(`❌ Help script not found: ${scriptPath}`));
        safeExit(2);
        return;
      }

      const result = spawnSync(process.execPath, [scriptPath], {
        stdio: 'inherit',
        env: process.env,
        cwd: root,
      });

      if (result.error) {
        console.error(
          chalk.red(
            `❌ Failed to run help script: ${result.error.message ?? String(result.error)}`
          )
        );
        const errorCode = (result.error as NodeJS.ErrnoException).code;
        safeExit(errorCode === 'ENOENT' ? 127 : 1);
        return;
      }

      safeExit(result.status !== null ? result.status : 1);
    });

  return help;
}
