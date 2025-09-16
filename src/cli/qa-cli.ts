import { Command } from 'commander';
import { execa } from 'execa';
import chalk from 'chalk';
import { safeExit } from '../utils/safe-exit.js';

export function createQaCommand(): Command {
  const cmd = new Command('qa');
  cmd
    .description('Run QA checks (light mode maps to test:fast)')
    .option('--light', 'Run lightweight QA (maps to vitest test:fast)')
    .option('--verbose', 'Verbose output')
    .action(async (options) => {
      try {
        if (options.light) {
          const args = process.env['CI'] ? ['--reporter=dot'] : [];
          console.log(chalk.cyan('🧪 Running QA (light): vitest test:fast'));
          const { exitCode } = await execa('pnpm', ['run', 'test:fast', ...args], { stdio: 'inherit' });
          safeExit(exitCode ?? 0);
          return;
        }

        console.log(chalk.cyan('🔍 Running full quality gates'));
        const { exitCode } = await execa('node', ['dist/src/cli/index.js', 'quality', 'run', '--sequential'], { stdio: 'inherit' });
        safeExit(exitCode ?? 0);
      } catch (err) {
        console.error(chalk.red('❌ QA execution failed'));
        safeExit(1);
      }
    });

  return cmd;
}

export default createQaCommand;
