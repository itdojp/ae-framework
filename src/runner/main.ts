import { cac } from 'cac';
import { tddGuard } from '../commands/tdd/guard.js';
import { benchRun } from '../commands/bench/run.js';
import { qaRun } from '../commands/qa/run.js';
import { qaFlake } from '../commands/qa/flake.js';
import { verifyRun } from '../commands/verify/run.js';

export async function main() {
  const cli = cac('ae');
  
  cli.command('tdd:guard', 'Run TDD pre-commit guard')
    .action(tddGuard);
  
  cli.command('bench', 'Run benchmarks')
    .action(benchRun);
  
  cli.command('qa', 'Run QA metrics')
    .action(qaRun);
  
  cli.command('qa:flake', 'Run tests multiple times to detect flakiness')
    .option('--times <n>', 'Repeat count', { default: 10 })
    .action((opts) => qaFlake(Number(opts.times)));
  
  cli.command('verify', 'Run types/lint/qa/bench in one shot')
    .action(verifyRun);
  
  cli.option('--seed <n>', 'Random seed (AE_SEED also supported)');
  
  cli.help();
  cli.parse();
}