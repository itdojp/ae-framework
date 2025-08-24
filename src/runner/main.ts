import { cac } from 'cac';
import { tddGuard } from '../commands/tdd/guard.js';
import { benchRun } from '../commands/bench/run.js';
import { qaRun } from '../commands/qa/run.js';

export async function main() {
  const cli = cac('ae');
  
  cli.command('tdd:guard', 'Run TDD pre-commit guard')
    .action(tddGuard);
  
  cli.command('bench', 'Run benchmarks')
    .action(benchRun);
  
  cli.command('qa', 'Run QA metrics')
    .action(qaRun);
  
  cli.option('--seed <n>', 'Random seed (AE_SEED also supported)');
  
  cli.help();
  cli.parse();
}