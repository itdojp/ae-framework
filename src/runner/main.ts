import { cac } from 'cac';
import { tddGuard } from '../commands/tdd/guard.js';
import { benchRun } from '../commands/bench/run.js';
import { qaRun } from '../commands/qa/run.js';
import { qaFlake } from '../commands/qa/flake.js';
import { verifyRun } from '../commands/verify/run.js';
import { agentComplete } from '../commands/agent/complete.js';
import { doctorEnv } from '../commands/doctor/env.js';

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
    .option('--pattern <glob>', 'Test pattern/directory filter (e.g., "unit" for unit tests)')
    .option('--timeoutMs <n>', 'Execution timeout per run in milliseconds', { default: 300000 })
    .option('--workers <n|percent>', 'Worker threads/processes (number or percentage like "50%")')
    .action(async (opts) => {
      const r = await qaFlake({
        times: Number(opts.times),
        pattern: opts.pattern,
        timeoutMs: Number(opts.timeoutMs),
        workers: opts.workers
      });
      process.exit(r.ok ? 0 : 1);
    });
  
  cli.command('verify', 'Run types/lint/qa/bench in one shot')
    .action(async () => {
      const r = await verifyRun();
      process.exit(r.ok ? 0 : 1);
    });
  
  cli.command('agent:complete', 'LLM completion with record/replay support')
    .option('--prompt <text>', 'Prompt text')
    .option('--system <text>', 'System message')
    .option('--record', 'Record mode')
    .option('--replay', 'Replay mode') 
    .option('--cassette-dir <dir>', 'Cassette directory')
    .action((opts) => agentComplete(opts.prompt, opts.system, opts));
  
  cli.command('doctor env', 'diagnose environment & LLM keys')
    .action(doctorEnv);
  
  cli.option('--seed <n>', 'Random seed (AE_SEED also supported)');
  
  cli.help();
  cli.parse();
}