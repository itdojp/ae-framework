#!/usr/bin/env node
import { spawn } from 'node:child_process';
import path from 'node:path';

const repoRoot = process.cwd();

function parseArgs(argv) {
  const options = {
    input: null,
    format: 'auto',
    outputDir: path.join('hermetic-reports', 'trace'),
    replay: true,
    dryRun: false,
  };
  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--input' || arg === '-i') && next) {
      options.input = next;
      i += 1;
    } else if ((arg === '--output-dir' || arg === '-o') && next) {
      options.outputDir = next;
      i += 1;
    } else if ((arg === '--format' || arg === '-f') && next) {
      options.format = next;
      i += 1;
    } else if (arg === '--skip-replay') {
      options.replay = false;
    } else if (arg === '--dry-run') {
      options.dryRun = true;
    } else if (arg === '--help' || arg === '-h') {
      options.help = true;
    }
  }
  return options;
}

function printHelp() {
  console.log(`Usage: pnpm pipelines:trace [options]\n\nOptions:\n  -i, --input <file>        Trace file (NDJSON or OTLP JSON). Default: samples/trace/kvonce-sample.ndjson\n  -o, --output-dir <dir>    Output directory for artifacts (default: hermetic-reports/trace)\n  -f, --format <fmt>        Trace format (ndjson|otlp|auto). Default: auto\n      --skip-replay         Skip TLC replay step\n      --dry-run             Print the command without executing\n      --help                Show this message\n`);
}

const opts = parseArgs(process.argv);
if (opts.help) {
  printHelp();
  process.exit(0);
}

const command = ['pnpm', 'verify:conformance'];
const inputPath = opts.input || path.join('samples', 'trace', 'kvonce-sample.ndjson');
command.push('--trace', inputPath);
if (opts.format) {
  command.push('--trace-format', opts.format);
}
if (opts.outputDir) {
  command.push('--trace-output', opts.outputDir);
}
if (!opts.replay) {
  command.push('--trace-skip-replay');
}

if (opts.dryRun) {
  console.log('[trace] dry-run:', command.join(' '));
  process.exit(0);
}

const child = spawn(command[0], command.slice(1), {
  cwd: repoRoot,
  stdio: 'inherit',
  env: process.env,
});

child.on('close', (code) => {
  process.exit(code ?? 1);
});
