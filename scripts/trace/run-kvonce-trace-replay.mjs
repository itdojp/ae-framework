#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { appendSection } from '../ci/step-summary.mjs';

function parseArgs(argv) {
  const options = {
    input: 'samples/trace/kvonce-sample.ndjson',
    outputDir: path.join('hermetic-reports', 'trace', 'replay'),
    format: 'auto',
  };
  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    const next = argv[i + 1];
    if ((current === '--input' || current === '-i') && next) {
      options.input = next;
      i += 1;
    } else if ((current === '--output-dir' || current === '-o') && next) {
      options.outputDir = next;
      i += 1;
    } else if ((current === '--format' || current === '-f') && next) {
      options.format = next;
      i += 1;
    } else if (current === '--help' || current === '-h') {
      options.help = true;
    }
  }
  return options;
}

function printHelp() {
  console.log(`Usage: node scripts/trace/run-kvonce-trace-replay.mjs [--input <file>] [--format ndjson|otlp] [--output-dir <dir>] [--help|-h]`);
  console.log('Runs KvOnce trace validation and attempts TLC replay (if tooling is available).');
  console.log('  --help, -h        Show this help message and exit.');
}

function run(cmd, args, options = {}) {
  const result = spawnSync(cmd, args, {
    stdio: 'pipe',
    encoding: 'utf8',
    env: { ...process.env, ...options.env },
    cwd: options.cwd ?? process.cwd(),
  });
  return {
    command: `${cmd} ${args.join(' ')}`,
    status: result.status,
    stdout: result.stdout ?? '',
    stderr: result.stderr ?? '',
  };
}

const opts = parseArgs(process.argv);
if (opts.help) {
  printHelp();
  process.exit(0);
}

const OUTPUT_TRUNCATE_LIMIT = Number(process.env.TRACE_REPLAY_OUTPUT_TRUNCATE ?? 2000);

const repoRoot = process.cwd();
const resolvedInput = path.resolve(repoRoot, opts.input);
const outputDir = path.resolve(repoRoot, opts.outputDir);
const conformanceDir = path.join(outputDir, 'conformance');
fs.mkdirSync(outputDir, { recursive: true });
fs.mkdirSync(conformanceDir, { recursive: true });

function inferFormat(file, requested) {
  if (requested && requested !== 'auto') {
    return requested;
  }
  if (file.endsWith('.ndjson')) return 'ndjson';
  return 'otlp';
}

const summary = {
  input: path.relative(repoRoot, resolvedInput),
  format: inferFormat(opts.input, opts.format),
  conformance: {
    status: 'not_run',
  },
  tlc: {
    status: 'not_run',
  },
  timestamp: new Date().toISOString(),
};

if (!fs.existsSync(resolvedInput)) {
  summary.conformance.status = 'missing_input';
} else {
  const conformanceArgs = [
    'scripts/trace/run-kvonce-conformance.sh',
    '--input',
    resolvedInput,
    '--output-dir',
    conformanceDir,
    '--format',
    summary.format,
  ];
  const confResult = run('bash', conformanceArgs);
  summary.conformance.status = confResult.status === 0 ? 'ran' : 'failed';
  summary.conformance.exitCode = confResult.status;
  summary.conformance.stdout = confResult.stdout.slice(0, OUTPUT_TRUNCATE_LIMIT);
  summary.conformance.stderr = confResult.stderr.slice(0, OUTPUT_TRUNCATE_LIMIT);

  const validationPath = path.join(conformanceDir, 'kvonce-validation.json');
  if (fs.existsSync(validationPath)) {
    try {
      const validation = JSON.parse(fs.readFileSync(validationPath, 'utf8'));
      summary.conformance.report = {
        valid: Boolean(validation.valid),
        issues: Array.isArray(validation.issues) ? validation.issues.length : 0,
      };
    } catch (error) {
      summary.conformance.reportError = error.message;
    }
  }

  const tlcResult = run('pnpm', ['run', 'spec:kv-once:tlc']);
  summary.tlc.exitCode = tlcResult.status;
  summary.tlc.stdout = tlcResult.stdout.slice(0, OUTPUT_TRUNCATE_LIMIT);
  summary.tlc.stderr = tlcResult.stderr.slice(0, OUTPUT_TRUNCATE_LIMIT);
  summary.tlc.status = tlcResult.status === 0 ? 'ran' : 'failed';

  const tlaSummaryPath = path.join(repoRoot, 'hermetic-reports', 'formal', 'tla-summary.json');
  if (fs.existsSync(tlaSummaryPath)) {
    try {
      const tlaSummary = JSON.parse(fs.readFileSync(tlaSummaryPath, 'utf8'));
      summary.tlc.summary = {
        status: tlaSummary.status,
        ran: tlaSummary.ran,
        engine: tlaSummary.engine,
      };
      const replayCopy = path.join(outputDir, 'tla-summary.json');
      fs.copyFileSync(tlaSummaryPath, replayCopy);
    } catch (error) {
      summary.tlc.summaryError = error.message;
    }
  }
}

const summaryPath = path.join(outputDir, 'kvonce-trace-replay.json');
fs.writeFileSync(summaryPath, JSON.stringify(summary, null, 2));
console.log(`KvOnce trace replay summary: ${path.relative(repoRoot, summaryPath)}`);

const summaryLines = [
  `- input: ${summary.input}`,
  `- conformance: ${summary.conformance.status}`,
];
if (summary.conformance.report) {
  summaryLines.push(`  - valid: ${summary.conformance.report.valid} (issues: ${summary.conformance.report.issues})`);
}
if (summary.tlc.summary) {
  summaryLines.push(`- TLC status: ${summary.tlc.summary.status} (engine=${summary.tlc.summary.engine})`);
} else {
  summaryLines.push(`- TLC status: ${summary.tlc.status}`);
}
appendSection('KvOnce Trace Replay', summaryLines);

if (summary.conformance.status === 'failed') {
  process.exitCode = 1;
}
