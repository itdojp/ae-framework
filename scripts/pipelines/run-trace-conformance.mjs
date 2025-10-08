#!/usr/bin/env node
import fs from 'node:fs';
import { spawn, spawnSync } from 'node:child_process';
import path from 'node:path';

const repoRoot = process.cwd();

function parseArgs(argv) {
  const options = {
    input: null,
    format: 'auto',
    outputDir: path.join('hermetic-reports', 'trace'),
    summaryOut: null,
    envelope: true,
    envelopeOut: path.join('artifacts', 'trace', 'report-envelope.json'),
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
    } else if ((arg === '--summary-out' || arg === '--summary') && next) {
      options.summaryOut = next;
      i += 1;
    } else if (arg === '--envelope-out' && next) {
      options.envelopeOut = next;
      i += 1;
    } else if (arg === '--no-envelope') {
      options.envelope = false;
    } else if (arg === '--dry-run') {
      options.dryRun = true;
    } else if (arg === '--help' || arg === '-h') {
      options.help = true;
    }
  }
  return options;
}

function printHelp() {
  const helpLines = [
    'Usage: pnpm pipelines:trace [options]',
    '',
    'Options:',
    '  -i, --input <file>        Trace file (NDJSON or OTLP JSON). Default: samples/trace/kvonce-sample.ndjson',
    '  -o, --output-dir <dir>    Output directory for artifacts (default: hermetic-reports/trace)',
    '  -f, --format <fmt>        Trace format (ndjson|otlp|auto). Default: auto',
    '      --summary-out <file>  Conformance summary JSON path (default: <output-dir>/kvonce-conformance-summary.json)',
    '      --envelope-out <file> Report envelope output path (default: artifacts/trace/report-envelope.json)',
    '      --no-envelope         Skip creating a report envelope',
    '      --skip-replay         Skip TLC replay step',
    '      --dry-run             Print the command without executing',
    '      --help                Show this message',
  ];
  console.log(helpLines.join('\n'));
}

const opts = parseArgs(process.argv);
if (opts.help) {
  printHelp();
  process.exit(0);
}

const traceOutputDir = path.resolve(repoRoot, opts.outputDir);
const summaryOutPath = path.resolve(repoRoot, opts.summaryOut ?? path.join(opts.outputDir, 'kvonce-conformance-summary.json'));
const summaryOutArg = path.relative(repoRoot, summaryOutPath);
const traceOutputArg = path.relative(repoRoot, traceOutputDir);
const envelopeOutPath = path.resolve(repoRoot, opts.envelopeOut);

const command = ['pnpm', 'verify:conformance'];
const inputPath = opts.input || path.join('samples', 'trace', 'kvonce-sample.ndjson');
command.push('--trace', inputPath);
if (opts.format) {
  command.push('--trace-format', opts.format);
}
command.push('--trace-output', traceOutputArg);
command.push('--out', summaryOutArg);
if (!opts.replay) {
  command.push('--trace-skip-replay');
}

if (opts.dryRun) {
  console.log('[trace] dry-run:', command.join(' '));
  console.log(`[trace] summary -> ${summaryOutArg}`);
  if (opts.envelope) {
    console.log(`[trace] envelope -> ${path.relative(repoRoot, envelopeOutPath)}`);
  }
  process.exit(0);
}

const child = spawn(command[0], command.slice(1), {
  cwd: repoRoot,
  stdio: 'inherit',
  env: process.env,
});

child.on('close', (code) => {
  const exitCode = code ?? 1;
  if (opts.envelope) {
    try {
      if (!fs.existsSync(summaryOutPath)) {
        console.warn(`[pipelines:trace] summary not found at ${summaryOutArg}; skipping envelope creation`);
      } else {
        const summary = JSON.parse(fs.readFileSync(summaryOutPath, 'utf8'));
        const artifacts = new Set();
        const pushArtifact = (maybePath) => {
          if (!maybePath || typeof maybePath !== 'string') return;
          const resolved = path.resolve(repoRoot, maybePath);
          if (fs.existsSync(resolved)) {
            artifacts.add(path.relative(repoRoot, resolved));
          }
        };

        if (summary.trace) {
          pushArtifact(summary.trace.ndjson);
          pushArtifact(summary.trace.projection?.path);
          pushArtifact(summary.trace.projection?.stateSequence);
          pushArtifact(summary.trace.validation?.path);
          pushArtifact(summary.trace.replay?.summaryPath);
        }

        const env = {
          ...process.env,
          REPORT_ENVELOPE_SUMMARY: summaryOutPath,
          REPORT_ENVELOPE_OUTPUT: envelopeOutPath,
          REPORT_ENVELOPE_SOURCE: 'pipelines:trace',
        };
        if (artifacts.size > 0) {
          env.REPORT_ENVELOPE_EXTRA_ARTIFACTS = Array.from(artifacts).join(',');
        }

        const envelopeResult = spawnSync(process.execPath, [path.join('scripts', 'trace', 'create-report-envelope.mjs')], {
          cwd: repoRoot,
          env,
          stdio: 'inherit',
        });
        if (envelopeResult.status !== 0) {
          console.error('[pipelines:trace] failed to create report envelope');
        }
      }
    } catch (error) {
      console.error('[pipelines:trace] envelope creation failed:', error);
    }
  }

  process.exit(exitCode);
});
