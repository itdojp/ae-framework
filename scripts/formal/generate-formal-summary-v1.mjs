#!/usr/bin/env node
/**
 * Generate Formal Summary v1 (formal-summary/v1) from downloaded formal artifacts.
 *
 * Intended usage:
 * - CI formal-aggregate workflow: download artifacts to artifacts_dl, then generate v1 summary
 * - Local: point --in to a directory with the same artifact layout
 */
import fs from 'node:fs';
import path from 'node:path';
import { buildArtifactMetadata } from '../ci/lib/artifact-metadata.mjs';

const DEFAULT_IN = 'artifacts_dl';
const DEFAULT_OUT = path.join('artifacts', 'formal', 'formal-summary-v1.json');

function parseArgs(argv) {
  const args = { inDir: DEFAULT_IN, outFile: DEFAULT_OUT };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--in' && next) {
      args.inDir = next;
      i += 1;
    } else if (a.startsWith('--in=')) {
      args.inDir = a.slice('--in='.length);
    } else if (a === '--out' && next) {
      args.outFile = next;
      i += 1;
    } else if (a.startsWith('--out=')) {
      args.outFile = a.slice('--out='.length);
    } else if (a === '--help' || a === '-h') {
      args.help = true;
    }
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/formal/generate-formal-summary-v1.mjs [--in <dir>] [--out <file>]

Options:
  --in <dir>   Input directory containing downloaded artifacts (default: ${DEFAULT_IN})
  --out <file> Output JSON file path (default: ${DEFAULT_OUT})
  -h, --help   Show this help
`);
}

function readJsonSafe(p) {
  try {
    return JSON.parse(fs.readFileSync(p, 'utf8'));
  } catch {
    return undefined;
  }
}

function find(baseDir, relPath) {
  const p = path.join(baseDir, relPath);
  return fs.existsSync(p) ? p : undefined;
}

function mapStatus({ raw, present }) {
  if (!present) return { status: 'missing', reason: 'summary_not_found' };
  if (!raw || typeof raw !== 'object') return { status: 'unknown', reason: 'invalid_json' };

  const status = typeof raw.status === 'string' ? raw.status : '';
  const ran = typeof raw.ran === 'boolean' ? raw.ran : null;
  const ok = typeof raw.ok === 'boolean' ? raw.ok : null;
  const exitCode = typeof raw.exitCode === 'number' ? raw.exitCode : null;

  if (ok === true) return { status: 'ok', reason: null };
  if (ok === false) return { status: 'failed', reason: status || 'ok=false' };

  if (status === 'file_not_found' || status === 'project_not_found' || status === 'jar_not_found') {
    return { status: 'missing', reason: status };
  }
  if (
    status === 'tool_not_available' ||
    status === 'solver_not_available' ||
    status === 'compile_not_available' ||
    status === 'java_not_available' ||
    status === 'jar_not_set'
  ) {
    return { status: 'skipped', reason: status };
  }

  if (status === 'gen_failed' || status === 'compile_failed') {
    return { status: 'failed', reason: status };
  }

  if (status === 'timeout') {
    return { status: 'unknown', reason: status };
  }

  if (exitCode !== null && exitCode !== 0) return { status: 'failed', reason: status || `exitCode=${exitCode}` };
  if (status === 'failed') return { status: 'failed', reason: status };

  if (ran === true && status === 'ran') {
    // Some tools currently do not provide a reliable ok flag; treat as unknown fact-only.
    return { status: 'unknown', reason: 'ran_without_ok' };
  }
  if (ran === false) return { status: 'skipped', reason: status || 'not_ran' };

  return { status: 'unknown', reason: status || null };
}

function buildResultItem({ name, raw, present }) {
  const mapped = mapStatus({ raw, present });
  const code = typeof raw?.exitCode === 'number' ? raw.exitCode : (typeof raw?.code === 'number' ? raw.code : null);
  const durationMs = typeof raw?.timeMs === 'number' ? raw.timeMs : (typeof raw?.durationMs === 'number' ? raw.durationMs : null);
  const logPath = null;
  return {
    name,
    status: mapped.status,
    code,
    durationMs,
    logPath,
    reason: mapped.reason,
  };
}

function computeAggregateStatus(results) {
  const statuses = results.map((r) => r.status);
  const ok = statuses.length > 0 && statuses.every((s) => s === 'ok');
  if (ok) return { ok: true, status: 'ok' };
  if (statuses.some((s) => s === 'failed')) return { ok: false, status: 'failed' };
  if (statuses.length > 0 && statuses.every((s) => s === 'missing')) return { ok: false, status: 'missing' };
  if (statuses.length > 0 && statuses.every((s) => s === 'skipped')) return { ok: false, status: 'skipped' };
  return { ok: false, status: 'unknown' };
}

function main() {
  const args = parseArgs(process.argv);
  if (args.help) {
    printHelp();
    return 0;
  }

  const repoRoot = process.cwd();
  const baseDir = path.resolve(repoRoot, args.inDir);
  if (!fs.existsSync(baseDir)) {
    console.warn(`Input directory not found: ${baseDir} (emitting all-missing summary)`);
  }

  const runTimestampRaw = process.env.RUN_TIMESTAMP;
  const now = (() => {
    if (!runTimestampRaw) return new Date();
    const parsed = new Date(runTimestampRaw);
    return Number.isNaN(parsed.getTime()) ? new Date() : parsed;
  })();
  const metadata = buildArtifactMetadata({ now });

  const inputs = [
    { name: 'tla', rel: path.join('formal-reports-tla', 'tla-summary.json') },
    { name: 'alloy', rel: path.join('formal-reports-alloy', 'alloy-summary.json') },
    { name: 'smt', rel: path.join('formal-reports-smt', 'smt-summary.json') },
    { name: 'apalache', rel: path.join('formal-reports-apalache', 'apalache-summary.json') },
    { name: 'conformance', rel: path.join('formal-reports-conformance', 'conformance-summary.json') },
    { name: 'kani', rel: path.join('formal-reports-kani', 'kani-summary.json') },
    { name: 'spin', rel: path.join('formal-reports-spin', 'spin-summary.json') },
    { name: 'csp', rel: path.join('formal-reports-csp', 'csp-summary.json') },
    { name: 'lean', rel: path.join('formal-reports-lean', 'lean-summary.json') },
  ];

  const results = inputs.map(({ name, rel }) => {
    const p = find(baseDir, rel);
    const raw = p ? readJsonSafe(p) : undefined;
    return buildResultItem({ name, raw, present: Boolean(p) });
  });

  const computed = computeAggregateStatus(results);
  const summary = {
    schemaVersion: 'formal-summary/v1',
    tool: 'aggregate',
    status: computed.status,
    ok: computed.ok,
    generatedAtUtc: metadata.generatedAtUtc,
    metadata,
    results,
  };

  const outFile = path.resolve(repoRoot, args.outFile);
  fs.mkdirSync(path.dirname(outFile), { recursive: true });
  fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
  console.log(`Formal Summary v1 written: ${path.relative(repoRoot, outFile)}`);
  return 0;
}

process.exit(main());
