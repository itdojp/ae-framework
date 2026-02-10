#!/usr/bin/env node
/**
 * Generate a run manifest that records which artifacts were produced and whether they are "fresh"
 * for the current git commit.
 *
 * Intended usage:
 * - CI: generate + check (non-blocking -> opt-in strict)
 * - Local: detect stale artifacts when re-running only parts of the pipeline
 */
import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { buildArtifactMetadata } from './lib/artifact-metadata.mjs';
import { normalizeArtifactPath } from './lib/path-normalization.mjs';

const DEFAULT_OUT = path.join('artifacts', 'run-manifest.json');
const DEFAULT_SCHEMA_VERSION = '1.0.0';

function parseArgs(argv) {
  const args = {
    out: DEFAULT_OUT,
    topLevelCommand: null,
  };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--out' && next) {
      args.out = next;
      i += 1;
    } else if (a.startsWith('--out=')) {
      args.out = a.slice('--out='.length);
    } else if (a === '--top-level-command' && next) {
      args.topLevelCommand = next;
      i += 1;
    } else if (a.startsWith('--top-level-command=')) {
      args.topLevelCommand = a.slice('--top-level-command='.length);
    } else if (a === '--help' || a === '-h') {
      args.help = true;
    }
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/ci/generate-run-manifest.mjs [--out <file>] [--top-level-command <string>]

Options:
  --out <file>                 Output path (default: ${DEFAULT_OUT})
  --top-level-command <string> Human-readable command/workflow label (recommended)
  -h, --help                   Show this help
`);
}

function readJsonSafe(filePath) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch {
    return undefined;
  }
}

function coerceCommit(value) {
  if (!value) return null;
  const s = String(value).trim();
  return s ? s : null;
}

function commitEquals(a, b) {
  const left = coerceCommit(a);
  const right = coerceCommit(b);
  if (!left || !right) return null;
  if (left === right) return true;
  if (left.length >= 7 && right.length >= 7 && (left.startsWith(right) || right.startsWith(left))) return true;
  return false;
}

function extractProducedCommit(payload) {
  if (!payload || typeof payload !== 'object') return { commit: null, source: null };
  const metaCommit = coerceCommit(payload?.metadata?.gitCommit);
  if (metaCommit) return { commit: metaCommit, source: 'metadata.gitCommit' };
  const correlationCommit = coerceCommit(payload?.correlation?.commit);
  if (correlationCommit) return { commit: correlationCommit, source: 'correlation.commit' };
  const traceCorrelationCommit = coerceCommit(payload?.traceCorrelation?.commit);
  if (traceCorrelationCommit) return { commit: traceCorrelationCommit, source: 'traceCorrelation.commit' };
  return { commit: null, source: null };
}

function summarizeArtifact({ name, relPath }, { repoRoot, currentCommit }) {
  const resolved = path.resolve(repoRoot, relPath);
  const normalizedPath = normalizeArtifactPath(relPath, { repoRoot }) ?? relPath;

  if (!fs.existsSync(resolved)) {
    return [
      name,
      {
        path: normalizedPath,
        status: 'missing',
        producedByCommit: null,
        staleComparedToCurrentCommit: null,
        commitSource: null,
        notes: null,
      },
    ];
  }

  if (!relPath.endsWith('.json')) {
    return [
      name,
      {
        path: normalizedPath,
        status: 'present',
        producedByCommit: null,
        staleComparedToCurrentCommit: null,
        commitSource: null,
        notes: 'non_json_artifact',
      },
    ];
  }

  const payload = readJsonSafe(resolved);
  if (!payload) {
    return [
      name,
      {
        path: normalizedPath,
        status: 'invalid_json',
        producedByCommit: null,
        staleComparedToCurrentCommit: null,
        commitSource: null,
        notes: null,
      },
    ];
  }

  const produced = extractProducedCommit(payload);
  const isSame = commitEquals(currentCommit, produced.commit);
  return [
    name,
    {
      path: normalizedPath,
      status: 'present',
      producedByCommit: produced.commit,
      staleComparedToCurrentCommit: isSame === null ? null : !isSame,
      commitSource: produced.source,
      notes: produced.commit ? null : 'commit_not_found_in_artifact',
    },
  ];
}

export function main(argv = process.argv) {
  const args = parseArgs(argv);
  if (args.help) {
    printHelp();
    return 0;
  }

  const repoRoot = process.cwd();
  const runTimestamp = process.env.RUN_TIMESTAMP || new Date().toISOString();
  const metadata = buildArtifactMetadata({ now: runTimestamp });
  const currentCommit = metadata?.gitCommit ?? null;

  const topLevelCommand =
    args.topLevelCommand ??
    process.env.RUN_MANIFEST_TOP_LEVEL_COMMAND ??
    process.env.GITHUB_WORKFLOW ??
    process.env.GITHUB_JOB ??
    'local-run';

  const targets = [
    { name: 'verifyLite', relPath: path.join('artifacts', 'verify-lite', 'verify-lite-run-summary.json') },
    { name: 'reportEnvelope', relPath: path.join('artifacts', 'report-envelope.json') },
    { name: 'formal', relPath: path.join('artifacts', 'hermetic-reports', 'formal', 'summary.json') },
    { name: 'conformance', relPath: path.join('artifacts', 'hermetic-reports', 'conformance', 'summary.json') },
    { name: 'progress', relPath: path.join('artifacts', 'progress', 'summary.json') },
  ];

  const summaries = Object.fromEntries(
    targets.map((target) => summarizeArtifact(target, { repoRoot, currentCommit })),
  );

  const manifest = {
    schemaVersion: process.env.RUN_MANIFEST_SCHEMA_VERSION ?? DEFAULT_SCHEMA_VERSION,
    topLevelCommand,
    timestamp: runTimestamp,
    metadata,
    summaries,
  };

  const outPath = path.resolve(repoRoot, args.out);
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, JSON.stringify(manifest, null, 2));
  console.log(`[run-manifest] wrote ${normalizeArtifactPath(outPath, { repoRoot }) ?? outPath}`);
  return 0;
}

const selfUrl = pathToFileURL(process.argv[1] || '').href;
if (selfUrl === import.meta.url) {
  process.exit(main(process.argv));
}
