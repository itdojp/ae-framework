#!/usr/bin/env node
/**
 * Check a run manifest for freshness and emit a machine-readable result JSON.
 */
import fs from 'node:fs';
import path from 'node:path';
import { normalizeArtifactPath } from './lib/path-normalization.mjs';

const DEFAULT_MANIFEST = path.join('artifacts', 'run-manifest.json');
const DEFAULT_RESULT = path.join('artifacts', 'run-manifest-check.json');

function parseArgs(argv) {
  const args = {
    manifest: DEFAULT_MANIFEST,
    result: DEFAULT_RESULT,
    requireFresh: [],
    expectTopLevelCommand: null,
  };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--manifest' && next) {
      args.manifest = next;
      i += 1;
    } else if (a.startsWith('--manifest=')) {
      args.manifest = a.slice('--manifest='.length);
    } else if (a === '--result' && next) {
      args.result = next;
      i += 1;
    } else if (a.startsWith('--result=')) {
      args.result = a.slice('--result='.length);
    } else if (a === '--require-fresh' && next) {
      args.requireFresh.push(next);
      i += 1;
    } else if (a.startsWith('--require-fresh=')) {
      args.requireFresh.push(a.slice('--require-fresh='.length));
    } else if (a === '--expect-top-level-command' && next) {
      args.expectTopLevelCommand = next;
      i += 1;
    } else if (a.startsWith('--expect-top-level-command=')) {
      args.expectTopLevelCommand = a.slice('--expect-top-level-command='.length);
    } else if (a === '--help' || a === '-h') {
      args.help = true;
    }
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/ci/check-run-manifest.mjs [--manifest <file>] [--require-fresh <names>] [--result <file>]

Options:
  --manifest <file>                 Manifest path (default: ${DEFAULT_MANIFEST})
  --require-fresh <names>           Comma-separated list (repeatable)
  --expect-top-level-command <str>  Fail if manifest.topLevelCommand differs
  --result <file>                   Result JSON path (default: ${DEFAULT_RESULT})
  -h, --help                        Show this help
`);
}

function splitCsv(values) {
  return values
    .flatMap((v) => String(v || '').split(','))
    .map((s) => s.trim())
    .filter(Boolean);
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function main(argv = process.argv) {
  const args = parseArgs(argv);
  if (args.help) {
    printHelp();
    return 0;
  }

  const repoRoot = process.cwd();
  const manifestPath = path.resolve(repoRoot, args.manifest);
  const resultPath = path.resolve(repoRoot, args.result);

  const violations = [];
  let manifest;

  if (!fs.existsSync(manifestPath)) {
    violations.push({ kind: 'manifest_missing', message: 'run manifest file not found' });
  } else {
    try {
      manifest = readJson(manifestPath);
    } catch (error) {
      violations.push({ kind: 'manifest_invalid_json', message: error instanceof Error ? error.message : String(error) });
    }
  }

  const requiredFresh = splitCsv(args.requireFresh);
  const currentCommit = manifest?.metadata?.gitCommit ?? null;

  if (manifest && args.expectTopLevelCommand) {
    if (String(manifest.topLevelCommand || '') !== String(args.expectTopLevelCommand)) {
      violations.push({
        kind: 'top_level_command_mismatch',
        expected: args.expectTopLevelCommand,
        actual: manifest.topLevelCommand ?? null,
      });
    }
  }

  if (manifest && requiredFresh.length > 0) {
    const summaries = manifest.summaries && typeof manifest.summaries === 'object' ? manifest.summaries : {};
    for (const name of requiredFresh) {
      const entry = summaries[name];
      if (!entry) {
        violations.push({ kind: 'summary_missing', name });
        continue;
      }
      if (entry.status !== 'present') {
        violations.push({ kind: 'summary_not_present', name, status: entry.status ?? null });
        continue;
      }
      if (entry.staleComparedToCurrentCommit === null || entry.staleComparedToCurrentCommit === undefined) {
        violations.push({
          kind: 'freshness_unknown',
          name,
          currentCommit,
          producedByCommit: entry.producedByCommit ?? null,
          commitSource: entry.commitSource ?? null,
        });
        continue;
      }
      if (entry.staleComparedToCurrentCommit) {
        violations.push({
          kind: 'stale_artifact',
          name,
          currentCommit,
          producedByCommit: entry.producedByCommit ?? null,
          path: entry.path ?? null,
        });
      }
    }
  }

  const ok = violations.length === 0;
  const result = {
    schemaVersion: '1.0.0',
    checkedAt: new Date().toISOString(),
    ok,
    manifest: normalizeArtifactPath(manifestPath, { repoRoot }) ?? manifestPath,
    requireFresh: requiredFresh,
    violations,
  };

  fs.mkdirSync(path.dirname(resultPath), { recursive: true });
  fs.writeFileSync(resultPath, JSON.stringify(result, null, 2));
  console.log(`[run-manifest-check] ok=${ok} violations=${violations.length}`);
  if (!ok) {
    for (const v of violations.slice(0, 10)) {
      console.log(`- ${v.kind}${v.name ? ` (${v.name})` : ''}`);
    }
    if (violations.length > 10) {
      console.log(`... ${violations.length - 10} more`);
    }
  }

  return ok ? 0 : 1;
}

process.exit(main(process.argv));

