#!/usr/bin/env node
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const DEFAULT_OUTPUT = 'artifacts/assurance/claim-evidence-provenance.json';
const MANIFEST_PATH = 'artifacts/assurance/claim-evidence-manifest.json';
const GENERATOR_PATH = 'scripts/assurance/build-claim-evidence-manifest.mjs';
const CONTRACT_PATH = 'scripts/ci/lib/claim-evidence-manifest-contract.mjs';
const SCHEMA_PATH = 'schema/claim-evidence-manifest.schema.json';
const SCHEMA_VERSION = 'verify-lite-assurance-provenance/v1';

function sha256File(filePath) {
  if (!fs.existsSync(filePath)) return null;
  return crypto.createHash('sha256').update(fs.readFileSync(filePath)).digest('hex');
}

function ensureParent(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function isoNow() {
  return new Date().toISOString();
}

function env(name) {
  const value = String(process.env[name] || '').trim();
  return value || null;
}

function buildProvenance(outputPath = DEFAULT_OUTPUT) {
  const generatedAt = isoNow();
  return {
    schemaVersion: SCHEMA_VERSION,
    generatedAt,
    repository: env('GITHUB_REPOSITORY'),
    workflow: {
      name: env('GITHUB_WORKFLOW') || 'Verify Lite',
      ref: env('GITHUB_WORKFLOW_REF'),
      sha: env('GITHUB_WORKFLOW_SHA'),
      runId: env('GITHUB_RUN_ID'),
      runAttempt: env('GITHUB_RUN_ATTEMPT'),
      eventName: env('GITHUB_EVENT_NAME'),
      actor: env('GITHUB_ACTOR'),
    },
    source: {
      ref: env('GITHUB_REF'),
      sha: env('VERIFY_LITE_PR_HEAD_SHA') || env('GITHUB_SHA'),
      baseRef: env('GITHUB_BASE_REF'),
      headRef: env('GITHUB_HEAD_REF'),
    },
    artifact: {
      name: 'verify-lite-report',
      manifestPath: MANIFEST_PATH,
      manifestSha256: sha256File(MANIFEST_PATH),
      provenancePath: outputPath,
    },
    generator: {
      command: 'pnpm -s run claim-evidence:generate',
      path: GENERATOR_PATH,
      sha256: sha256File(GENERATOR_PATH),
      schemaPath: SCHEMA_PATH,
      schemaSha256: sha256File(SCHEMA_PATH),
      contractPath: CONTRACT_PATH,
      contractSha256: sha256File(CONTRACT_PATH),
    },
  };
}

function parseArgs(argv) {
  let outputPath = DEFAULT_OUTPUT;
  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if ((arg === '--out' || arg === '--output') && argv[index + 1]) {
      outputPath = argv[++index];
    } else if (arg.startsWith('--out=')) {
      outputPath = arg.slice('--out='.length);
    } else if (arg.startsWith('--output=')) {
      outputPath = arg.slice('--output='.length);
    } else if (arg === '--help') {
      process.stdout.write('Usage: node scripts/ci/write-verify-lite-assurance-provenance.mjs [--out <path>]\n');
      process.exit(0);
    }
  }
  return { outputPath };
}

function main() {
  const { outputPath } = parseArgs(process.argv);
  const provenance = buildProvenance(outputPath);
  ensureParent(outputPath);
  fs.writeFileSync(outputPath, `${JSON.stringify(provenance, null, 2)}\n`);
  process.stdout.write(`[verify-lite-provenance] wrote ${outputPath}\n`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  main();
}

export { buildProvenance };
