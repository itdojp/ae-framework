#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

export const DEFAULT_OUTPUT_JSON = 'tmp/maintenance/tracked-artifact-inventory.json';
export const DEFAULT_OUTPUT_MD = 'tmp/maintenance/tracked-artifact-inventory.md';

const COMMITTED_CONTRACT_PREFIXES = [
  'artifacts/api/',
  'artifacts/bdd/',
  'artifacts/contracts/',
  'artifacts/domain/',
  'artifacts/plan/',
  'artifacts/properties/',
  'artifacts/repros/',
  'artifacts/types/',
];
const COMMITTED_CONTRACT_EXACT = new Set(['artifacts/public-types.current.d.ts']);
const ARCHIVE_PREFIXES = ['artifacts/archive/'];
const LOCAL_DEBUG_PREFIXES = ['artifacts/codex/'];
const REFERENCE_PREFIXES = ['artifacts/hermetic-reports/', 'artifacts/validation-results/'];

export const parseArgs = (argv) => {
  const options = {
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
  };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--') {
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = String(argv[++i] || '').trim();
      if (!options.outputJson) {
        throw new Error('--output-json requires a value');
      }
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = String(argv[++i] || '').trim();
      if (!options.outputMd) {
        throw new Error('--output-md requires a value');
      }
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      process.stdout.write(
        'Usage: node scripts/maintenance/tracked-artifact-inventory.mjs [--output-json <path>] [--output-md <path>]\n',
      );
      process.exit(0);
    }
    throw new Error(`Unknown argument: ${arg}`);
  }
  return options;
};

export const classifyArtifact = (artifactPath) => {
  const normalized = String(artifactPath || '').replaceAll(path.sep, '/');
  if (COMMITTED_CONTRACT_EXACT.has(normalized)) return 'committed-contract';
  if (COMMITTED_CONTRACT_PREFIXES.some((prefix) => normalized.startsWith(prefix))) return 'committed-contract';
  if (ARCHIVE_PREFIXES.some((prefix) => normalized.startsWith(prefix))) return 'archive';
  if (LOCAL_DEBUG_PREFIXES.some((prefix) => normalized.startsWith(prefix))) return 'local-debug-archive';
  if (REFERENCE_PREFIXES.some((prefix) => normalized.startsWith(prefix))) return 'reference-snapshot';
  if (normalized.startsWith('artifacts/')) return 'reference-snapshot';
  throw new Error(`Unsupported artifact path: ${artifactPath}`);
};

export const proposePlacement = (artifactPath) => {
  const normalized = String(artifactPath || '').replaceAll(path.sep, '/');
  const category = classifyArtifact(normalized);
  if (category === 'archive') return { action: 'keep', target: normalized, rationale: 'tracked archive' };
  if (category === 'local-debug-archive') {
    return { action: 'keep', target: normalized, rationale: 'ignored-by-default local debug archive' };
  }
  if (category === 'committed-contract') {
    return { action: 'keep', target: normalized, rationale: 'consumer-facing committed contract artifact' };
  }
  if (normalized.startsWith('artifacts/hermetic-reports/')) {
    return {
      action: 'move',
      target: normalized.replace('artifacts/hermetic-reports/', 'artifacts/reference/hermetic-reports/'),
      rationale: 'tracked reference snapshot outside runtime output namespace',
    };
  }
  if (normalized.startsWith('artifacts/validation-results/')) {
    return {
      action: 'move',
      target: normalized.replace('artifacts/validation-results/', 'artifacts/reference/validation-results/'),
      rationale: 'tracked validation snapshot outside runtime output namespace',
    };
  }
  const basename = path.posix.basename(normalized);
  if (basename.startsWith('bench')) {
    return {
      action: 'move',
      target: `artifacts/reference/benchmarks/${basename}`,
      rationale: 'tracked benchmark baseline at root should move under reference snapshots',
    };
  }
  if (basename.startsWith('types-') || basename === 'public-types.current.d.ts') {
    return {
      action: 'move',
      target: `artifacts/reference/types/${basename}`,
      rationale: 'tracked type/reference snapshot should live under a typed reference namespace',
    };
  }
  if (basename.startsWith('verify') || basename.startsWith('recovery-')) {
    return {
      action: 'move',
      target: `artifacts/reference/verify/${basename}`,
      rationale: 'tracked verification snapshot should move under reference snapshots',
    };
  }
  return {
    action: 'review',
    target: normalized,
    rationale: 'manual placement review required',
  };
};

const runGit = (args) =>
  execFileSync('git', args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  }).trim();

export const listTrackedArtifacts = ({ gitRunner = runGit } = {}) => {
  const output = gitRunner(['ls-files', 'artifacts']);
  return String(output || '')
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean)
    .sort();
};

export const buildInventory = (artifacts) => {
  const items = artifacts.map((artifactPath) => ({
    path: artifactPath,
    category: classifyArtifact(artifactPath),
    proposal: proposePlacement(artifactPath),
  }));
  const summary = items.reduce((acc, item) => {
    acc[item.category] = (acc[item.category] || 0) + 1;
    acc[`${item.proposal.action}Count`] = (acc[`${item.proposal.action}Count`] || 0) + 1;
    return acc;
  }, { total: items.length });
  const topLevelTracked = items.filter((item) => item.path.split('/').length === 2);
  return {
    generatedAt: new Date().toISOString(),
    summary,
    topLevelTracked,
    items,
  };
};

const escapeCell = (value) =>
  String(value ?? '')
    .replaceAll('\\', '\\\\')
    .replaceAll('|', '\\|')
    .replaceAll('\r\n', '<br>')
    .replaceAll('\n', '<br>');

const codeCell = (value) => `\`${escapeCell(value)}\``;

export const renderMarkdown = (report) => {
  const lines = [
    '# Tracked Artifact Inventory',
    '',
    `- generatedAt: ${report.generatedAt}`,
    `- total: ${report.summary.total}`,
    `- committed-contract: ${report.summary['committed-contract'] || 0}`,
    `- reference-snapshot: ${report.summary['reference-snapshot'] || 0}`,
    `- archive: ${report.summary.archive || 0}`,
    `- local-debug-archive: ${report.summary['local-debug-archive'] || 0}`,
    '',
    '## Top-level tracked artifacts',
    '',
    '| Path | Category | Proposed action | Target | Rationale |',
    '| --- | --- | --- | --- | --- |',
  ];
  for (const item of report.topLevelTracked) {
    lines.push(
      `| ${codeCell(item.path)} | ${escapeCell(item.category)} | ${escapeCell(item.proposal.action)} | ${codeCell(item.proposal.target)} | ${escapeCell(item.proposal.rationale)} |`,
    );
  }
  lines.push('', '## Move candidates', '', '| Path | Target | Rationale |', '| --- | --- | --- |');
  for (const item of report.items.filter((entry) => entry.proposal.action === 'move')) {
    lines.push(
      `| ${codeCell(item.path)} | ${codeCell(item.proposal.target)} | ${escapeCell(item.proposal.rationale)} |`,
    );
  }
  lines.push('');
  return lines.join('\n');
};

export const writeOutputs = (report, options) => {
  fs.mkdirSync(path.dirname(options.outputJson), { recursive: true });
  fs.mkdirSync(path.dirname(options.outputMd), { recursive: true });
  fs.writeFileSync(options.outputJson, `${JSON.stringify(report, null, 2)}\n`);
  fs.writeFileSync(options.outputMd, `${renderMarkdown(report)}\n`);
};

export const main = (argv = process.argv) => {
  const options = parseArgs(argv.slice(2));
  const report = buildInventory(listTrackedArtifacts());
  writeOutputs(report, options);
  process.stdout.write(`Tracked artifact inventory written to ${options.outputJson} and ${options.outputMd}\n`);
  return 0;
};

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exitCode = main(process.argv);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`${message}\n`);
    process.exitCode = 1;
  }
}
