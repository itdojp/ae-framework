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
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { buildArtifactMetadata } from '../ci/lib/artifact-metadata.mjs';
import { normalizeArtifactPath } from '../ci/lib/path-normalization.mjs';
import { getFormalRunnerProducer, hasEligibleToolVersion } from './execution-evidence.mjs';

const DEFAULT_IN = 'artifacts_dl';
const DEFAULT_OUT = path.join('artifacts', 'formal', 'formal-summary-v1.json');
const DEFAULT_OUT_V2 = null;
const DEFAULT_LAYOUT = 'downloaded';
const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const repositoryRoot = path.resolve(scriptDir, '..', '..');
const executionEvidenceSchema = JSON.parse(fs.readFileSync(
  path.join(repositoryRoot, 'schema', 'formal-execution-evidence-v1.schema.json'),
  'utf8',
));
const runnerOutputSchema = JSON.parse(fs.readFileSync(
  path.join(repositoryRoot, 'schema', 'formal-runner-output-v1.schema.json'),
  'utf8',
));
const executionEvidenceAjv = new Ajv2020({ allErrors: true, strict: false });
addFormats(executionEvidenceAjv);
const validateExecutionEvidence = executionEvidenceAjv.compile(executionEvidenceSchema);
const validateRunnerOutput = executionEvidenceAjv.compile(runnerOutputSchema);
const SUMMARY_PRODUCER = Object.freeze({
  id: 'ae.formal.summary-generator',
  version: '1.0.0',
  contract: 'formal-summary-adapter/v1',
  artifactRef: 'scripts/formal/generate-formal-summary-v1.mjs',
});
const INELIGIBLE_TOOL_VERSIONS = new Set(['', 'unknown', 'unspecified', 'n/a', 'na', 'none', 'null']);

function parseArgs(argv) {
  const args = {
    inDir: DEFAULT_IN,
    outFile: DEFAULT_OUT,
    outFileV2: DEFAULT_OUT_V2,
    layout: DEFAULT_LAYOUT,
    inProvided: false,
  };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--in' && next) {
      args.inDir = next;
      args.inProvided = true;
      i += 1;
    } else if (a.startsWith('--in=')) {
      args.inDir = a.slice('--in='.length);
      args.inProvided = true;
    } else if (a === '--out' && next) {
      args.outFile = next;
      i += 1;
    } else if (a.startsWith('--out=')) {
      args.outFile = a.slice('--out='.length);
    } else if (a === '--out-v2' && next) {
      args.outFileV2 = next;
      i += 1;
    } else if (a.startsWith('--out-v2=')) {
      args.outFileV2 = a.slice('--out-v2='.length);
    } else if (a === '--layout' && next) {
      args.layout = next;
      i += 1;
    } else if (a.startsWith('--layout=')) {
      args.layout = a.slice('--layout='.length);
    } else if (a === '--help' || a === '-h') {
      args.help = true;
    }
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/formal/generate-formal-summary-v1.mjs [--layout <downloaded|hermetic>] [--in <dir>] [--out <file>] [--out-v2 <file>]

Options:
  --layout <downloaded|hermetic> Input layout (default: ${DEFAULT_LAYOUT})
  --in <dir>                   Input directory (default: ${DEFAULT_IN})
                               downloaded: expects formal-reports-*/... under <dir>
                               hermetic: expects artifacts/hermetic-reports layout under <dir>
  --out <file>                 Output JSON file path (default: ${DEFAULT_OUT})
  --out-v2 <file>              Optional Formal Summary v2 output path (disabled by default)
  -h, --help                   Show this help
`);
}

function toFormalSummaryV2(summaryV1) {
  return {
    ...summaryV1,
    schemaVersion: 'formal-summary/v2',
    contractId: 'formal-summary.v2',
  };
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

function normalizeLayout(layout) {
  const s = String(layout || '')
    .trim()
    .toLowerCase();
  if (!s) return DEFAULT_LAYOUT;
  if (s === 'downloaded' || s === 'ci' || s === 'artifacts_dl') return 'downloaded';
  if (s === 'hermetic' || s === 'local' || s === 'workspace') return 'hermetic';
  return s;
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

  if (status === 'timeout') return { status: 'timeout', reason: status };
  if (status === 'tool-error' || status === 'error') return { status: 'tool-error', reason: status };

  if (exitCode !== null && exitCode !== 0) return { status: 'failed', reason: status || `exitCode=${exitCode}` };
  if (status === 'failed') return { status: 'failed', reason: status };

  if (ran === true && status === 'ran') {
    // Some tools currently do not provide a reliable ok flag; treat as unknown fact-only.
    return { status: 'unknown', reason: 'ran_without_ok' };
  }
  if (ran === false) return { status: 'skipped', reason: status || 'not_ran' };

  return { status: 'unknown', reason: status || null };
}

function resolveLogPath({ repoRoot, baseDir, name, raw, summaryPath, summaryRel }) {
  const candidates = [];
  const push = (p) => { if (p) candidates.push(p); };
  const baseRoot = path.resolve(baseDir);
  const isWithinBaseDir = (p) => {
    const rel = path.relative(baseRoot, p);
    return !rel.startsWith('..') && !path.isAbsolute(rel);
  };

  const rawPaths = [];
  if (typeof raw?.logPath === 'string' && raw.logPath.trim()) rawPaths.push(raw.logPath.trim());
  if (typeof raw?.outputFile === 'string' && raw.outputFile.trim()) rawPaths.push(raw.outputFile.trim());
  if (typeof raw?.runnerResult?.executionEvidence?.result?.logPath === 'string'
    && raw.runnerResult.executionEvidence.result.logPath.trim()) {
    rawPaths.push(raw.runnerResult.executionEvidence.result.logPath.trim());
  }

  for (const rp of rawPaths) {
    if (path.isAbsolute(rp)) {
      push(path.resolve(rp));
      continue;
    }
    // Prefer paths relative to the summary/input dirs, then fall back to repo-relative (contract).
    if (summaryPath) push(path.resolve(path.dirname(summaryPath), rp));
    push(path.resolve(baseDir, rp));
    push(path.resolve(repoRoot, rp));
  }

  const evidenceLogPath = typeof raw?.runnerResult?.executionEvidence?.result?.logPath === 'string'
    ? raw.runnerResult.executionEvidence.result.logPath.trim()
    : '';
  if (summaryPath && evidenceLogPath && path.basename(evidenceLogPath) === path.basename(summaryPath)) {
    push(path.resolve(summaryPath));
  }

  // Conventional log filename: <tool>-output.txt next to the summary file.
  if (summaryPath) {
    push(path.join(path.dirname(summaryPath), `${name}-output.txt`));
  } else if (summaryRel) {
    push(path.join(baseDir, path.dirname(summaryRel), `${name}-output.txt`));
  }

  for (const p of candidates) {
    if (!p) continue;
    const abs = path.resolve(p);
    if (!isWithinBaseDir(abs)) continue;
    if (fs.existsSync(abs)) return normalizeArtifactPath(abs, { repoRoot });
  }
  return null;
}

function hasExactProducerBinding(actual, expected) {
  return actual
    && typeof actual === 'object'
    && !Array.isArray(actual)
    && actual.id === expected.id
    && actual.version === expected.version
    && actual.contract === expected.contract
    && actual.artifactRef === expected.artifactRef;
}

function normalizeRunnerReportedExecutionEvidence(raw, expectedStatus, runnerName, resolvedLogPath) {
  const runnerResult = raw?.runnerResult;
  if (!runnerResult || typeof runnerResult !== 'object' || Array.isArray(runnerResult)) return null;
  if (!validateRunnerOutput(runnerResult)) return null;
  const evidence = runnerResult.executionEvidence;
  if (!evidence || typeof evidence !== 'object' || Array.isArray(evidence)) return null;
  const expectedProducers = runnerName === 'conformance'
    ? [getFormalRunnerProducer('conformance'), getFormalRunnerProducer('conformanceDriver')]
    : [getFormalRunnerProducer(runnerName)];
  if (!validateExecutionEvidence(evidence)) return null;
  if (evidence.provenance !== 'runner-reported' || evidence.adapter !== undefined) return null;
  if (!expectedProducers.some((producer) => hasExactProducerBinding(runnerResult.producer, producer))) return null;
  if (!expectedProducers.some((producer) => hasExactProducerBinding(evidence.producer, producer))) return null;
  if (!hasExactProducerBinding(evidence.producer, runnerResult.producer)) return null;
  if (runnerResult.artifactStatus !== evidence.artifactStatus) return null;
  if (evidence.result.status !== expectedStatus) return null;
  const rawCode = typeof raw?.exitCode === 'number' ? raw.exitCode : (typeof raw?.code === 'number' ? raw.code : null);
  if (evidence.result.code !== rawCode) return null;
  if (evidence.executionOccurred === true && !resolvedLogPath) return null;
  if (evidence.executionOccurred === true
    && path.basename(evidence.result.logPath) !== path.basename(resolvedLogPath)) return null;
  return {
    ...JSON.parse(JSON.stringify(evidence)),
    provenance: 'adapter-verified',
    adapter: SUMMARY_PRODUCER,
  };
}

function buildResultItem({ name, raw, present, logPath }) {
  const mapped = mapStatus({ raw, present });
  const code = typeof raw?.exitCode === 'number' ? raw.exitCode : (typeof raw?.code === 'number' ? raw.code : null);
  const durationMs = typeof raw?.timeMs === 'number' ? raw.timeMs : (typeof raw?.durationMs === 'number' ? raw.durationMs : null);
  const executionEvidence = normalizeRunnerReportedExecutionEvidence(raw, mapped.status, name, logPath);
  const evidenceWasPresent = raw?.runnerResult && typeof raw.runnerResult === 'object';
  const versionEvidenceGap = executionEvidence
    && (!hasEligibleToolVersion(executionEvidence.tool)
      || INELIGIBLE_TOOL_VERSIONS.has(String(executionEvidence.tool.version).trim().toLowerCase()));
  const requiresExecutionEvidence = ['ok', 'failed', 'timeout', 'tool-error'].includes(mapped.status);
  const missingRequiredEvidence = requiresExecutionEvidence && !executionEvidence;
  const status = missingRequiredEvidence || (mapped.status === 'ok' && versionEvidenceGap)
    ? 'unknown'
    : mapped.status;
  const reason = missingRequiredEvidence
    ? (evidenceWasPresent ? 'invalid_runner_output_contract' : 'runner_output_contract_missing')
    : mapped.status === 'ok' && versionEvidenceGap
      ? 'tool_version_evidence_gap'
      : mapped.reason;
  return {
    name,
    status,
    artifactStatus: executionEvidence?.artifactStatus ?? 'not-executed',
    code,
    durationMs,
    logPath,
    reason,
    ...(executionEvidence ? { executionEvidence } : {}),
  };
}

function computeAggregateStatus(results) {
  const statuses = results.map((r) => r.status);
  const ok = statuses.length > 0 && statuses.every((s) => s === 'ok');
  if (ok) return { ok: true, status: 'ok' };
  if (statuses.some((s) => s === 'failed')) return { ok: false, status: 'failed' };
  if (statuses.some((s) => s === 'tool-error')) return { ok: false, status: 'tool-error' };
  if (statuses.some((s) => s === 'timeout')) return { ok: false, status: 'timeout' };
  if (statuses.length > 0 && statuses.every((s) => s === 'missing')) return { ok: false, status: 'missing' };
  if (statuses.length > 0 && statuses.every((s) => s === 'skipped')) return { ok: false, status: 'skipped' };
  return { ok: false, status: 'unknown' };
}

function getInputs(layout) {
  if (layout === 'hermetic') {
    return [
      { name: 'tla', rel: path.join('formal', 'tla-summary.json') },
      { name: 'alloy', rel: path.join('formal', 'alloy-summary.json') },
      { name: 'smt', rel: path.join('formal', 'smt-summary.json') },
      { name: 'apalache', rel: path.join('formal', 'apalache-summary.json') },
      { name: 'conformance', rel: path.join('conformance', 'summary.json') },
      { name: 'kani', rel: path.join('formal', 'kani-summary.json') },
      { name: 'spin', rel: path.join('formal', 'spin-summary.json') },
      { name: 'csp', rel: path.join('formal', 'csp-summary.json') },
      { name: 'lean', rel: path.join('formal', 'lean-summary.json') },
    ];
  }

  return [
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
}

function main() {
  const args = parseArgs(process.argv);
  if (args.help) {
    printHelp();
    return 0;
  }

  const repoRoot = process.cwd();
  const layout = normalizeLayout(args.layout);
  if (layout !== 'downloaded' && layout !== 'hermetic') {
    console.error(`Unsupported --layout: ${args.layout} (expected: downloaded|hermetic)`);
    return 2;
  }

  const inDir =
    layout === 'hermetic' && !args.inProvided ? path.join('artifacts', 'hermetic-reports') : args.inDir;

  const baseDir = path.resolve(repoRoot, inDir);
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

  const inputs = getInputs(layout);

  const results = inputs.map(({ name, rel }) => {
    const p = find(baseDir, rel);
    const raw = p ? readJsonSafe(p) : undefined;
    const logPath = resolveLogPath({ repoRoot, baseDir, name, raw, summaryPath: p, summaryRel: rel });
    return buildResultItem({ name, raw, present: Boolean(p), logPath });
  });

  const computed = computeAggregateStatus(results);
  const summary = {
    schemaVersion: 'formal-summary/v1',
    tool: 'aggregate',
    artifactStatus: 'execution-report',
    producer: SUMMARY_PRODUCER,
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

  if (args.outFileV2) {
    const summaryV2 = toFormalSummaryV2(summary);
    const outFileV2 = path.resolve(repoRoot, args.outFileV2);
    fs.mkdirSync(path.dirname(outFileV2), { recursive: true });
    fs.writeFileSync(outFileV2, JSON.stringify(summaryV2, null, 2));
    console.log(`Formal Summary v2 written: ${path.relative(repoRoot, outFileV2)}`);
  }
  return 0;
}

process.exit(main());
