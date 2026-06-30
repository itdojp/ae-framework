#!/usr/bin/env node
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const SCHEMA_VERSION = 'variance-report/v1';
const CONTRACT_ID = 'variance-report.v1';
const DEFAULT_GENERATED_AT = '1970-01-01T00:00:00.000Z';
const DEFAULT_OUTPUT_JSON = 'artifacts/quality/variance-report.json';
const DEFAULT_OUTPUT_MD = 'artifacts/quality/variance-report.md';
const DEFAULT_ALLOWED_FIELD_NAMES = [
  'generatedAt',
  'generatedAtUtc',
  'generatedAtLocal',
  'timestamp',
  'startedAt',
  'completedAt',
  'durationMs',
  'runId',
  'runAttempt',
];
const INPUT_GROUPS = [
  ['contextPack', 'context-pack'],
  ['execPlan', 'exec-plan'],
  ['templates', 'template'],
  ['validationCommands', 'validation-command'],
  ['toolVersions', 'tool-version'],
  ['artifactContracts', 'artifact-contract'],
];

function readRequiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (!value || value.startsWith('--')) {
    throw new Error(`missing value for ${option}`);
  }
  return value;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    baseline: null,
    candidate: null,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    generatedAt: DEFAULT_GENERATED_AT,
    allowedFieldNames: [...DEFAULT_ALLOWED_FIELD_NAMES],
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      break;
    }
    if (arg === '--baseline') {
      options.baseline = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--candidate') {
      options.candidate = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--allowed-field') {
      const value = readRequiredValue(argv, index, arg);
      if (!options.allowedFieldNames.includes(value)) {
        options.allowedFieldNames.push(value);
      }
      index += 1;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  if (!Number.isNaN(Date.parse(options.generatedAt))) {
    options.generatedAt = new Date(options.generatedAt).toISOString();
  } else if (!options.help) {
    throw new Error(`--generated-at must be an ISO date-time: ${options.generatedAt}`);
  }

  if (!options.help) {
    if (!options.baseline) {
      throw new Error('--baseline is required');
    }
    if (!options.candidate) {
      throw new Error('--candidate is required');
    }
  }
  options.allowedFieldNames.sort();
  return options;
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/quality/compare-judgment-artifacts.mjs --baseline <json> --candidate <json> [options]\n\nOptions:\n  --output-json <path>     JSON report path (default: ${DEFAULT_OUTPUT_JSON})\n  --output-md <path>       Markdown report path (default: ${DEFAULT_OUTPUT_MD})\n  --generated-at <iso>     report timestamp (default: ${DEFAULT_GENERATED_AT} for deterministic output)\n  --allowed-field <name>   additional volatile field name to ignore during normalized comparison (repeatable)\n  --help                   show this help\n`);
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function canonicalize(value) {
  return JSON.stringify(value ?? null);
}

function hashValue(value) {
  return crypto.createHash('sha256').update(canonicalize(value)).digest('hex');
}

function normalizeValue(value, allowedNames) {
  if (Array.isArray(value)) {
    const normalizedItems = value
      .map((entry) => normalizeValue(entry, allowedNames))
      .filter((entry) => entry !== undefined);
    return normalizedItems.length > 0 ? normalizedItems : undefined;
  }
  if (value && typeof value === 'object') {
    const normalized = {};
    for (const key of Object.keys(value).sort()) {
      if (allowedNames.has(key)) {
        continue;
      }
      const normalizedChild = normalizeValue(value[key], allowedNames);
      if (normalizedChild !== undefined) {
        normalized[key] = normalizedChild;
      }
    }
    return Object.keys(normalized).length > 0 ? normalized : undefined;
  }
  return value;
}

function valueToString(value) {
  if (typeof value === 'string') {
    return value;
  }
  if (value === undefined) {
    return '<missing>';
  }
  return JSON.stringify(value);
}

function pathToPointer(pathParts) {
  if (pathParts.length === 0) {
    return '$';
  }
  return `$${pathParts.map((part) => (typeof part === 'number' ? `[${part}]` : `.${part}`)).join('')}`;
}

function classify(pathParts) {
  const joined = pathParts.join('.');
  if (joined.startsWith('inputFingerprints.contextPack')) {
    return ['context-drift', 'context-pack'];
  }
  if (joined.startsWith('inputFingerprints.execPlan')) {
    return ['context-drift', 'exec-plan'];
  }
  if (joined.startsWith('inputFingerprints.templates')) {
    return ['prompt-template-drift', 'template'];
  }
  if (joined.startsWith('inputFingerprints.validationCommands')) {
    return ['check-order-drift', 'validation-command'];
  }
  if (joined.startsWith('inputFingerprints.toolVersions')) {
    return ['tool-version-drift', 'tool-version'];
  }
  if (joined.startsWith('inputFingerprints.artifactContracts') || joined.endsWith('schemaVersion') || joined.endsWith('contractId')) {
    return ['artifact-shape-drift', 'artifact-contract'];
  }
  return ['value-drift', 'judgment-artifact'];
}

function diffValues(baseline, candidate, pathParts = []) {
  if (Object.is(baseline, candidate)) {
    return [];
  }
  if (Array.isArray(baseline) || Array.isArray(candidate)) {
    if (!Array.isArray(baseline) || !Array.isArray(candidate)) {
      return [{ pathParts, baselineValue: baseline, candidateValue: candidate }];
    }
    const diffs = [];
    const maxLength = Math.max(baseline.length, candidate.length);
    for (let index = 0; index < maxLength; index += 1) {
      diffs.push(...diffValues(baseline[index], candidate[index], [...pathParts, index]));
    }
    return diffs;
  }
  if (baseline && typeof baseline === 'object' && candidate && typeof candidate === 'object') {
    const keys = new Set([...Object.keys(baseline), ...Object.keys(candidate)]);
    const diffs = [];
    for (const key of [...keys].sort()) {
      diffs.push(...diffValues(baseline[key], candidate[key], [...pathParts, key]));
    }
    return diffs;
  }
  return [{ pathParts, baselineValue: baseline, candidateValue: candidate }];
}

function collectAllowedDifferences(baseline, candidate, allowedNames, pathParts = []) {
  const baselineIsObject = baseline && typeof baseline === 'object';
  const candidateIsObject = candidate && typeof candidate === 'object';
  if (!baselineIsObject && !candidateIsObject) {
    return [];
  }
  const differences = [];
  const keys = new Set([
    ...(baselineIsObject ? Object.keys(baseline) : []),
    ...(candidateIsObject ? Object.keys(candidate) : []),
  ]);
  for (const key of [...keys].sort()) {
    const nextPath = [...pathParts, key];
    const baselineValue = baselineIsObject ? baseline[key] : undefined;
    const candidateValue = candidateIsObject ? candidate[key] : undefined;
    if (allowedNames.has(key)) {
      if (!Object.is(baselineValue, candidateValue)) {
        differences.push({
          affectedEvidencePath: pathToPointer(nextPath),
          fieldName: key,
          reason: 'volatile field allowed by variance normalization policy',
          baselineValue: valueToString(baselineValue),
          candidateValue: valueToString(candidateValue),
        });
      }
      continue;
    }
    if (Array.isArray(baselineValue) || Array.isArray(candidateValue)) {
      const baselineArray = Array.isArray(baselineValue) ? baselineValue : [];
      const candidateArray = Array.isArray(candidateValue) ? candidateValue : [];
      const maxLength = Math.max(baselineArray.length, candidateArray.length);
      for (let index = 0; index < maxLength; index += 1) {
        differences.push(...collectAllowedDifferences(baselineArray[index], candidateArray[index], allowedNames, [...nextPath, index]));
      }
      continue;
    }
    differences.push(...collectAllowedDifferences(baselineValue, candidateValue, allowedNames, nextPath));
  }
  return differences;
}

function buildInputHashes(baseline, candidate, allowedNames) {
  const hashes = [];
  for (const [groupName, sourceInputKind] of INPUT_GROUPS) {
    const baselineValue = baseline.inputFingerprints?.[groupName] ?? null;
    const candidateValue = candidate.inputFingerprints?.[groupName] ?? null;
    const normalizedBaseline = normalizeValue(baselineValue, allowedNames);
    const normalizedCandidate = normalizeValue(candidateValue, allowedNames);
    const baselineSha256 = hashValue(normalizedBaseline);
    const candidateSha256 = hashValue(normalizedCandidate);
    hashes.push({
      sourceInputKind,
      affectedEvidencePath: `$.inputFingerprints.${groupName}`,
      baselineSha256,
      candidateSha256,
      match: baselineSha256 === candidateSha256,
    });
  }
  return hashes;
}

function buildFindings(diffs) {
  return diffs.map((diff, index) => {
    const [category, sourceInputKind] = classify(diff.pathParts);
    const affectedEvidencePath = pathToPointer(diff.pathParts);
    return {
      id: `variance-${String(index + 1).padStart(3, '0')}`,
      category,
      severity: 'warn',
      reportOnly: true,
      judgmentRelevant: true,
      sourceInputKind,
      affectedEvidencePath,
      message: `Normalized judgment artifact differs at ${affectedEvidencePath}.`,
      baselineValue: valueToString(diff.baselineValue),
      candidateValue: valueToString(diff.candidateValue),
    };
  });
}

export function compareJudgmentArtifacts(options) {
  const allowedNames = new Set(options.allowedFieldNames);
  const baseline = readJson(options.baseline);
  const candidate = readJson(options.candidate);
  const normalizedBaseline = normalizeValue(baseline, allowedNames);
  const normalizedCandidate = normalizeValue(candidate, allowedNames);
  const normalizedJudgment = {
    baselineSha256: hashValue(normalizedBaseline),
    candidateSha256: hashValue(normalizedCandidate),
    match: false,
  };
  normalizedJudgment.match = normalizedJudgment.baselineSha256 === normalizedJudgment.candidateSha256;
  const diffs = diffValues(normalizedBaseline, normalizedCandidate);
  const expectedDifferences = collectAllowedDifferences(baseline, candidate, allowedNames);
  const findings = buildFindings(diffs);

  return {
    schemaVersion: SCHEMA_VERSION,
    contractId: CONTRACT_ID,
    generatedAt: options.generatedAt,
    enforcement: {
      mode: 'report-only',
      ordinaryPrBlocking: false,
      policy: 'Variance reports make judgment drift visible without blocking ordinary PRs in this issue slice.',
      promotionRule: 'Future enforcement requires stable fixtures, known false-positive handling, documented allowed fields, and an explicit policy-gate change.',
    },
    inputs: {
      baseline: options.baseline,
      candidate: options.candidate,
    },
    normalization: {
      allowedFieldNames: options.allowedFieldNames,
      arrayOrderPolicy: 'preserve-order',
    },
    summary: {
      status: findings.length === 0 ? 'stable' : 'drift',
      findingCount: findings.length,
      reportOnlyFindingCount: findings.length,
      judgmentRelevantFindingCount: findings.filter((finding) => finding.judgmentRelevant).length,
      expectedDifferenceCount: expectedDifferences.length,
    },
    inputHashes: buildInputHashes(baseline, candidate, allowedNames),
    normalizedJudgment,
    expectedDifferences,
    findings,
  };
}

function renderMarkdown(report) {
  const hashRows = report.inputHashes.map((entry) => `| ${entry.sourceInputKind} | ${entry.affectedEvidencePath} | ${entry.match ? 'yes' : 'no'} | \`${entry.baselineSha256}\` | \`${entry.candidateSha256}\` |`).join('\n');
  const expectedRows = report.expectedDifferences.length > 0
    ? report.expectedDifferences.map((entry) => `| ${entry.affectedEvidencePath} | ${entry.fieldName} | ${entry.reason} |`).join('\n')
    : '| _none_ | _n/a_ | _n/a_ |';
  const findingRows = report.findings.length > 0
    ? report.findings.map((finding) => `| ${finding.id} | ${finding.category} | ${finding.sourceInputKind} | ${finding.affectedEvidencePath} | ${finding.judgmentRelevant ? 'yes' : 'no'} | ${finding.message} |`).join('\n')
    : '| _none_ | _n/a_ | _n/a_ | _n/a_ | _n/a_ | _n/a_ |';

  return `# Variance Report\n\nGenerated at: ${report.generatedAt}\n\n## Summary\n\n- Status: **${report.summary.status}**\n- Enforcement: **${report.enforcement.mode}**\n- Ordinary PR blocking: **${report.enforcement.ordinaryPrBlocking ? 'yes' : 'no'}**\n- Normalized judgment match: **${report.normalizedJudgment.match ? 'yes' : 'no'}**\n- Findings: **${report.summary.findingCount}**\n- Expected volatile differences: **${report.summary.expectedDifferenceCount}**\n\n${report.enforcement.policy}\n\n## Input hashes\n\n| Source input | Evidence path | Match | Baseline SHA-256 | Candidate SHA-256 |\n| --- | --- | --- | --- | --- |\n${hashRows}\n\n## Expected differences\n\n| Evidence path | Field | Reason |\n| --- | --- | --- |\n${expectedRows}\n\n## Drift findings\n\n| ID | Category | Source input | Evidence path | Judgment relevant | Message |\n| --- | --- | --- | --- | --- | --- |\n${findingRows}\n\n## Promotion rule\n\n${report.enforcement.promotionRule}\n`;
}

function writeJson(filePath, payload) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function writeText(filePath, text) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, text.endsWith('\n') ? text : `${text}\n`);
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }
  const report = compareJudgmentArtifacts(options);
  writeJson(options.outputJson, report);
  writeText(options.outputMd, renderMarkdown(report));
  process.stdout.write(`Wrote ${options.outputJson}\n`);
  process.stdout.write(`Wrote ${options.outputMd}\n`);
  return 0;
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  try {
    process.exitCode = run();
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    process.exitCode = 1;
  }
}
