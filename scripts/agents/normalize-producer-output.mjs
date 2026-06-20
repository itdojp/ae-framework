#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/agents/producer-normalization-summary.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/agents/producer-normalization-summary.md';
const SCHEMA_VERSION = 'producer-normalization-summary/v1';
const REPORT_ONLY_MODE = 'report-only';
const MANIFEST_STATUSES = new Set(['partial', 'satisfied', 'waived', 'unresolved']);
const POLICY_RESULTS = new Set(['pass', 'waived', 'report-only', 'block']);

function readRequiredValue(argv, index, option) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`missing value for ${option}`);
  }
  return next;
}

function parseArgs(argv) {
  const options = {
    input: null,
    outJson: DEFAULT_OUTPUT_JSON_PATH,
    outMd: DEFAULT_OUTPUT_MD_PATH,
    producer: null,
    generatedAt: null,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }

    switch (arg) {
      case '--input':
        options.input = readRequiredValue(argv, index, arg);
        index += 1;
        break;
      case '--out-json':
        options.outJson = readRequiredValue(argv, index, arg);
        index += 1;
        break;
      case '--out-md':
        options.outMd = readRequiredValue(argv, index, arg);
        index += 1;
        break;
      case '--producer':
        options.producer = readRequiredValue(argv, index, arg);
        index += 1;
        break;
      case '--generated-at':
        options.generatedAt = readRequiredValue(argv, index, arg);
        index += 1;
        break;
      case '--help':
      case '-h':
        options.help = true;
        break;
      default:
        throw new Error(`unknown option: ${arg}`);
    }
  }

  return options;
}

function usage() {
  return [
    'Usage: node scripts/agents/normalize-producer-output.mjs --input <fixture.json> [options]',
    '',
    'Options:',
    '  --input <path>       Raw producer-output fixture to summarize. Required.',
    `  --out-json <path>    JSON output path. Default: ${DEFAULT_OUTPUT_JSON_PATH}`,
    `  --out-md <path>      Markdown output path. Default: ${DEFAULT_OUTPUT_MD_PATH}`,
    '  --producer <id>      Override or supply producer id for the summary.',
    '  --generated-at <iso> Deterministic timestamp for tests/fixtures.',
    '  --help              Show this message.',
  ].join('\n');
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function toRepoRelativePath(filePath, cwd = process.cwd()) {
  const resolved = path.resolve(cwd, filePath);
  const relative = path.relative(cwd, resolved).replaceAll(path.sep, '/');
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    return filePath.replaceAll(path.sep, '/');
  }
  return relative;
}

function readJsonRequired(filePath, label) {
  if (!filePath) {
    throw new Error(`${label} path is required`);
  }
  if (!fs.existsSync(filePath)) {
    throw new Error(`${label} not found: ${filePath}`);
  }
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`${label} is invalid JSON: ${filePath} (${message})`);
  }
}

function normalizeText(value) {
  if (typeof value !== 'string') {
    return null;
  }
  const normalized = value.trim();
  return normalized || null;
}

function normalizeStringArray(values) {
  if (!Array.isArray(values)) {
    return [];
  }
  const seen = new Set();
  const result = [];
  for (const value of values) {
    const text = normalizeText(value);
    if (!text || seen.has(text)) {
      continue;
    }
    seen.add(text);
    result.push(text);
  }
  return result;
}

function normalizeObjectArray(values) {
  if (!Array.isArray(values)) {
    return [];
  }
  return values.filter((value) => value && typeof value === 'object' && !Array.isArray(value));
}

function normalizeProducer(fixture, producerOverride = null) {
  const rawProducer = fixture?.producer;
  if (rawProducer && typeof rawProducer === 'object' && !Array.isArray(rawProducer)) {
    const id = normalizeText(producerOverride) ?? normalizeText(rawProducer.id) ?? 'unknown-producer';
    return {
      id,
      fixtureProducerId: normalizeText(rawProducer.id) ?? id,
      displayName: normalizeText(rawProducer.displayName) ?? id,
      category: normalizeText(rawProducer.category) ?? 'unknown',
      trustBoundary: normalizeText(rawProducer.trustBoundary) ?? 'Producer output is untrusted until normalized and reviewed.',
    };
  }

  const producerId = normalizeText(producerOverride) ?? normalizeText(rawProducer) ?? 'unknown-producer';
  return {
    id: producerId,
    fixtureProducerId: normalizeText(rawProducer) ?? producerId,
    displayName: producerId,
    category: 'unknown',
    trustBoundary: 'Producer output is untrusted until normalized and reviewed.',
  };
}

function normalizeExpectedArtifact(entry) {
  const artifact = normalizeText(entry?.artifact) ?? 'unknown-artifact';
  return {
    artifact,
    purpose: normalizeText(entry?.purpose) ?? 'No purpose provided by fixture.',
    requiredForThisFixture: entry?.requiredForThisFixture === true,
  };
}

function normalizeKnownGap(entry) {
  return {
    gapId: normalizeText(entry?.gapId) ?? 'ACP-GAP-UNKNOWN',
    summary: normalizeText(entry?.summary) ?? 'No gap summary provided by fixture.',
  };
}

function commandLooksMissing(command) {
  const status = normalizeText(command?.status)?.toLowerCase() ?? '';
  return /not[-_ ]?run|missing|pending|unavailable|waived-report-only|failed|failure/.test(status);
}

function evidenceListIsMissing(claim) {
  if (!Array.isArray(claim?.supportingEvidence)) {
    return true;
  }
  return normalizeStringArray(claim.supportingEvidence).length === 0;
}

function missingWaiverMetadata(claim) {
  const waiver = claim?.waiver;
  if (!waiver || typeof waiver !== 'object' || Array.isArray(waiver)) {
    return ['waiver'];
  }
  const missing = [];
  for (const field of ['owner', 'reason', 'expiresAt', 'evidence']) {
    if (!normalizeText(waiver[field])) {
      missing.push(`waiver.${field}`);
    }
  }
  return missing;
}

function buildFinding(id, kind, summary, details = {}) {
  return {
    id,
    severity: 'report-only',
    kind,
    summary,
    details,
  };
}

function analyzeFixture({ commands, claimsMentioned, knownGaps, rawSignals }) {
  const reportOnlyFindings = [];
  const missingEvidence = [];
  const unresolvedNotes = [];

  for (const gap of knownGaps) {
    reportOnlyFindings.push(buildFinding(
      `known-gap:${gap.gapId}`,
      'known-gap',
      `${gap.gapId}: ${gap.summary}`,
      { gapId: gap.gapId },
    ));
    unresolvedNotes.push(`${gap.gapId}: ${gap.summary}`);
  }

  for (const signal of rawSignals) {
    const kind = normalizeText(signal?.kind) ?? 'raw-signal';
    const value = normalizeText(signal?.value);
    if (/open-question|risk|unresolved|blocker/i.test(kind) && value) {
      unresolvedNotes.push(value);
    }
  }

  commands.forEach((command, index) => {
    if (!commandLooksMissing(command)) {
      return;
    }
    const commandText = normalizeText(command?.command) ?? `command[${index}]`;
    const status = normalizeText(command?.status) ?? 'missing';
    const summary = `Command evidence is not complete: ${commandText} (${status})`;
    missingEvidence.push({
      kind: 'command',
      summary,
      command: commandText,
    });
    reportOnlyFindings.push(buildFinding(
      `missing-command:${index + 1}`,
      'missing-evidence',
      summary,
      { command: commandText, status },
    ));
  });

  claimsMentioned.forEach((claim, index) => {
    const claimId = normalizeText(claim?.claimId) ?? `claim[${index}]`;
    const targetArtifact = normalizeText(claim?.targetArtifact) ?? 'unknown-artifact';

    if (evidenceListIsMissing(claim)) {
      const summary = `Claim has no supporting evidence list: ${claimId}`;
      missingEvidence.push({
        kind: 'claim-evidence',
        summary,
        claimId,
        artifact: targetArtifact,
      });
      reportOnlyFindings.push(buildFinding(
        `missing-claim-evidence:${index + 1}`,
        'missing-evidence',
        summary,
        { claimId, targetArtifact },
      ));
    }

    if (targetArtifact === 'claim-evidence-manifest/v1') {
      const status = normalizeText(claim?.expectedManifestStatus);
      if (!status || !MANIFEST_STATUSES.has(status)) {
        reportOnlyFindings.push(buildFinding(
          `unsupported-manifest-status:${index + 1}`,
          'unsupported-claim',
          `Claim ${claimId} does not use claim-evidence-manifest/v1 status vocabulary.`,
          { claimId, targetArtifact, expectedManifestStatus: status },
        ));
      }
      if (status === 'waived') {
        const missingFields = missingWaiverMetadata(claim);
        if (missingFields.length > 0) {
          const summary = `Waiver metadata is incomplete for claim ${claimId}: ${missingFields.join(', ')}`;
          missingEvidence.push({
            kind: 'waiver-metadata',
            summary,
            claimId,
            artifact: targetArtifact,
          });
          reportOnlyFindings.push(buildFinding(
            `missing-waiver-metadata:${index + 1}`,
            'waiver-metadata',
            summary,
            { claimId, targetArtifact, missingFields },
          ));
        }
      }
    } else if (targetArtifact === 'policy-decision/v1') {
      const result = normalizeText(claim?.expectedPolicyResult);
      if (!result || !POLICY_RESULTS.has(result)) {
        reportOnlyFindings.push(buildFinding(
          `unsupported-policy-result:${index + 1}`,
          'unsupported-claim',
          `Claim ${claimId} does not use policy-decision/v1 result vocabulary.`,
          { claimId, targetArtifact, expectedPolicyResult: result },
        ));
      }
      if (result === 'waived') {
        const missingFields = missingWaiverMetadata(claim);
        if (missingFields.length > 0) {
          const summary = `Policy waiver metadata is incomplete for claim ${claimId}: ${missingFields.join(', ')}`;
          missingEvidence.push({
            kind: 'waiver-metadata',
            summary,
            claimId,
            artifact: targetArtifact,
          });
          reportOnlyFindings.push(buildFinding(
            `missing-policy-waiver-metadata:${index + 1}`,
            'waiver-metadata',
            summary,
            { claimId, targetArtifact, missingFields },
          ));
        }
      }
    } else {
      reportOnlyFindings.push(buildFinding(
        `unsupported-target-artifact:${index + 1}`,
        'unsupported-claim',
        `Claim ${claimId} targets ${targetArtifact}; no report-only skeleton route is defined yet.`,
        { claimId, targetArtifact },
      ));
    }
  });

  return {
    reportOnlyFindings,
    missingEvidence,
    unresolvedNotes: normalizeStringArray(unresolvedNotes),
  };
}

export function buildNormalizationSummary(fixture, options = {}) {
  const generatedAt = normalizeText(options.generatedAt) ?? new Date().toISOString();
  const inputPath = normalizeText(options.inputPath) ?? 'unknown-input';
  const producer = normalizeProducer(fixture, options.producer ?? null);
  const rawSignals = normalizeObjectArray(fixture?.rawSignals);
  const changedFiles = normalizeObjectArray(fixture?.changedFiles);
  const commands = normalizeObjectArray(fixture?.commands);
  const claimsMentioned = normalizeObjectArray(fixture?.claimsMentioned);
  const expectedArtifacts = normalizeObjectArray(fixture?.expectedArtifacts).map(normalizeExpectedArtifact);
  const knownGaps = normalizeObjectArray(fixture?.knownGaps).map(normalizeKnownGap);
  const analysis = analyzeFixture({ commands, claimsMentioned, knownGaps, rawSignals });

  return {
    schemaVersion: SCHEMA_VERSION,
    generatedAt,
    mode: REPORT_ONLY_MODE,
    input: {
      path: inputPath,
      producerOverride: normalizeText(options.producer) ?? null,
    },
    producer,
    source: fixture?.source && typeof fixture.source === 'object' && !Array.isArray(fixture.source)
      ? fixture.source
      : {},
    summary: {
      rawSignals: rawSignals.length,
      changedFiles: changedFiles.length,
      commands: commands.length,
      claimsMentioned: claimsMentioned.length,
      expectedArtifacts: expectedArtifacts.length,
      knownGaps: knownGaps.length,
      missingEvidence: analysis.missingEvidence.length,
      reportOnlyFindings: analysis.reportOnlyFindings.length,
    },
    producerAssertions: {
      rawSignals,
      changedFiles,
      commands,
      claimsMentioned,
    },
    controlPlaneRouting: {
      expectedArtifacts,
      knownGaps,
      missingEvidence: analysis.missingEvidence,
      unresolvedNotes: analysis.unresolvedNotes,
      reportOnlyFindings: analysis.reportOnlyFindings,
    },
    controlPlaneJudgment: {
      emitsDecision: false,
      result: 'not-emitted',
      reason: 'Report-only normalization summarizes raw producer output and routing gaps; it does not decide pass, proved, or approved status.',
    },
  };
}

function formatList(items, formatItem) {
  if (!items.length) {
    return '- None\n';
  }
  return items.map(formatItem).join('\n') + '\n';
}

function renderMarkdown(summary) {
  const lines = [];
  lines.push('# Producer Normalization Summary');
  lines.push('');
  lines.push('> Report-only: this summary does not approve, prove, or pass the producer output.');
  lines.push('');
  lines.push(`- Schema: \`${summary.schemaVersion}\``);
  lines.push(`- Generated at: \`${summary.generatedAt}\``);
  lines.push(`- Input: \`${summary.input.path}\``);
  lines.push(`- Producer: \`${summary.producer.id}\` (${summary.producer.displayName})`);
  lines.push(`- Mode: \`${summary.mode}\``);
  lines.push(`- Control-plane decision emitted: \`${summary.controlPlaneJudgment.emitsDecision}\``);
  lines.push('');
  lines.push('## Expected artifact routing');
  lines.push('');
  lines.push(formatList(summary.controlPlaneRouting.expectedArtifacts, (entry) => (
    `- \`${entry.artifact}\` — ${entry.purpose}`
  )).trimEnd());
  lines.push('');
  lines.push('## Missing evidence');
  lines.push('');
  lines.push(formatList(summary.controlPlaneRouting.missingEvidence, (entry) => (
    `- **${entry.kind}**: ${entry.summary}`
  )).trimEnd());
  lines.push('');
  lines.push('## Report-only findings');
  lines.push('');
  lines.push(formatList(summary.controlPlaneRouting.reportOnlyFindings, (entry) => (
    `- \`${entry.id}\` (${entry.kind}): ${entry.summary}`
  )).trimEnd());
  lines.push('');
  lines.push('## Claims mentioned by producer');
  lines.push('');
  lines.push(formatList(summary.producerAssertions.claimsMentioned, (claim) => {
    const claimId = normalizeText(claim.claimId) ?? 'unknown-claim';
    const targetArtifact = normalizeText(claim.targetArtifact) ?? 'unknown-artifact';
    return `- \`${claimId}\` → \`${targetArtifact}\``;
  }).trimEnd());
  lines.push('');
  lines.push('## Unresolved notes');
  lines.push('');
  lines.push(formatList(summary.controlPlaneRouting.unresolvedNotes, (note) => `- ${note}`).trimEnd());
  lines.push('');
  return `${lines.join('\n')}\n`;
}

export { renderMarkdown, parseArgs };

function runCli() {
  const options = parseArgs(process.argv.slice(2));
  if (options.help) {
    console.log(usage());
    return;
  }
  if (!options.input) {
    throw new Error('--input is required');
  }

  const fixture = readJsonRequired(options.input, 'producer fixture');
  const summary = buildNormalizationSummary(fixture, {
    inputPath: toRepoRelativePath(options.input),
    producer: options.producer,
    generatedAt: options.generatedAt,
  });

  ensureParentDir(options.outJson);
  fs.writeFileSync(options.outJson, `${JSON.stringify(summary, null, 2)}\n`);

  ensureParentDir(options.outMd);
  fs.writeFileSync(options.outMd, renderMarkdown(summary));

  console.log(`Producer normalization summary written: ${options.outJson}`);
  console.log(`Producer normalization markdown written: ${options.outMd}`);
}

const invokedScriptPath = process.argv[1] ? path.resolve(process.argv[1]) : null;

if (invokedScriptPath === fileURLToPath(import.meta.url)) {
  try {
    runCli();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error(`normalize-producer-output: ${message}`);
    process.exit(1);
  }
}
