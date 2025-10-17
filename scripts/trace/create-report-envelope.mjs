#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fromVerifyLite } from '@ae-framework/envelope';

const summaryPath = process.argv[2] ?? process.env.REPORT_ENVELOPE_SUMMARY ?? 'artifacts/verify-lite/verify-lite-run-summary.json';
const outputPath = process.argv[3] ?? process.env.REPORT_ENVELOPE_OUTPUT ?? 'artifacts/report-envelope.json';
const source = process.env.REPORT_ENVELOPE_SOURCE ?? 'verify-lite';
const noteEnv = process.env.REPORT_ENVELOPE_NOTES ?? '';

const ensureFile = (filePath) => {
  if (!fs.existsSync(filePath)) {
    console.error(`[report-envelope] summary not found: ${filePath}`);
    process.exit(1);
  }
};

ensureFile(summaryPath);

const readJson = (filePath) => {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    console.error(`[report-envelope] failed to parse ${filePath}:`, error);
    process.exit(1);
  }
};

const summary = readJson(summaryPath);
const now = new Date().toISOString();
const workflow = process.env.GITHUB_WORKFLOW ?? process.env.GITHUB_JOB ?? 'local-run';
const branch = process.env.GITHUB_REF ?? 'local';
const runId = process.env.GITHUB_RUN_ID ?? `local-${Date.now()}`;
const commit = process.env.GITHUB_SHA ?? '0000000';

const derivedTraceIds = Array.isArray(summary?.trace?.traceIds)
  ? summary.trace.traceIds.map((value) => (typeof value === 'string' ? value.trim() : '')).filter(Boolean)
  : [];

const traceIdsEnv = process.env.REPORT_ENVELOPE_TRACE_IDS ?? '';
const traceIdsSeed = traceIdsEnv
  .split(',')
  .map((value) => value.trim())
  .filter(Boolean);

const notesSeed = noteEnv
  .split(/\r?\n/)
  .map((value) => value.trim())
  .filter(Boolean);

const envelope = fromVerifyLite(summary, {
  source,
  generatedAt: now,
  correlation: {
    runId,
    workflow,
    commit,
    branch,
    traceIds: [...derivedTraceIds, ...traceIdsSeed],
  },
  tempoLinkTemplate: process.env.REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE,
  notes: notesSeed,
});

const correlation = envelope.traceCorrelation;
if (correlation) {
  envelope.correlation = correlation;
}

// Preserve the original summary structure for compatibility with downstream consumers
envelope.summary = summary;

const computeChecksum = (buffer) => `sha256:${crypto.createHash('sha256').update(buffer).digest('hex')}`;

const artifactsByPath = new Map();
const registerArtifact = (artifact) => {
  if (!artifact || typeof artifact.path !== 'string' || !artifact.path.trim()) {
    return;
  }
  const resolved = path.resolve(artifact.path);
  const record = {
    type: artifact.type ?? 'application/json',
    description: artifact.description ?? null,
  };
  if (fs.existsSync(resolved)) {
    const buffer = fs.readFileSync(resolved);
    record.path = path.relative(process.cwd(), resolved);
    record.checksum = computeChecksum(buffer);
    artifactsByPath.set(resolved, record);
  } else {
    record.path = artifact.path;
    artifactsByPath.set(artifact.path, record);
  }
};

const existingArtifacts = Array.isArray(envelope.artifacts) ? envelope.artifacts : [];
for (const artifact of existingArtifacts) {
  registerArtifact(artifact);
}

const pushArtifact = (filePath, { type = 'application/json', description = null } = {}) => {
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    console.warn(`[report-envelope] artifact not found, skipping: ${filePath}`);
    return;
  }
  const buffer = fs.readFileSync(resolved);
  registerArtifact({
    type,
    path: path.relative(process.cwd(), resolved),
    checksum: computeChecksum(buffer),
    ...(description ? { description } : {}),
  });
};

pushArtifact(summaryPath, { description: 'Raw summary artifact' });

const payloadMetadataPath = process.env.REPORT_ENVELOPE_PAYLOAD_METADATA;
if (payloadMetadataPath) {
  pushArtifact(payloadMetadataPath, { description: 'Payload metadata' });
}

const extraArtifactsEnv = process.env.REPORT_ENVELOPE_EXTRA_ARTIFACTS ?? '';
const extraArtifacts = extraArtifactsEnv
  .split(',')
  .map((value) => value.trim())
  .filter(Boolean);

for (const artifactPath of extraArtifacts) {
  pushArtifact(artifactPath, {});
}

envelope.artifacts = Array.from(artifactsByPath.values());

const destDir = path.dirname(outputPath);
if (!fs.existsSync(destDir)) {
  fs.mkdirSync(destDir, { recursive: true });
}

fs.writeFileSync(outputPath, JSON.stringify(envelope, null, 2));
console.log(`[report-envelope] wrote envelope to ${outputPath}`);
