import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';

export const ARTIFACT_PROVENANCE_SCHEMA_VERSION = 'ci-artifact-provenance/v1';

const HEX_SHA_RE = /^[0-9a-f]{64}$/;

export function normalizeSubjectPath(subjectPath) {
  const raw = String(subjectPath ?? '').trim();
  if (!raw) {
    throw new Error('subject path must not be empty');
  }
  if (path.isAbsolute(raw)) {
    throw new Error(`subject path must be repository-relative: ${raw}`);
  }
  const normalized = path.posix.normalize(raw.replace(/\\/g, '/'));
  if (normalized === '.' || normalized === '..' || normalized.startsWith('../') || normalized.includes('/../')) {
    throw new Error(`subject path must stay within the artifact root: ${raw}`);
  }
  return normalized;
}

export function sha256File(filePath) {
  const hash = crypto.createHash('sha256');
  hash.update(fs.readFileSync(filePath));
  return hash.digest('hex');
}

function readJsonOptional(filePath) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch {
    return undefined;
  }
}

function parsePullRequestEvent(env = process.env) {
  const eventPath = env.GITHUB_EVENT_PATH;
  const event = eventPath ? readJsonOptional(eventPath) : undefined;
  const pr = event?.pull_request;
  return {
    prNumber: pr?.number ?? null,
    headSha: typeof pr?.head?.sha === 'string' ? pr.head.sha : (env.GITHUB_SHA || ''),
    baseSha: typeof pr?.base?.sha === 'string' ? pr.base.sha : '',
    headRepository: typeof pr?.head?.repo?.full_name === 'string' ? pr.head.repo.full_name : '',
    baseRepository: typeof pr?.base?.repo?.full_name === 'string' ? pr.base.repo.full_name : '',
  };
}

export function collectSubjects({ root = '.', subjects = [] } = {}) {
  const rootDir = path.resolve(root);
  return subjects.map((subject) => {
    const normalized = normalizeSubjectPath(subject);
    const fullPath = path.resolve(rootDir, normalized);
    const relative = path.relative(rootDir, fullPath);
    if (relative.startsWith('..') || path.isAbsolute(relative)) {
      throw new Error(`subject path escapes artifact root: ${subject}`);
    }
    const stat = fs.statSync(fullPath);
    if (!stat.isFile()) {
      throw new Error(`subject path is not a regular file: ${normalized}`);
    }
    return {
      path: normalized,
      sha256: sha256File(fullPath),
      size: stat.size,
    };
  });
}

export function buildArtifactProvenance({
  artifactName,
  root = '.',
  subjects = [],
  env = process.env,
  generatedAt = new Date().toISOString(),
} = {}) {
  const name = String(artifactName ?? '').trim();
  if (!name) {
    throw new Error('artifactName is required');
  }
  const collectedSubjects = collectSubjects({ root, subjects });
  if (!collectedSubjects.length) {
    throw new Error('at least one subject is required');
  }
  const pr = parsePullRequestEvent(env);
  return {
    schemaVersion: ARTIFACT_PROVENANCE_SCHEMA_VERSION,
    generatedAt,
    artifact: {
      name,
      subjects: collectedSubjects,
    },
    producer: {
      repository: env.GITHUB_REPOSITORY || '',
      workflow: env.GITHUB_WORKFLOW || '',
      workflowRef: env.GITHUB_WORKFLOW_REF || '',
      runId: String(env.GITHUB_RUN_ID || ''),
      runAttempt: String(env.GITHUB_RUN_ATTEMPT || ''),
      eventName: env.GITHUB_EVENT_NAME || '',
      headSha: pr.headSha || '',
      baseSha: pr.baseSha || '',
      prNumber: pr.prNumber,
      headRepository: pr.headRepository,
      baseRepository: pr.baseRepository,
    },
  };
}

function maybeCompare(errors, label, actual, expected) {
  const exp = String(expected ?? '').trim();
  if (!exp) return;
  const act = String(actual ?? '').trim();
  if (act !== exp) {
    errors.push(`${label} mismatch: expected ${JSON.stringify(exp)}, actual ${JSON.stringify(act)}`);
  }
}

export function validateArtifactProvenance({
  provenance,
  root = '.',
  expected = {},
  requireSubjects = [],
} = {}) {
  const errors = [];
  if (!provenance || typeof provenance !== 'object') {
    return ['provenance must be a JSON object'];
  }
  if (provenance.schemaVersion !== ARTIFACT_PROVENANCE_SCHEMA_VERSION) {
    errors.push(`schemaVersion mismatch: expected ${ARTIFACT_PROVENANCE_SCHEMA_VERSION}, actual ${JSON.stringify(provenance.schemaVersion)}`);
  }
  const artifact = provenance.artifact;
  const producer = provenance.producer;
  if (!artifact || typeof artifact !== 'object') {
    errors.push('artifact object is required');
  }
  if (!producer || typeof producer !== 'object') {
    errors.push('producer object is required');
  }
  if (artifact && typeof artifact === 'object') {
    maybeCompare(errors, 'artifact.name', artifact.name, expected.artifactName);
  }
  if (producer && typeof producer === 'object') {
    maybeCompare(errors, 'producer.repository', producer.repository, expected.repository);
    maybeCompare(errors, 'producer.workflow', producer.workflow, expected.workflow);
    maybeCompare(errors, 'producer.workflowRef', producer.workflowRef, expected.workflowRef);
    maybeCompare(errors, 'producer.runId', producer.runId, expected.runId);
    maybeCompare(errors, 'producer.runAttempt', producer.runAttempt, expected.runAttempt);
    maybeCompare(errors, 'producer.eventName', producer.eventName, expected.eventName);
    maybeCompare(errors, 'producer.headSha', producer.headSha, expected.headSha);
    maybeCompare(errors, 'producer.baseSha', producer.baseSha, expected.baseSha);
    if (String(expected.prNumber ?? '').trim()) {
      const actualPr = producer.prNumber == null ? '' : String(producer.prNumber);
      maybeCompare(errors, 'producer.prNumber', actualPr, expected.prNumber);
    }
  }

  const subjects = Array.isArray(artifact?.subjects) ? artifact.subjects : [];
  if (!subjects.length) {
    errors.push('artifact.subjects must contain at least one subject');
  }
  const seen = new Set();
  const rootDir = path.resolve(root);
  for (const subject of subjects) {
    if (!subject || typeof subject !== 'object') {
      errors.push('artifact subject must be an object');
      continue;
    }
    let normalized;
    try {
      normalized = normalizeSubjectPath(subject.path);
    } catch (error) {
      errors.push(error instanceof Error ? error.message : String(error));
      continue;
    }
    if (seen.has(normalized)) {
      errors.push(`duplicate subject path: ${normalized}`);
      continue;
    }
    seen.add(normalized);
    if (subject.path !== normalized) {
      errors.push(`subject path is not normalized: ${JSON.stringify(subject.path)} -> ${normalized}`);
    }
    if (typeof subject.sha256 !== 'string' || !HEX_SHA_RE.test(subject.sha256)) {
      errors.push(`subject ${normalized} has invalid sha256`);
      continue;
    }
    const fullPath = path.resolve(rootDir, normalized);
    const relative = path.relative(rootDir, fullPath);
    if (relative.startsWith('..') || path.isAbsolute(relative)) {
      errors.push(`subject path escapes artifact root: ${normalized}`);
      continue;
    }
    if (!fs.existsSync(fullPath)) {
      errors.push(`subject file is missing: ${normalized}`);
      continue;
    }
    const stat = fs.statSync(fullPath);
    if (!stat.isFile()) {
      errors.push(`subject file is not a regular file: ${normalized}`);
      continue;
    }
    const actualSha = sha256File(fullPath);
    if (actualSha !== subject.sha256) {
      errors.push(`subject ${normalized} sha256 mismatch: expected ${subject.sha256}, actual ${actualSha}`);
    }
    if (typeof subject.size === 'number' && stat.size !== subject.size) {
      errors.push(`subject ${normalized} size mismatch: expected ${subject.size}, actual ${stat.size}`);
    }
  }

  for (const required of requireSubjects) {
    let normalized;
    try {
      normalized = normalizeSubjectPath(required);
    } catch (error) {
      errors.push(error instanceof Error ? error.message : String(error));
      continue;
    }
    if (!seen.has(normalized)) {
      errors.push(`required subject missing from provenance: ${normalized}`);
    }
  }

  return errors;
}
