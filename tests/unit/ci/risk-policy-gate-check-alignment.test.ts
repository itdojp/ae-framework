import fs from 'node:fs';
import path from 'node:path';
import micromatch from 'micromatch';
import { describe, expect, it } from 'vitest';
import yaml from 'js-yaml';
import {
  getGateCheckPatternsForLabel,
  getRequiredChecks,
  loadRiskPolicy,
} from '../../../scripts/ci/lib/risk-policy.mjs';

type WorkflowJob = {
  name?: unknown;
  uses?: unknown;
  strategy?: {
    matrix?: Record<string, unknown>;
  };
};

type WorkflowDocument = {
  on?: unknown;
  jobs?: Record<string, WorkflowJob>;
};

const WORKFLOW_DIR = path.resolve(process.cwd(), '.github/workflows');
const MATRIX_KEY_PATTERN = /\${{\s*matrix\.([A-Za-z0-9_-]+)\s*}}/g;

function listWorkflowFiles() {
  return fs.readdirSync(WORKFLOW_DIR)
    .filter((file) => /\.(?:ya?ml)$/i.test(file))
    .sort();
}

function parseWorkflow(fileName: string) {
  const filePath = path.resolve(WORKFLOW_DIR, fileName);
  const raw = fs.readFileSync(filePath, 'utf8');
  const parsed = yaml.load(raw) as WorkflowDocument;
  return { raw, parsed };
}

function listWorkflowTriggers(workflowOn: unknown): string[] {
  if (typeof workflowOn === 'string') return [workflowOn];
  if (Array.isArray(workflowOn)) {
    return workflowOn
      .filter((entry): entry is string => typeof entry === 'string')
      .map((entry) => entry.trim())
      .filter(Boolean);
  }
  if (workflowOn && typeof workflowOn === 'object') {
    return Object.keys(workflowOn);
  }
  return [];
}

function isWorkflowCallOnly(parsed: WorkflowDocument | undefined) {
  const triggers = listWorkflowTriggers(parsed?.on);
  return triggers.length > 0 && triggers.every((trigger) => trigger === 'workflow_call');
}

function normalizeString(value: unknown) {
  return String(value ?? '').trim();
}

function normalizeUniqueStrings(values: unknown[]) {
  return [...new Set(values.map(normalizeString).filter(Boolean))];
}

function resolveMatrixValues(job: WorkflowJob, key: string) {
  const matrix = job?.strategy?.matrix;
  if (!matrix || typeof matrix !== 'object') return [];
  const direct = Array.isArray(matrix[key]) ? matrix[key] : [];
  const include = Array.isArray(matrix.include)
    ? matrix.include
      .map((item) => (
        item && typeof item === 'object'
          ? (item as Record<string, unknown>)[key]
          : undefined
      ))
      .filter((item) => item !== undefined)
    : [];
  return normalizeUniqueStrings([...direct, ...include]);
}

function extractMatrixKeys(template: string) {
  return normalizeUniqueStrings([...template.matchAll(MATRIX_KEY_PATTERN)].map((match) => match[1]));
}

function escapeRegExp(value: string) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function expandMatrixTemplate(template: string, job: WorkflowJob) {
  const keys = extractMatrixKeys(template);
  if (keys.length === 0) return [template];

  let names = [template];
  for (const key of keys) {
    const values = resolveMatrixValues(job, key);
    if (values.length === 0) continue;
    const pattern = new RegExp(`\\$\\{\\{\\s*matrix\\.${escapeRegExp(key)}\\s*\\}\\}`, 'g');
    names = names.flatMap((name) => values.map((value) => name.replace(pattern, value)));
  }
  return normalizeUniqueStrings(names);
}

function resolveJobDisplayNames(jobId: string, job: WorkflowJob) {
  const template = normalizeString(job?.name) || normalizeString(jobId);
  if (!template) return [];
  return expandMatrixTemplate(template, job);
}

function resolveLocalReusableWorkflowFile(uses: unknown) {
  const normalized = normalizeString(uses).replace(/^\.\//, '').split('@')[0] ?? '';
  if (!normalized.startsWith('.github/workflows/')) return null;
  return path.basename(normalized);
}

function collectWorkflowCheckNames() {
  const files = listWorkflowFiles();
  const workflows = new Map(
    files.map((file) => [file, parseWorkflow(file)]),
  );

  const directJobNamesByWorkflow = new Map<string, string[]>();
  const checkNames = new Set<string>();

  for (const [file, { parsed }] of workflows) {
    const jobs = parsed?.jobs && typeof parsed.jobs === 'object' ? parsed.jobs : {};
    const names = Object.entries(jobs)
      .flatMap(([jobId, job]) => resolveJobDisplayNames(jobId, job))
      .sort();
    directJobNamesByWorkflow.set(file, names);
    // `on: workflow_call` only workflows do not surface standalone PR checks.
    if (!isWorkflowCallOnly(parsed)) {
      for (const name of names) checkNames.add(name);
    }
  }

  for (const [_, { parsed }] of workflows) {
    const jobs = parsed?.jobs && typeof parsed.jobs === 'object' ? parsed.jobs : {};
    for (const [jobId, job] of Object.entries(jobs)) {
      const calleeFile = resolveLocalReusableWorkflowFile(job?.uses);
      if (!calleeFile) continue;
      const calleeJobNames = directJobNamesByWorkflow.get(calleeFile) || [];
      if (calleeJobNames.length === 0) continue;
      const callerJobNames = resolveJobDisplayNames(jobId, job);
      for (const callerName of callerJobNames) {
        for (const calleeName of calleeJobNames) {
          checkNames.add(`${callerName} / ${calleeName}`);
        }
      }
    }
  }

  for (const { raw } of workflows.values()) {
    for (const match of raw.matchAll(/checkName\s*=\s*['"]([^'"]+)['"]/g)) {
      const checkName = normalizeString(match[1]);
      if (checkName) checkNames.add(checkName);
    }
  }

  return [...checkNames].sort();
}

function isGlobPattern(pattern: string) {
  return /[*?[\]{}()!+@]/.test(pattern);
}

function patternMatchesAnyCheck(checkNames: string[], pattern: string) {
  if (!pattern) return false;
  if (isGlobPattern(pattern)) {
    return checkNames.some((checkName) => micromatch.isMatch(checkName, pattern, { dot: true }));
  }
  return checkNames.includes(pattern);
}

describe('risk-policy gate check alignment', () => {
  const policy = loadRiskPolicy('policy/risk-policy.yml');
  const checkNames = collectWorkflowCheckNames();

  it('required_checks are present in workflow check names', () => {
    const requiredChecks = getRequiredChecks(policy);
    const missing = requiredChecks.filter((checkName) => !checkNames.includes(checkName));
    expect(missing, `missing required_checks: ${missing.join(', ')}`).toEqual([]);
  });

  it('gate_checks patterns match workflow check names', () => {
    const labels = Object.keys(policy?.gate_checks || {}).sort();
    const missing = labels
      .flatMap((label) => getGateCheckPatternsForLabel(policy, label)
        .map((pattern) => ({ label, pattern })))
      .filter(({ pattern }) => !patternMatchesAnyCheck(checkNames, pattern));

    expect(
      missing,
      `unmatched gate_checks patterns: ${missing.map((item) => `${item.label}:${item.pattern}`).join(', ')}`,
    ).toEqual([]);
  });
});
