#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import { DEFAULT_POLICY_PATH, getMinHumanApprovals, getRiskLabels, loadRiskPolicy } from '../ci/lib/risk-policy.mjs';

const __filename = fileURLToPath(import.meta.url);
const DEFAULT_INPUT_PATH = 'artifacts/plan/plan-artifact.input.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/plan/plan-artifact.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/plan/plan-artifact.md';

function parseArgs(argv = process.argv) {
  const options = {
    inputPath: DEFAULT_INPUT_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    policyPath: DEFAULT_POLICY_PATH,
    repository: '',
    prNumber: null,
    baseRef: '',
    headRef: '',
    eventPath: process.env.GITHUB_EVENT_PATH || '',
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    const readValue = (name) => {
      if (!next || next.startsWith('-')) {
        throw new Error(`missing value for ${name}`);
      }
      index += 1;
      return next;
    };

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--input') {
      options.inputPath = readValue('--input');
      continue;
    }
    if (arg.startsWith('--input=')) {
      options.inputPath = arg.slice('--input='.length);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readValue('--output-json');
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue('--output-md');
      continue;
    }
    if (arg.startsWith('--output-md=')) {
      options.outputMarkdownPath = arg.slice('--output-md='.length);
      continue;
    }
    if (arg === '--policy') {
      options.policyPath = readValue('--policy');
      continue;
    }
    if (arg.startsWith('--policy=')) {
      options.policyPath = arg.slice('--policy='.length);
      continue;
    }
    if (arg === '--repo') {
      options.repository = readValue('--repo');
      continue;
    }
    if (arg.startsWith('--repo=')) {
      options.repository = arg.slice('--repo='.length);
      continue;
    }
    if (arg === '--pr') {
      options.prNumber = Number(readValue('--pr'));
      continue;
    }
    if (arg.startsWith('--pr=')) {
      options.prNumber = Number(arg.slice('--pr='.length));
      continue;
    }
    if (arg === '--base-ref') {
      options.baseRef = readValue('--base-ref');
      continue;
    }
    if (arg.startsWith('--base-ref=')) {
      options.baseRef = arg.slice('--base-ref='.length);
      continue;
    }
    if (arg === '--head-ref') {
      options.headRef = readValue('--head-ref');
      continue;
    }
    if (arg.startsWith('--head-ref=')) {
      options.headRef = arg.slice('--head-ref='.length);
      continue;
    }
    if (arg === '--event-path') {
      options.eventPath = readValue('--event-path');
      continue;
    }
    if (arg.startsWith('--event-path=')) {
      options.eventPath = arg.slice('--event-path='.length);
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(
    'Plan Artifact generator\n\n'
      + 'Usage:\n'
      + '  node scripts/plan-artifact/generate.mjs [options]\n\n'
      + 'Options:\n'
      + `  --input <path>                input JSON (default: ${DEFAULT_INPUT_PATH})\n`
      + `  --output-json <path>          output JSON (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
      + `  --output-md <path>            output Markdown (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
      + `  --policy <path>               risk policy path (default: ${DEFAULT_POLICY_PATH})\n`
      + '  --repo <owner/repo>           repository override\n'
      + '  --pr <number>                 PR number override\n'
      + '  --base-ref <ref>              base branch override\n'
      + '  --head-ref <ref>              head branch override\n'
      + '  --event-path <path>           GitHub event payload path override\n'
      + '  --help, -h                    show help\n',
  );
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonFile(filePath) {
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`file not found: ${resolved}`);
  }
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

function readEventPayload(eventPath) {
  if (!eventPath) return null;
  const resolved = path.resolve(eventPath);
  if (!fs.existsSync(resolved)) return null;
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

function resolveSource(options, input) {
  const payload = readEventPayload(options.eventPath);
  const inputSource = input?.source && typeof input.source === 'object' ? input.source : {};
  const repository = String(
    options.repository
      || inputSource.repository
      || payload?.repository?.full_name
      || process.env.GITHUB_REPOSITORY
      || '',
  ).trim();
  const prNumber = Number(
    options.prNumber
      || inputSource.prNumber
      || payload?.pull_request?.number
      || process.env.PR_NUMBER
      || 0,
  );
  const baseRef = String(
    options.baseRef
      || inputSource.baseRef
      || payload?.pull_request?.base?.ref
      || process.env.GITHUB_BASE_REF
      || '',
  ).trim();
  const headRef = String(
    options.headRef
      || inputSource.headRef
      || payload?.pull_request?.head?.ref
      || process.env.GITHUB_HEAD_REF
      || '',
  ).trim();

  if (!repository) throw new Error('repository is required');
  if (!Number.isFinite(prNumber) || prNumber < 1) throw new Error('prNumber is required');
  if (!baseRef) throw new Error('baseRef is required');
  if (!headRef) throw new Error('headRef is required');

  return {
    repository,
    prNumber: Math.trunc(prNumber),
    baseRef,
    headRef,
  };
}

function normalizeNamedText(values, prefix) {
  if (!Array.isArray(values) || values.length === 0) {
    throw new Error(`${prefix} must contain at least one item`);
  }
  return values.map((entry, index) => {
    if (typeof entry === 'string') {
      const text = entry.trim();
      if (!text) throw new Error(`${prefix}[${index}] must be non-empty`);
      return { id: `${prefix.toUpperCase()}${index + 1}`, text };
    }
    if (!entry || typeof entry !== 'object') {
      throw new Error(`${prefix}[${index}] must be an object or string`);
    }
    const id = String(entry.id || `${prefix.toUpperCase()}${index + 1}`).trim();
    const text = String(entry.text || '').trim();
    if (!id || !text) throw new Error(`${prefix}[${index}] must include id and text`);
    return { id, text };
  });
}

function normalizeVerificationPlan(values) {
  if (!Array.isArray(values) || values.length === 0) {
    throw new Error('verificationPlan must contain at least one step');
  }
  return values.map((entry, index) => {
    if (!entry || typeof entry !== 'object') {
      throw new Error(`verificationPlan[${index}] must be an object`);
    }
    const id = String(entry.id || `V${index + 1}`).trim();
    const name = String(entry.name || '').trim();
    const command = String(entry.command || '').trim();
    const expectedEvidence = Array.isArray(entry.expectedEvidence)
      ? [...new Set(entry.expectedEvidence.map((item) => String(item || '').trim()).filter(Boolean))]
      : [];
    if (!id || !name || !command) {
      throw new Error(`verificationPlan[${index}] must include id, name, and command`);
    }
    return { id, name, command, expectedEvidence };
  });
}

function normalizeFilesExpected(values) {
  if (!Array.isArray(values) || values.length === 0) {
    throw new Error('filesExpectedToChange must contain at least one path');
  }
  const normalized = [...new Set(values.map((item) => String(item || '').trim()).filter(Boolean))];
  if (normalized.length === 0) {
    throw new Error('filesExpectedToChange must contain at least one path');
  }
  return normalized;
}

function normalizeStringArray(values) {
  if (!Array.isArray(values)) return [];
  return [...new Set(values.map((item) => String(item || '').trim()).filter(Boolean))];
}

function requireTrimmedString(value, fieldName) {
  const normalized = String(value || '').trim();
  if (!normalized) {
    throw new Error(`${fieldName} is required and must be non-empty`);
  }
  return normalized;
}

function buildPlanArtifact(options) {
  const input = readJsonFile(options.inputPath);
  const policy = loadRiskPolicy(options.policyPath);
  const riskLabels = getRiskLabels(policy);
  const selectedRisk = String(input?.risk?.selected || '').trim();
  if (selectedRisk !== riskLabels.low && selectedRisk !== riskLabels.high) {
    throw new Error(`risk.selected must be ${riskLabels.low} or ${riskLabels.high}`);
  }
  const minHumanApprovals = selectedRisk === riskLabels.high ? getMinHumanApprovals(policy) : 0;
  return {
    schemaVersion: 'plan-artifact/v1',
    contractId: 'plan-artifact.v1',
    generatedAt: new Date().toISOString(),
    source: resolveSource(options, input),
    goal: requireTrimmedString(input?.goal, 'goal'),
    scope: requireTrimmedString(input?.scope, 'scope'),
    risk: {
      selected: selectedRisk,
      requiresHumanApproval: minHumanApprovals > 0,
      minHumanApprovals,
    },
    assumptions: normalizeNamedText(input?.assumptions, 'A'),
    filesExpectedToChange: normalizeFilesExpected(input?.filesExpectedToChange),
    verificationPlan: normalizeVerificationPlan(input?.verificationPlan),
    rollbackPlan: requireTrimmedString(input?.rollbackPlan, 'rollbackPlan'),
    requiredHumanInput: normalizeStringArray(input?.requiredHumanInput),
    notes: normalizeStringArray(input?.notes),
  };
}

function renderMarkdown(planArtifact) {
  const lines = [
    '## Plan Artifact',
    '',
    `- goal: ${planArtifact.goal}`,
    `- scope: ${planArtifact.scope}`,
    `- risk: ${planArtifact.risk.selected}`,
    `- approvals required: ${planArtifact.risk.minHumanApprovals}`,
    `- source: ${planArtifact.source.repository}#${planArtifact.source.prNumber} (${planArtifact.source.baseRef} <- ${planArtifact.source.headRef})`,
    '',
    '### Assumptions',
    '',
    ...planArtifact.assumptions.map((item) => `- ${item.id}: ${item.text}`),
    '',
    '### Files expected to change',
    '',
    ...planArtifact.filesExpectedToChange.map((item) => `- \`${item}\``),
    '',
    '### Verification plan',
    '',
  ];
  for (const item of planArtifact.verificationPlan) {
    lines.push(`- ${item.id}: ${item.name}`);
    lines.push(`  - command: \`${item.command}\``);
    if (item.expectedEvidence.length > 0) {
      lines.push(`  - expected evidence: ${item.expectedEvidence.map((entry) => `\`${entry}\``).join(', ')}`);
    }
  }
  lines.push('', '### Rollback plan', '', planArtifact.rollbackPlan, '');
  if (planArtifact.requiredHumanInput.length > 0) {
    lines.push('### Required human input', '', ...planArtifact.requiredHumanInput.map((item) => `- ${item}`), '');
  }
  if (planArtifact.notes.length > 0) {
    lines.push('### Notes', '', ...planArtifact.notes.map((item) => `- ${item}`), '');
  }
  return `${lines.join('\n')}\n`;
}

export { buildPlanArtifact, parseArgs, renderMarkdown };

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }
  const planArtifact = buildPlanArtifact(options);
  const markdown = renderMarkdown(planArtifact);

  ensureDirectory(options.outputJsonPath);
  fs.writeFileSync(path.resolve(options.outputJsonPath), `${JSON.stringify(planArtifact, null, 2)}\n`);
  ensureDirectory(options.outputMarkdownPath);
  fs.writeFileSync(path.resolve(options.outputMarkdownPath), markdown);
  process.stdout.write(`Generated ${options.outputJsonPath} and ${options.outputMarkdownPath}\n`);
  return 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  try {
    process.exit(main(process.argv));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[plan-artifact:generate] ${message}\n`);
    process.exit(1);
  }
}
