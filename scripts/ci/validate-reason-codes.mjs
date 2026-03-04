#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import yaml from 'yaml';
import { resolveAutomationReasonCode } from './lib/automation-reason-codes.mjs';
import { resolveReasonCode as resolveAutopilotReasonCode } from './lib/pr-orchestration-contracts.mjs';

const DEFAULT_POLICY_PATH = 'policy/reason-codes.yml';
const VALID_OWNER_HINTS = new Set(['ai', 'human', 'either']);
const REASON_CODE_PATTERN = /^[a-z][a-z0-9_]*(?:\.[a-z][a-z0-9_]*)+$/u;

const AUTOPILOT_REASON_SAMPLES = [
  '',
  'merge conflict',
  'max rounds reached without convergence',
  'draft pr',
  'missing label autopilot:on',
  'already merged',
  'auto-merge enabled',
  'checks healthy, waiting for required checks/merge queue',
  'actionable review task scan truncated (pagination required)',
  'missing policy labels: run-security',
  'auto-label failed: exit=1',
  'policy-label detection failed: timeout',
  'actionable review tasks pending: 2 unresolved',
  'actionable execution failed: 1/2 failed',
  'actionable execution incomplete: 1/2 incomplete',
];

const AUTOMATION_REPORT_SAMPLES = [
  {
    tool: 'pr-self-heal',
    status: 'error',
    reason: 'GITHUB_REPOSITORY is required',
  },
  {
    tool: 'pr-self-heal',
    status: 'error',
    reason: 'GITHUB_REPOSITORY format is invalid',
  },
  {
    tool: 'pr-self-heal',
    status: 'error',
    reason: 'PR_NUMBER is required and must be a positive integer',
  },
  {
    tool: 'copilot-auto-fix',
    status: 'skip',
    reason: 'AE_AUTOMATION_GLOBAL_DISABLE is enabled',
  },
  {
    tool: 'copilot-auto-fix',
    status: 'skip',
    reason: 'copilot-auto-fix is disabled after config resolution',
  },
  {
    tool: 'copilot-review',
    status: 'skip',
    reason: 'github-actions[bot] is not in ai_review_actors/copilot_actors',
  },
  {
    tool: 'pr-self-heal',
    status: 'skip',
    reason: 'no PR targets found',
  },
  {
    tool: 'pr-self-heal',
    status: 'skip',
    reason: 'workflow_run has no associated pull request',
  },
  {
    tool: 'pr-self-heal',
    status: 'skip',
    reason: 'all targets skipped',
  },
  {
    tool: 'pr-self-heal',
    status: 'error',
    reason: '2 target(s) failed',
  },
  {
    tool: 'pr-self-heal',
    status: 'blocked',
    reason: '2 target(s) blocked',
  },
  {
    tool: 'codex-autopilot-lane',
    status: 'blocked',
    reason: 'merge conflict',
  },
  {
    tool: 'codex-autopilot-lane',
    status: 'blocked',
    reason: 'actionable execution failed: 1/2 failed',
  },
  {
    tool: 'codex-autopilot-lane',
    status: 'skip',
    reason: 'already merged',
  },
  {
    tool: 'copilot-auto-fix',
    status: 'blocked',
    reason: 'totally unknown condition',
  },
];

function toNonEmptyString(value, fallback = '') {
  const normalized = String(value ?? '').trim();
  return normalized || fallback;
}

function createViolation(type, message, context = {}) {
  return {
    type,
    message,
    ...context,
  };
}

function parseArgs(argv = process.argv) {
  const options = {
    policyPath: DEFAULT_POLICY_PATH,
    format: 'text',
  };

  for (const arg of argv.slice(2)) {
    if (arg.startsWith('--policy=')) {
      options.policyPath = arg.slice('--policy='.length) || DEFAULT_POLICY_PATH;
      continue;
    }
    if (arg.startsWith('--format=')) {
      const requested = arg.slice('--format='.length);
      if (requested === 'text' || requested === 'json') {
        options.format = requested;
      }
      continue;
    }
    if (!arg.startsWith('-') && options.policyPath === DEFAULT_POLICY_PATH) {
      options.policyPath = arg;
    }
  }

  return options;
}

function validatePolicyShape(parsed, resolvedPolicyPath) {
  const violations = [];
  const registry = parsed && typeof parsed === 'object' ? parsed : {};

  if (!registry || typeof registry !== 'object' || Array.isArray(registry)) {
    violations.push(createViolation('invalid_root', 'policy root must be an object'));
    return {
      violations,
      codeEntries: [],
      registry,
    };
  }

  const schemaVersion = toNonEmptyString(registry.schemaVersion);
  if (!schemaVersion) {
    violations.push(createViolation('missing_schema_version', 'schemaVersion is required'));
  } else if (!/^\d+\.\d+\.\d+$/u.test(schemaVersion)) {
    violations.push(
      createViolation('invalid_schema_version', 'schemaVersion must be semver (x.y.z)', {
        value: schemaVersion,
      }),
    );
  }

  const contractId = toNonEmptyString(registry.contractId);
  if (!contractId) {
    violations.push(createViolation('missing_contract_id', 'contractId is required'));
  }

  const rawCodes = Array.isArray(registry.codes) ? registry.codes : null;
  if (!rawCodes) {
    violations.push(createViolation('missing_codes', 'codes must be an array'));
    return {
      violations,
      codeEntries: [],
      registry,
    };
  }

  const seen = new Map();
  const codeEntries = [];
  for (let index = 0; index < rawCodes.length; index += 1) {
    const rawEntry = rawCodes[index];
    const itemPath = `codes[${index}]`;
    if (!rawEntry || typeof rawEntry !== 'object' || Array.isArray(rawEntry)) {
      violations.push(createViolation('invalid_code_entry', 'code entry must be an object', { itemPath }));
      continue;
    }

    const code = toNonEmptyString(rawEntry.code);
    const title = toNonEmptyString(rawEntry.title);
    const description = toNonEmptyString(rawEntry.description);
    const ownerHint = toNonEmptyString(rawEntry.ownerHint);
    const category = toNonEmptyString(rawEntry.category);

    if (!code) {
      violations.push(createViolation('missing_code', 'code is required', { itemPath }));
    } else {
      if (!REASON_CODE_PATTERN.test(code)) {
        violations.push(
          createViolation('invalid_code_format', 'code must be lowercase dot-separated identifiers', {
            itemPath,
            code,
          }),
        );
      }
      const previous = seen.get(code);
      if (previous) {
        violations.push(
          createViolation('duplicate_code', 'code must be unique', {
            itemPath,
            code,
            duplicateOf: previous,
          }),
        );
      } else {
        seen.set(code, itemPath);
      }
    }

    if (!title) {
      violations.push(createViolation('missing_title', 'title is required', { itemPath, code }));
    }
    if (!description) {
      violations.push(createViolation('missing_description', 'description is required', { itemPath, code }));
    }
    if (!ownerHint) {
      violations.push(createViolation('missing_owner_hint', 'ownerHint is required', { itemPath, code }));
    } else if (!VALID_OWNER_HINTS.has(ownerHint)) {
      violations.push(
        createViolation('invalid_owner_hint', 'ownerHint must be one of ai|human|either', {
          itemPath,
          code,
          value: ownerHint,
        }),
      );
    }
    if (!category) {
      violations.push(createViolation('missing_category', 'category is required', { itemPath, code }));
    }

    codeEntries.push({
      code,
      title,
      description,
      ownerHint,
      category,
      itemPath,
    });
  }

  if (codeEntries.length === 0) {
    violations.push(createViolation('empty_codes', 'codes must contain at least one entry'));
  }

  const registryPath = path.relative(process.cwd(), resolvedPolicyPath) || resolvedPolicyPath;
  for (const entry of codeEntries) {
    if (!entry.code) continue;
    if (!entry.description) {
      violations.push(
        createViolation('invalid_description', 'description must be non-empty', {
          itemPath: entry.itemPath,
          code: entry.code,
          registryPath,
        }),
      );
    }
  }

  return {
    violations,
    codeEntries,
    registry,
  };
}

function collectEmitReasonCodes() {
  const codes = new Set();

  for (const reason of AUTOPILOT_REASON_SAMPLES) {
    const resolved = toNonEmptyString(resolveAutopilotReasonCode(reason));
    if (resolved) {
      codes.add(resolved);
    }
  }

  for (const sample of AUTOMATION_REPORT_SAMPLES) {
    const resolved = toNonEmptyString(resolveAutomationReasonCode(sample));
    if (resolved) {
      codes.add(resolved);
    }
  }

  return [...codes].sort((left, right) => left.localeCompare(right));
}

export function validateReasonCodesPolicy(policyPath = DEFAULT_POLICY_PATH) {
  const resolvedPolicyPath = path.resolve(policyPath);
  const violations = [];

  if (!fs.existsSync(resolvedPolicyPath)) {
    return {
      policyPath: resolvedPolicyPath,
      registryCodes: [],
      emittedCodes: collectEmitReasonCodes(),
      missingEmitCodes: [],
      violations: [
        createViolation('missing_policy_file', `policy file not found: ${resolvedPolicyPath}`),
      ],
    };
  }

  let parsed;
  try {
    parsed = yaml.parse(fs.readFileSync(resolvedPolicyPath, 'utf8'));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error ?? 'unknown parse error');
    return {
      policyPath: resolvedPolicyPath,
      registryCodes: [],
      emittedCodes: collectEmitReasonCodes(),
      missingEmitCodes: [],
      violations: [
        createViolation('invalid_yaml', `failed to parse YAML: ${message}`),
      ],
    };
  }

  const shape = validatePolicyShape(parsed, resolvedPolicyPath);
  violations.push(...shape.violations);

  const registryCodes = shape.codeEntries
    .map((entry) => entry.code)
    .filter(Boolean)
    .sort((left, right) => left.localeCompare(right));
  const registryCodeSet = new Set(registryCodes);

  const emittedCodes = collectEmitReasonCodes();
  const missingEmitCodes = emittedCodes.filter((code) => !registryCodeSet.has(code));
  for (const code of missingEmitCodes) {
    violations.push(
      createViolation('missing_emitted_code', 'reason code emitted by scripts is not registered in policy', {
        code,
      }),
    );
  }

  return {
    policyPath: resolvedPolicyPath,
    registryCodes,
    emittedCodes,
    missingEmitCodes,
    violations,
  };
}

function renderText(result, exitCode) {
  const lines = [];
  lines.push('Reason code registry validation');
  lines.push(`- policy: ${result.policyPath}`);
  lines.push(`- registered codes: ${result.registryCodes.length}`);
  lines.push(`- emitted codes: ${result.emittedCodes.length}`);
  lines.push(`- missing emitted codes: ${result.missingEmitCodes.length}`);
  lines.push(`- violations: ${result.violations.length}`);
  if (result.missingEmitCodes.length > 0) {
    lines.push(`- missing list: ${result.missingEmitCodes.join(', ')}`);
  }
  if (result.violations.length > 0) {
    lines.push('');
    lines.push('Violations:');
    for (const violation of result.violations) {
      const codeLabel = violation.code ? ` [${violation.code}]` : '';
      const itemPath = violation.itemPath ? ` @${violation.itemPath}` : '';
      lines.push(`- ${violation.type}${codeLabel}${itemPath}: ${violation.message}`);
    }
  }
  lines.push(`- exitCode: ${exitCode}`);
  return `${lines.join('\n')}\n`;
}

export function runReasonCodeValidation(argv = process.argv) {
  const options = parseArgs(argv);
  const result = validateReasonCodesPolicy(options.policyPath);
  const exitCode = result.violations.length > 0 ? 1 : 0;

  if (options.format === 'json') {
    process.stdout.write(JSON.stringify({
      policyPath: result.policyPath,
      registeredCodes: result.registryCodes,
      emittedCodes: result.emittedCodes,
      missingEmittedCodes: result.missingEmitCodes,
      violations: result.violations,
      exitCode,
    }, null, 2));
    process.stdout.write('\n');
  } else {
    process.stdout.write(renderText(result, exitCode));
  }

  return { ...result, exitCode, options };
}

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath || typeof argvPath !== 'string') {
    return false;
  }
  try {
    const modulePath = path.resolve(fileURLToPath(metaUrl));
    const entryPath = path.resolve(argvPath);
    return modulePath === entryPath;
  } catch {
    return false;
  }
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  const result = runReasonCodeValidation(process.argv);
  process.exit(result.exitCode);
}

export {
  AUTOPILOT_REASON_SAMPLES,
  AUTOMATION_REPORT_SAMPLES,
  DEFAULT_POLICY_PATH,
  REASON_CODE_PATTERN,
  VALID_OWNER_HINTS,
  collectEmitReasonCodes,
};
