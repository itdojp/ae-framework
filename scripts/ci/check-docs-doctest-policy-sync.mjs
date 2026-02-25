#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import yaml from 'js-yaml';

export const DEFAULT_PATHS = {
  workflowPath: '.github/workflows/docs-doctest.yml',
  packagePath: 'package.json',
  policyPath: 'docs/ci/docs-doctest-policy.md',
};

export const REQUIRED_WORKFLOW_PATHS = [
  'README.md',
  'docs/README.md',
  'docs/**',
  'scripts/doctest.ts',
  'scripts/docs/check-doc-consistency.mjs',
  'scripts/ci/check-docs-doctest-policy-sync.mjs',
  '.github/workflows/docs-doctest.yml',
  'package.json',
  'pnpm-lock.yaml',
];

const SYNC_CHECK_COMMAND = 'node scripts/ci/check-docs-doctest-policy-sync.mjs';

export function readUtf8(filePath) {
  try {
    return readFileSync(filePath, 'utf8');
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`failed to read ${filePath}: ${message}`);
  }
}

export function parseJson(raw, filePath) {
  try {
    return JSON.parse(raw);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`invalid JSON in ${filePath}: ${message}`);
  }
}

export function parseWorkflow(raw, filePath) {
  try {
    const parsed = yaml.load(raw);
    if (!parsed || typeof parsed !== 'object') {
      throw new Error('workflow root must be a mapping');
    }
    return parsed;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`invalid YAML in ${filePath}: ${message}`);
  }
}

function normalizeExpression(value) {
  return String(value ?? '').replace(/\s+/g, ' ').trim();
}

export function ensureContains(source, snippet, message, errors) {
  if (typeof source !== 'string' || !source.includes(snippet)) {
    errors.push(`${message} (missing: ${snippet})`);
  }
}

export function ensureArrayContains(values, expected, message, errors) {
  if (!Array.isArray(values) || !values.includes(expected)) {
    errors.push(`${message} (missing: ${expected})`);
  }
}

export function ensureEqual(actual, expected, message, errors) {
  if (actual !== expected) {
    errors.push(`${message} (expected: ${expected}, actual: ${actual || '(empty)'})`);
  }
}

export function findStepByName(steps, name) {
  if (!Array.isArray(steps)) {
    return { step: null, index: -1 };
  }
  const index = steps.findIndex((candidate) => candidate?.name === name);
  return {
    step: index >= 0 ? steps[index] : null,
    index,
  };
}

export function validateWorkflowConfig(workflowConfig, errors) {
  const onConfig = workflowConfig?.on ?? workflowConfig?.['on'];
  const pullRequestPaths = onConfig?.pull_request?.paths;
  const pushPaths = onConfig?.push?.paths;
  const dispatchInput = onConfig?.workflow_dispatch?.inputs?.full;

  for (const requiredPath of REQUIRED_WORKFLOW_PATHS) {
    ensureArrayContains(
      pullRequestPaths,
      requiredPath,
      'on.pull_request.paths must include required entry',
      errors
    );
    ensureArrayContains(
      pushPaths,
      requiredPath,
      'on.push.paths must include required entry',
      errors
    );
  }

  if (!dispatchInput || typeof dispatchInput !== 'object') {
    errors.push('on.workflow_dispatch.inputs.full is missing');
  } else {
    if (dispatchInput.type !== 'boolean') {
      errors.push(`workflow_dispatch full input type must be boolean (actual: ${dispatchInput.type})`);
    }
    if (dispatchInput.required !== false) {
      errors.push(`workflow_dispatch full input required must be false (actual: ${dispatchInput.required})`);
    }
  }

  const jobs = workflowConfig?.jobs ?? {};
  const indexJob = jobs['doctest-index'];
  const fullJob = jobs['doctest-full'];

  if (!indexJob || typeof indexJob !== 'object') {
    errors.push('jobs.doctest-index is missing');
    return;
  }
  if (!fullJob || typeof fullJob !== 'object') {
    errors.push('jobs.doctest-full is missing');
    return;
  }

  ensureEqual(
    normalizeExpression(indexJob.if),
    "${{ github.event_name != 'schedule' }}",
    'jobs.doctest-index.if mismatch',
    errors
  );
  ensureEqual(
    normalizeExpression(fullJob.if),
    "${{ github.event_name == 'schedule' || (github.event_name == 'workflow_dispatch' && inputs.full) }}",
    'jobs.doctest-full.if mismatch',
    errors
  );

  const indexSteps = indexJob.steps;
  const fullSteps = fullJob.steps;

  const { step: indexSyncStep, index: indexSyncPos } = findStepByName(
    indexSteps,
    'Validate docs-doctest policy sync'
  );
  const { step: fullSyncStep, index: fullSyncPos } = findStepByName(
    fullSteps,
    'Validate docs-doctest policy sync'
  );
  const { index: indexInstallPos } = findStepByName(indexSteps, 'Install dependencies');
  const { index: fullInstallPos } = findStepByName(fullSteps, 'Install dependencies');

  if (!indexSyncStep) {
    errors.push('doctest-index must include "Validate docs-doctest policy sync" step');
  } else {
    ensureContains(
      indexSyncStep.run,
      SYNC_CHECK_COMMAND,
      'doctest-index sync step must execute checker',
      errors
    );
  }
  if (!fullSyncStep) {
    errors.push('doctest-full must include "Validate docs-doctest policy sync" step');
  } else {
    ensureContains(
      fullSyncStep.run,
      SYNC_CHECK_COMMAND,
      'doctest-full sync step must execute checker',
      errors
    );
  }
  if (indexSyncPos >= 0 && indexInstallPos >= 0 && indexSyncPos > indexInstallPos) {
    errors.push('doctest-index sync step must run before Install dependencies');
  }
  if (fullSyncPos >= 0 && fullInstallPos >= 0 && fullSyncPos > fullInstallPos) {
    errors.push('doctest-full sync step must run before Install dependencies');
  }

  const { step: changedDocsStep, index: changedDocsPos } = findStepByName(
    indexSteps,
    'Detect changed markdown files (PR only)'
  );
  const { step: changedDocsRunStep, index: changedDocsRunPos } = findStepByName(
    indexSteps,
    'Run doctest (changed markdown in PR)'
  );

  if (!changedDocsStep) {
    errors.push('doctest-index must include "Detect changed markdown files (PR only)" step');
  } else {
    ensureEqual(
      normalizeExpression(changedDocsStep.if),
      "${{ github.event_name == 'pull_request' }}",
      'changed-docs step condition mismatch',
      errors
    );
    ensureContains(
      changedDocsStep.run,
      'git fetch --no-tags --depth=1 origin "${BASE_SHA}"',
      'changed-docs step must fetch base SHA in shallow checkout',
      errors
    );
    ensureContains(
      changedDocsStep.run,
      "-- '*.md' '**/*.md'",
      'changed-docs step must include root and nested markdown pathspec',
      errors
    );
    ensureContains(changedDocsStep.run, 'git diff --name-only', 'changed-docs step must run git diff', errors);
  }

  if (!changedDocsRunStep) {
    errors.push('doctest-index must include "Run doctest (changed markdown in PR)" step');
  } else {
    ensureEqual(
      normalizeExpression(changedDocsRunStep.if),
      "${{ github.event_name == 'pull_request' && steps.changed-docs.outputs.files != '' }}",
      'changed-docs doctest step condition mismatch',
      errors
    );
    ensureContains(
      changedDocsRunStep.run,
      'xargs -0 pnpm -s tsx scripts/doctest.ts',
      'changed-docs doctest step must invoke scripts/doctest.ts',
      errors
    );
  }

  if (changedDocsPos >= 0 && changedDocsRunPos >= 0 && changedDocsPos > changedDocsRunPos) {
    errors.push('"Detect changed markdown files (PR only)" must run before changed markdown doctest step');
  }
}

export function validatePackageScripts(scripts, errors) {
  const indexScript = scripts['test:doctest:index'];
  if (typeof indexScript !== 'string') {
    errors.push('package.json scripts.test:doctest:index is missing');
  } else {
    ensureContains(indexScript, 'scripts/doctest.ts', 'test:doctest:index must invoke scripts/doctest.ts', errors);
    ensureContains(indexScript, 'README.md', 'test:doctest:index must include README.md target', errors);
    ensureContains(indexScript, 'docs/README.md', 'test:doctest:index must include docs/README.md target', errors);
  }

  const fullScript = scripts['test:doctest:full'];
  if (typeof fullScript !== 'string') {
    errors.push('package.json scripts.test:doctest:full is missing');
  } else {
    ensureContains(fullScript, 'scripts/doctest.ts', 'test:doctest:full must invoke scripts/doctest.ts', errors);
    ensureContains(fullScript, 'docs/**/*.md', 'test:doctest:full must target docs/**/*.md', errors);
  }
}

export function validatePolicyDoc(policy, errors) {
  ensureContains(policy, '差分 Markdown', 'docs-doctest policy must mention changed markdown scope', errors);
  ensureContains(
    policy,
    'workflow_dispatch(full=true)',
    'docs-doctest policy must describe full dispatch input',
    errors
  );
  ensureContains(policy, '失敗時の対応手順（runbook）', 'docs-doctest policy must include runbook section', errors);
  ensureContains(
    policy,
    'check-docs-doctest-policy-sync.mjs',
    'docs-doctest policy must include sync checker local command',
    errors
  );
}

export function runDocsDoctestPolicySyncCheck(paths = DEFAULT_PATHS) {
  const { workflowPath, packagePath, policyPath } = paths;
  const errors = [];

  const workflowConfig = parseWorkflow(readUtf8(workflowPath), workflowPath);
  const pkg = parseJson(readUtf8(packagePath), packagePath);
  const policy = readUtf8(policyPath);
  const scripts = pkg?.scripts ?? {};

  validateWorkflowConfig(workflowConfig, errors);
  validatePackageScripts(scripts, errors);
  validatePolicyDoc(policy, errors);

  return {
    checkedFiles: [workflowPath, packagePath, policyPath],
    errors,
    exitCode: errors.length > 0 ? 1 : 0,
  };
}

export function main(paths = DEFAULT_PATHS) {
  try {
    const result = runDocsDoctestPolicySyncCheck(paths);

    if (result.exitCode !== 0) {
      console.error('[check-docs-doctest-policy-sync] FAILED');
      for (const error of result.errors) {
        console.error(`- ${error}`);
      }
      return result;
    }

    console.log('[check-docs-doctest-policy-sync] OK');
    for (const filePath of result.checkedFiles) {
      console.log(`- checked: ${filePath}`);
    }
    return result;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error('[check-docs-doctest-policy-sync] FAILED');
    console.error(`- ${message}`);
    return {
      checkedFiles: [paths.workflowPath, paths.packagePath, paths.policyPath],
      errors: [message],
      exitCode: 1,
    };
  }
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
  const result = main(DEFAULT_PATHS);
  process.exit(result.exitCode);
}
