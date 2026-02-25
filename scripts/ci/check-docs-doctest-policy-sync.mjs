#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const DEFAULT_PATHS = {
  workflowPath: '.github/workflows/docs-doctest.yml',
  packagePath: 'package.json',
  policyPath: 'docs/ci/docs-doctest-policy.md',
};

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

export function ensureContains(source, snippet, message, errors) {
  if (!source.includes(snippet)) {
    errors.push(`${message} (missing: ${snippet})`);
  }
}

export function ensureRegexCount(source, pattern, minimum, message, errors) {
  const count = [...source.matchAll(pattern)].length;
  if (count < minimum) {
    errors.push(`${message} (expected >= ${minimum}, actual: ${count})`);
  }
}

export function runDocsDoctestPolicySyncCheck(paths = DEFAULT_PATHS) {
  const { workflowPath, packagePath, policyPath } = paths;
  const errors = [];

  const workflow = readUtf8(workflowPath);
  const pkg = parseJson(readUtf8(packagePath), packagePath);
  const policy = readUtf8(policyPath);
  const scripts = pkg?.scripts ?? {};

  ensureContains(
    workflow,
    "if: ${{ github.event_name != 'schedule' }}",
    'doctest-index must skip schedule',
    errors
  );
  ensureContains(workflow, 'Detect changed markdown files (PR only)', 'changed-docs step is required', errors);
  ensureContains(
    workflow,
    'git fetch --no-tags --depth=1 origin "${BASE_SHA}"',
    'changed-docs step must fetch base SHA in shallow checkout',
    errors
  );
  ensureContains(
    workflow,
    "-- '*.md' '**/*.md'",
    'changed-docs pathspec must include root and nested markdown paths',
    errors
  );
  ensureContains(
    workflow,
    "if: ${{ github.event_name == 'pull_request' && steps.changed-docs.outputs.files != '' }}",
    'changed-docs doctest execution guard is required',
    errors
  );
  ensureRegexCount(
    workflow,
    /^\s*-\s*'scripts\/ci\/check-docs-doctest-policy-sync\.mjs'\s*$/gm,
    2,
    'docs-doctest workflow paths must include policy-sync checker',
    errors
  );

  if (typeof scripts['test:doctest:index'] !== 'string') {
    errors.push('package.json scripts.test:doctest:index is missing');
  } else if (!scripts['test:doctest:index'].includes('{README.md,docs/README.md}')) {
    errors.push('test:doctest:index must include README/docs index brace pattern');
  }

  if (typeof scripts['test:doctest:full'] !== 'string') {
    errors.push('package.json scripts.test:doctest:full is missing');
  } else if (!scripts['test:doctest:full'].includes('docs/**/*.md')) {
    errors.push('test:doctest:full must target docs/**/*.md');
  }

  ensureContains(policy, '差分 Markdown', 'docs-doctest policy must mention changed markdown scope', errors);
  ensureContains(
    policy,
    'workflow_dispatch(full=true)',
    'docs-doctest policy must describe full dispatch input',
    errors
  );

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
