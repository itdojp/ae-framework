#!/usr/bin/env node
import { readFileSync } from 'node:fs';

const workflowPath = '.github/workflows/docs-doctest.yml';
const packagePath = 'package.json';
const policyPath = 'docs/ci/docs-doctest-policy.md';

function readUtf8(path) {
  return readFileSync(path, 'utf8');
}

function ensureContains(source, snippet, message, errors) {
  if (!source.includes(snippet)) {
    errors.push(`${message} (missing: ${snippet})`);
  }
}

function main() {
  const errors = [];

  const workflow = readUtf8(workflowPath);
  const pkg = JSON.parse(readUtf8(packagePath));
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

  if (errors.length > 0) {
    console.error('[check-docs-doctest-policy-sync] FAILED');
    for (const error of errors) {
      console.error(`- ${error}`);
    }
    process.exit(1);
  }

  console.log('[check-docs-doctest-policy-sync] OK');
  console.log(`- checked: ${workflowPath}`);
  console.log(`- checked: ${packagePath}`);
  console.log(`- checked: ${policyPath}`);
}

main();
