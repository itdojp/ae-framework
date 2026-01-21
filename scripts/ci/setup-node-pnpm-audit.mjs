#!/usr/bin/env node
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const workflowsDir = join(process.cwd(), '.github', 'workflows');
const setupAction = './.github/actions/setup-node-pnpm';

try {
  const escapeForRegex = (value) => value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const usesPattern = new RegExp(
    String.raw`^[ \t]*uses:\s*(["'])?${escapeForRegex(setupAction)}\1?`,
    'm'
  );
  const reusableWorkflows = ['./.github/workflows/ci-core.yml', './.github/workflows/flake-stability.yml'];
  const reusablePattern = new RegExp(
    String.raw`^[ \t]*uses:\s*(["'])?(?:${reusableWorkflows.map(escapeForRegex).join('|')})\1?`,
    'm'
  );
  const pnpmOrNodePattern = /\bpnpm\b|\bnode\s+\S/m;
  const files = readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));
  const missing = [];
  const reviewOnly = [];
  for (const name of files) {
    const path = join(workflowsDir, name);
    const contents = readFileSync(path, 'utf8');
    if (usesPattern.test(contents) || reusablePattern.test(contents)) continue;
    if (pnpmOrNodePattern.test(contents)) {
      missing.push(name);
      continue;
    }
    reviewOnly.push(name);
  }

  missing.sort();
  reviewOnly.sort();
  if (missing.length === 0 && reviewOnly.length === 0) {
    console.log('All workflows use setup-node-pnpm or do not need pnpm/node.');
    process.exit(0);
  }

  if (missing.length > 0) {
    console.log('Workflows missing setup-node-pnpm (pnpm/node detected):');
    for (const name of missing) {
      console.log(`- ${name}`);
    }
  }
  if (reviewOnly.length > 0) {
    console.log('Workflows without pnpm/node usage (review if needed):');
    for (const name of reviewOnly) {
      console.log(`- ${name}`);
    }
  }
  process.exit(missing.length > 0 ? 1 : 0);
} catch (error) {
  console.error(`Failed to audit setup-node-pnpm usage in "${workflowsDir}":`);
  console.error(error instanceof Error ? error.message : error);
  process.exit(1);
}
