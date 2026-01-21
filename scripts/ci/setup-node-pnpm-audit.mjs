#!/usr/bin/env node
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const workflowsDir = join(process.cwd(), '.github', 'workflows');
const setupAction = './.github/actions/setup-node-pnpm';

try {
  const escapeForRegex = (value) => value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const usesPattern = new RegExp(
    String.raw`^[ \t]*uses:\s*['"]?${escapeForRegex(setupAction)}['"]?`,
    'm'
  );
  const reusableWorkflows = ['./.github/workflows/ci-core.yml', './.github/workflows/flake-stability.yml'];
  const reusablePattern = new RegExp(
    String.raw`^[ \t]*uses:\s*['"]?(?:${reusableWorkflows.map(escapeForRegex).join('|')})['"]?`,
    'm'
  );
  const files = readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));
  const missing = [];
  for (const name of files) {
    const path = join(workflowsDir, name);
    const contents = readFileSync(path, 'utf8');
    if (!usesPattern.test(contents) && !reusablePattern.test(contents)) {
      missing.push(name);
    }
  }

  missing.sort();
  if (missing.length === 0) {
    console.log('All workflows use setup-node-pnpm.');
    process.exit(0);
  }

  console.log('Workflows not using setup-node-pnpm:');
  for (const name of missing) {
    console.log(`- ${name}`);
  }
  process.exit(1);
} catch (error) {
  console.error(`Failed to audit setup-node-pnpm usage in "${workflowsDir}":`);
  console.error(error instanceof Error ? error.message : error);
  process.exit(1);
}
