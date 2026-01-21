#!/usr/bin/env node
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const workflowsDir = join(process.cwd(), '.github', 'workflows');
const setupAction = './.github/actions/setup-node-pnpm';

try {
  const files = readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));
  const missing = [];
  for (const name of files) {
    const path = join(workflowsDir, name);
    const contents = readFileSync(path, 'utf8');
    if (!contents.includes(`uses: ${setupAction}`)) {
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
  process.exitCode = 1;
} catch (error) {
  console.error(`Failed to audit setup-node-pnpm usage in "${workflowsDir}":`);
  console.error(error instanceof Error ? error.message : error);
  process.exit(1);
}
