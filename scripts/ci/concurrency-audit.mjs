#!/usr/bin/env node
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const workflowsDir = join(process.cwd(), '.github', 'workflows');

try {
  const files = readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));
  const missing = [];
  const concurrencyPattern = /^\s*concurrency:/m;

  for (const name of files) {
    const path = join(workflowsDir, name);
    const contents = readFileSync(path, 'utf8');
    if (!concurrencyPattern.test(contents)) {
      missing.push(name);
    }
  }

  missing.sort();
  if (missing.length === 0) {
    console.log('All workflows define concurrency.');
    process.exit(0);
  }

  console.log('Workflows missing concurrency:');
  for (const name of missing) {
    console.log(`- ${name}`);
  }
  process.exitCode = 1;
} catch (error) {
  console.error(`Failed to audit workflow concurrency in directory "${workflowsDir}":`);
  console.error(error instanceof Error ? error.message : error);
  process.exit(1);
}
