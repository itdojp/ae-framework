import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const workflowsDir = join(process.cwd(), '.github', 'workflows');
const files = readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));

const missing = [];
for (const name of files) {
  const path = join(workflowsDir, name);
  const contents = readFileSync(path, 'utf8');
  if (!contents.includes('concurrency:')) {
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
