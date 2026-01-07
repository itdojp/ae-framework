import * as fs from 'fs';
import * as path from 'path';
import chalk from 'chalk';

const isErrnoException = (value: unknown): value is NodeJS.ErrnoException => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  if (!('code' in value)) {
    return false;
  }
  return typeof (value as { code?: unknown }).code === 'string';
};

const CI_WORKFLOW_TEMPLATE = `name: ae-ci
on:
  push:
    branches: [ main ]
  pull_request:

jobs:
  qa-bench:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'pnpm'
      - name: Enable corepack
        run: corepack enable
      - name: Install
        run: pnpm install --frozen-lockfile
      - name: Build
        run: pnpm run build
      - name: QA
        run: node dist/src/cli/index.js qa
      - name: Bench (seeded)
        run: AE_SEED=123 node dist/src/cli/index.js bench
      - name: Upload artifacts
        uses: actions/upload-artifact@v4
        with:
          name: ae-artifacts
          path: artifacts/
`;

export async function ciScaffold(force = false) {
  const workflowDir = path.join(process.cwd(), '.github', 'workflows');
  const workflowFile = path.join(workflowDir, 'ae-ci.yml');

  // Create .github/workflows directory if it doesn't exist
  try {
    fs.mkdirSync(workflowDir, { recursive: true });
  } catch (error) {
    if (!isErrnoException(error) || error.code !== 'EEXIST') {
      throw error;
    }
  }

  // Write workflow file
  try {
    fs.writeFileSync(workflowFile, CI_WORKFLOW_TEMPLATE.trim(), { flag: force ? 'w' : 'wx' });
  } catch (error) {
    if (!force && isErrnoException(error) && error.code === 'EEXIST') {
      console.log(chalk.yellow('⚠️  CI workflow file already exists: .github/workflows/ae-ci.yml'));
      console.log(chalk.yellow('   Use --force to overwrite'));
      return;
    }
    throw error;
  }
  
  const action = force ? 'Updated' : 'Created';
  console.log(chalk.green(`✅ ${action} CI workflow: .github/workflows/ae-ci.yml`));
  
  console.log(chalk.cyan('\n📋 Workflow includes:'));
  console.log(chalk.cyan('  • Node.js 20 setup'));
  console.log(chalk.cyan('  • pnpm via corepack'));
  console.log(chalk.cyan('  • Build step'));
  console.log(chalk.cyan('  • QA validation via `ae qa`'));
  console.log(chalk.cyan('  • Deterministic benchmark via `AE_SEED=123 ae bench`'));
  console.log(chalk.cyan('  • Artifact upload from artifacts/ directory'));
  
  console.log(chalk.cyan('\n🚀 Triggers:'));
  console.log(chalk.cyan('  • Push to main branch'));
  console.log(chalk.cyan('  • Pull requests'));
}
