import * as fs from 'fs';
import * as path from 'path';
import chalk from 'chalk';

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
      - name: Use pnpm if available
        run: |
          if [ -f pnpm-lock.yaml ]; then npm i -g pnpm && echo "PM=pnpm" >> $GITHUB_ENV; else echo "PM=npm" >> $GITHUB_ENV; fi
      - name: Install
        run: \${{ env.PM }} install
      - name: Build
        run: \${{ env.PM }} run build
      - name: QA
        run: node dist/cli.js qa
      - name: Bench (seeded)
        run: AE_SEED=123 node dist/cli.js bench
      - name: Upload artifacts
        uses: actions/upload-artifact@v4
        with:
          name: ae-artifacts
          path: artifacts/
`;

export async function ciScaffold(force = false) {
  const workflowDir = path.join(process.cwd(), '.github', 'workflows');
  const workflowFile = path.join(workflowDir, 'ae-ci.yml');

  // Check if file already exists
  const fileExists = fs.existsSync(workflowFile);
  if (fileExists && !force) {
    console.log(chalk.yellow('⚠️  CI workflow file already exists: .github/workflows/ae-ci.yml'));
    console.log(chalk.yellow('   Use --force to overwrite'));
    return;
  }

  // Create .github/workflows directory if it doesn't exist
  if (!fs.existsSync(workflowDir)) {
    fs.mkdirSync(workflowDir, { recursive: true });
    console.log(chalk.blue('📁 Created .github/workflows directory'));
  }

  // Write workflow file
  fs.writeFileSync(workflowFile, CI_WORKFLOW_TEMPLATE.trim());
  
  const action = fileExists ? 'Updated' : 'Created';
  console.log(chalk.green(`✅ ${action} CI workflow: .github/workflows/ae-ci.yml`));
  
  console.log(chalk.cyan('\n📋 Workflow includes:'));
  console.log(chalk.cyan('  • Node.js 20 setup'));
  console.log(chalk.cyan('  • Auto-detection of pnpm vs npm'));
  console.log(chalk.cyan('  • Build step'));
  console.log(chalk.cyan('  • QA validation via `ae qa`'));
  console.log(chalk.cyan('  • Deterministic benchmark via `AE_SEED=123 ae bench`'));
  console.log(chalk.cyan('  • Artifact upload from artifacts/ directory'));
  
  console.log(chalk.cyan('\n🚀 Triggers:'));
  console.log(chalk.cyan('  • Push to main branch'));
  console.log(chalk.cyan('  • Pull requests'));
}