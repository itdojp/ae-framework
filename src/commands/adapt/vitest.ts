import * as fs from 'fs';
import * as path from 'path';
import chalk from 'chalk';

interface PackageJson {
  scripts?: Record<string, string>;
  [key: string]: any;
}

function generateVitestConfigTemplate(thresholds = { lines: 80, functions: 80, branches: 80, statements: 80 }) {
  return `import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    coverage: {
      provider: 'v8', // or 'c8'
      thresholds: {
        lines: ${thresholds.lines},
        functions: ${thresholds.functions},
        branches: ${thresholds.branches},
        statements: ${thresholds.statements},
      }
    }
  }
});
`;
}

function backupFile(filePath: string): void {
  if (fs.existsSync(filePath)) {
    const backupPath = `${filePath}.bak`;
    fs.copyFileSync(filePath, backupPath);
    console.log(chalk.blue(`📋 Backed up ${path.basename(filePath)} to ${path.basename(backupPath)}`));
  }
}

function updatePackageJson(): boolean {
  const packageJsonPath = path.join(process.cwd(), 'package.json');
  
  if (!fs.existsSync(packageJsonPath)) {
    console.log(chalk.red('❌ package.json not found'));
    return false;
  }

  backupFile(packageJsonPath);
  
  const packageJson: PackageJson = JSON.parse(fs.readFileSync(packageJsonPath, 'utf8'));
  
  let modified = false;

  // Add test script if missing
  if (!packageJson.scripts) {
    packageJson.scripts = {};
  }

  if (!packageJson.scripts.test) {
    const seedCmd = process.env.AE_SEED ? `AE_SEED=${process.env.AE_SEED} ` : '';
    packageJson.scripts.test = `${seedCmd}vitest run --coverage`;
    modified = true;
    console.log(chalk.green('✅ Added test script with coverage'));
  } else if (!packageJson.scripts.test.includes('--coverage') && packageJson.scripts.test.includes('vitest')) {
    // Update existing vitest script to include coverage
    const currentTest = packageJson.scripts.test;
    packageJson.scripts.test = `${currentTest} --coverage`;
    modified = true;
    console.log(chalk.green('✅ Updated test script with coverage'));
  } else if (!packageJson.scripts.test.includes('vitest')) {
    console.log(chalk.yellow('⚠️  Existing test script does not use Vitest, skipping coverage injection'));
  } else {
    console.log(chalk.blue('ℹ️  Test script already has coverage configuration'));
  }

  if (modified) {
    fs.writeFileSync(packageJsonPath, JSON.stringify(packageJson, null, 2) + '\n');
  }

  return true;
}

function generateVitestConfigSnippet(thresholds = { lines: 80, functions: 80, branches: 80, statements: 80 }) {
  return `
  test: {
    coverage: {
      provider: 'v8',
      thresholds: {
        lines: ${thresholds.lines},
        functions: ${thresholds.functions}, 
        branches: ${thresholds.branches},
        statements: ${thresholds.statements},
      }
    }
  }`;
}

function createVitestConfig(customThresholds?: { statements: number; branches: number; functions: number; lines: number }): void {
  const configPaths = [
    'vitest.config.ts',
    'vitest.config.js',
    'vite.config.ts',
    'vite.config.js'
  ];
  
  const existingConfig = configPaths.find(p => fs.existsSync(path.join(process.cwd(), p)));
  
  const thresholds = customThresholds || { lines: 80, functions: 80, branches: 80, statements: 80 };

  if (existingConfig) {
    console.log(chalk.blue(`ℹ️  Existing config found: ${existingConfig}`));
    console.log(chalk.yellow('⚠️  Please manually add coverage thresholds to your existing config:'));
    console.log(chalk.cyan(generateVitestConfigSnippet(thresholds)));
    return;
  }

  const configPath = path.join(process.cwd(), 'vitest.config.ts');
  fs.writeFileSync(configPath, generateVitestConfigTemplate(thresholds));
  console.log(chalk.green('✅ Created vitest.config.ts with coverage thresholds'));
}

function updatePreCommitHook(): void {
  const huskyPath = path.join(process.cwd(), '.husky');
  const preCommitPath = path.join(huskyPath, 'pre-commit');
  
  if (!fs.existsSync(preCommitPath)) {
    console.log(chalk.blue('ℹ️  No .husky/pre-commit found, skipping guard setup'));
    return;
  }

  backupFile(preCommitPath);
  
  const preCommitContent = fs.readFileSync(preCommitPath, 'utf8');
  
  if (preCommitContent.includes('ae tdd:guard')) {
    console.log(chalk.blue('ℹ️  TDD guard already configured in pre-commit hook'));
    return;
  }

  const updatedContent = preCommitContent.trim() + '\nae tdd:guard\n';
  fs.writeFileSync(preCommitPath, updatedContent);
  console.log(chalk.green('✅ Added TDD guard to pre-commit hook'));
}

export async function adaptVitest(thresholds?: { statements: number; branches: number; functions: number; lines: number }) {
  console.log(chalk.blue('🔧 Adapting project for Vitest with ae-framework integration\n'));

  try {
    const success = updatePackageJson();
    if (!success) return;

    createVitestConfig(thresholds);
    updatePreCommitHook();

    console.log(chalk.cyan('\n📋 Vitest Adaptation Summary:'));
    console.log(chalk.cyan('  • Coverage thresholds: 80% for all metrics'));
    console.log(chalk.cyan('  • AE_SEED integration for deterministic tests'));
    console.log(chalk.cyan('  • TDD guard integration via pre-commit hook'));
    console.log(chalk.cyan('  • Coverage provider: v8 (configurable)'));
    
    console.log(chalk.cyan('\n🔄 Next Steps:'));
    console.log(chalk.cyan('  • Install coverage provider: npm i -D @vitest/coverage-v8'));
    console.log(chalk.cyan('  • Run: npm test'));
    console.log(chalk.cyan('  • Verify coverage thresholds are enforced'));
    console.log(chalk.cyan('  • Check pre-commit hook with: git commit'));
    
    console.log(chalk.green('\n✅ Vitest adaptation completed successfully!'));

  } catch (error) {
    console.error(chalk.red(`❌ Vitest adaptation failed: ${error instanceof Error ? error.message : 'Unknown error'}`));
    process.exit(1);
  }
}