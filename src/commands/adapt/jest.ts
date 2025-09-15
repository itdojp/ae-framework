import * as fs from 'fs';
import * as path from 'path';
import chalk from 'chalk';

interface PackageJson {
  scripts?: Record<string, string>;
  [key: string]: any;
}

const DEFAULT_COVERAGE_THRESHOLD = {
  global: {
    branches: 80,
    functions: 80,
    lines: 80,
    statements: 80
  }
};

function backupFile(filePath: string): void {
  if (fs.existsSync(filePath)) {
    const backupPath = `${filePath}.bak`;
    fs.copyFileSync(filePath, backupPath);
    console.log(chalk.blue(`📋 Backed up ${path.basename(filePath)} to ${path.basename(backupPath)}`));
  }
}

function shellEscapeForSingleQuotes(str: string): string {
  // For single-quoted strings in shell, we need to replace single quotes with '\''
  return str.replace(/'/g, "'\\''");
}

function updatePackageJson(customThresholds?: { statements: number; branches: number; functions: number; lines: number }): boolean {
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

  const thresholdConfig = customThresholds ? {
    global: {
      branches: customThresholds.branches,
      functions: customThresholds.functions,
      lines: customThresholds.lines,
      statements: customThresholds.statements
    }
  } : DEFAULT_COVERAGE_THRESHOLD;

  if (!packageJson.scripts['test']) {
    const seedCmd = process.env['AE_SEED'] ? `AE_SEED=${process.env['AE_SEED']} ` : '';
    const thresholdJson = shellEscapeForSingleQuotes(JSON.stringify(thresholdConfig));
    packageJson.scripts['test'] = `${seedCmd}jest --coverage --coverageThreshold='${thresholdJson}'`;
    modified = true;
    console.log(chalk.green('✅ Added test script with coverage thresholds'));
  } else if (!packageJson.scripts['test'].includes('coverageThreshold')) {
    // Update existing test script to include coverage threshold
    const currentTest = packageJson.scripts['test'];
    const thresholdJson = shellEscapeForSingleQuotes(JSON.stringify(thresholdConfig));
    
    if (currentTest.includes('jest')) {
      packageJson.scripts['test'] = `${currentTest} --coverage --coverageThreshold='${thresholdJson}'`;
      modified = true;
      console.log(chalk.green('✅ Updated test script with coverage thresholds'));
    } else {
      console.log(chalk.yellow('⚠️  Existing test script does not use Jest, skipping threshold injection'));
    }
  } else {
    console.log(chalk.blue('ℹ️  Test script already has coverage threshold configuration'));
  }

  if (modified) {
    fs.writeFileSync(packageJsonPath, JSON.stringify(packageJson, null, 2) + '\n');
  }

  return true;
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

export async function adaptJest(thresholds?: { statements: number; branches: number; functions: number; lines: number }) {
  console.log(chalk.blue('🔧 Adapting project for Jest with ae-framework integration\n'));

  try {
    const success = updatePackageJson(thresholds);
    if (!success) return;

    updatePreCommitHook();

    console.log(chalk.cyan('\n📋 Jest Adaptation Summary:'));
    console.log(chalk.cyan('  • Coverage thresholds: 80% for all metrics'));
    console.log(chalk.cyan('  • AE_SEED integration for deterministic tests'));
    console.log(chalk.cyan('  • TDD guard integration via pre-commit hook'));
    
    console.log(chalk.cyan('\n🔄 Next Steps:'));
    console.log(chalk.cyan('  • Run: npm test'));
    console.log(chalk.cyan('  • Verify coverage thresholds are enforced'));
    console.log(chalk.cyan('  • Check pre-commit hook with: git commit'));
    
    console.log(chalk.green('\n✅ Jest adaptation completed successfully!'));

  } catch (error) {
    console.error(chalk.red(`❌ Jest adaptation failed: ${error instanceof Error ? error.message : 'Unknown error'}`));
    const { safeExit } = await import('../../utils/safe-exit.js');
    safeExit(1);
  }
}
