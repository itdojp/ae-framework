import * as os from 'node:os';
import * as process from 'node:process';
import { execSync } from 'node:child_process';
import chalk from 'chalk';

interface CheckResult {
  name: string;
  status: 'OK' | 'WARN' | 'ERROR';
  value: string;
  message?: string;
  action?: string;
}

function checkCommand(command: string): boolean {
  try {
    execSync(`which ${command}`, { stdio: 'pipe' });
    return true;
  } catch {
    return false;
  }
}

function getNodeVersion(): { major: number; minor: number; patch: number; full: string } {
  const version = process.version.slice(1); // Remove 'v' prefix
  const parts = version.split('.');
  const major = Number(parts[0] ?? '0');
  const minor = Number(parts[1] ?? '0');
  const patch = Number(parts[2] ?? '0');
  return { major, minor, patch, full: version };
}

function formatBytes(bytes: number): string {
  const gb = bytes / (1024 * 1024 * 1024);
  return `${gb.toFixed(1)}GB`;
}

export async function doctorEnv() {
  console.log(chalk.blue('🔍 Environment Diagnostics\n'));

  const checks: CheckResult[] = [];
  let hasErrors = false;
  let hasWarnings = false;

  // Node.js version check (>=20.11 <23)
  const nodeVersion = getNodeVersion();
  const nodeVersionStr = `v${nodeVersion.full}`;
  if (nodeVersion.major >= 23) {
    checks.push({
      name: 'Node.js Version',
      status: 'WARN',
      value: nodeVersionStr,
      message: 'Version too new, may have compatibility issues',
      action: 'Consider using Node.js 20.x or 22.x'
    });
    hasWarnings = true;
  } else if (nodeVersion.major >= 20 && (nodeVersion.major > 20 || nodeVersion.minor >= 11)) {
    checks.push({
      name: 'Node.js Version',
      status: 'OK',
      value: nodeVersionStr
    });
  } else {
    checks.push({
      name: 'Node.js Version',
      status: 'ERROR',
      value: nodeVersionStr,
      message: 'Version too old',
      action: 'Upgrade to Node.js >=20.11'
    });
    hasErrors = true;
  }

  // Memory check (>=8GB)
  const totalMemory = os.totalmem();
  const memoryGB = totalMemory / (1024 * 1024 * 1024);
  const memoryStr = formatBytes(totalMemory);
  if (memoryGB >= 8) {
    checks.push({
      name: 'Memory',
      status: 'OK',
      value: memoryStr
    });
  } else if (memoryGB >= 4) {
    checks.push({
      name: 'Memory',
      status: 'WARN',
      value: memoryStr,
      message: 'Low memory may impact performance',
      action: 'Consider upgrading to >=8GB RAM'
    });
    hasWarnings = true;
  } else {
    checks.push({
      name: 'Memory',
      status: 'ERROR',
      value: memoryStr,
      message: 'Insufficient memory',
      action: 'Upgrade to >=8GB RAM'
    });
    hasErrors = true;
  }

  // API Keys check
  const anthropicKey = process.env['ANTHROPIC_API_KEY'];
  const openaiKey = process.env['OPENAI_API_KEY'];
  const geminiKey = process.env['GEMINI_API_KEY'];
  
  const apiKeyCount = [anthropicKey, openaiKey, geminiKey].filter(Boolean).length;
  if (apiKeyCount > 0) {
    const keyNames = [];
    if (anthropicKey) keyNames.push('Anthropic');
    if (openaiKey) keyNames.push('OpenAI');
    if (geminiKey) keyNames.push('Gemini');
    
    checks.push({
      name: 'API Keys',
      status: 'OK',
      value: keyNames.join(', ')
    });
  } else {
    checks.push({
      name: 'API Keys',
      status: 'WARN',
      value: 'None configured',
      message: 'LLM features will use echo provider',
      action: 'Set ANTHROPIC_API_KEY, OPENAI_API_KEY, or GEMINI_API_KEY'
    });
    hasWarnings = true;
  }

  // Package managers
  const hasPnpm = checkCommand('pnpm');
  const hasNpx = checkCommand('npx');
  
  if (hasPnpm) {
    checks.push({
      name: 'pnpm',
      status: 'OK',
      value: 'Available'
    });
  } else {
    checks.push({
      name: 'pnpm',
      status: 'WARN',
      value: 'Not found',
      message: 'Will fallback to npm',
      action: 'Install with: npm install -g pnpm'
    });
    hasWarnings = true;
  }

  if (hasNpx) {
    checks.push({
      name: 'npx',
      status: 'OK',
      value: 'Available'
    });
  } else {
    checks.push({
      name: 'npx',
      status: 'ERROR',
      value: 'Not found',
      message: 'Required for package execution',
      action: 'Reinstall Node.js or npm'
    });
    hasErrors = true;
  }

  // Git
  const hasGit = checkCommand('git');
  if (hasGit) {
    checks.push({
      name: 'Git',
      status: 'OK',
      value: 'Available'
    });
  } else {
    checks.push({
      name: 'Git',
      status: 'ERROR',
      value: 'Not found',
      message: 'Required for version control',
      action: 'Install Git'
    });
    hasErrors = true;
  }

  // Chrome/Chromium (optional)
  const hasChrome = checkCommand('google-chrome') || checkCommand('chromium') || checkCommand('chrome');
  if (hasChrome) {
    checks.push({
      name: 'Chrome/Chromium',
      status: 'OK',
      value: 'Available'
    });
  } else {
    checks.push({
      name: 'Chrome/Chromium',
      status: 'WARN',
      value: 'Not found',
      message: 'E2E tests may not work',
      action: 'Install Chrome or Chromium for E2E testing'
    });
    hasWarnings = true;
  }

  // System info
  console.log(chalk.cyan('📊 System Information:'));
  console.log(chalk.cyan(`   OS: ${os.type()} ${os.release()}`));
  console.log(chalk.cyan(`   Architecture: ${os.arch()}`));
  console.log(chalk.cyan(`   Platform: ${os.platform()}`));
  console.log();

  // Results table
  console.log(chalk.cyan('🔍 Environment Checks:'));
  console.log();
  
  const maxNameLength = Math.max(...checks.map(c => c.name.length));
  
  checks.forEach(check => {
    const icon = check.status === 'OK' ? '✅' : check.status === 'WARN' ? '⚠️ ' : '❌';
    const color = check.status === 'OK' ? chalk.green : check.status === 'WARN' ? chalk.yellow : chalk.red;
    const name = check.name.padEnd(maxNameLength);
    
    console.log(`${icon} ${color(name)} ${color(check.value)}`);
    
    if (check.message) {
      console.log(`   ${color(`→ ${check.message}`)}`);
    }
    if (check.action) {
      console.log(`   ${color(`💡 ${check.action}`)}`);
    }
  });

  console.log();

  // Summary
  const errorCount = checks.filter(c => c.status === 'ERROR').length;
  const warnCount = checks.filter(c => c.status === 'WARN').length;
  const okCount = checks.filter(c => c.status === 'OK').length;

  if (hasErrors) {
    console.log(chalk.red(`❌ ${errorCount} critical issue(s) found`));
    console.log(chalk.yellow(`⚠️  ${warnCount} warning(s)`));
    console.log(chalk.green(`✅ ${okCount} check(s) passed`));
    console.log();
    console.log(chalk.red('🚫 Environment has critical issues that may prevent proper operation'));
    process.exit(1);
  } else if (hasWarnings) {
    console.log(chalk.yellow(`⚠️  ${warnCount} warning(s)`));
    console.log(chalk.green(`✅ ${okCount} check(s) passed`));
    console.log();
    console.log(chalk.yellow('⚠️  Environment has warnings but should work'));
  } else {
    console.log(chalk.green(`✅ All ${okCount} checks passed`));
    console.log();
    console.log(chalk.green('🎉 Environment is ready for ae-framework!'));
  }
}
