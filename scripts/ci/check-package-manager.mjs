import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const DEFAULT_PACKAGE_MANAGER = 'pnpm@10.0.0';
const DEFAULT_NODE_RANGE = '>=20.11 <23';

export function isExecutedAsMain(importMetaUrl, argvPath) {
  const modulePath = fileURLToPath(importMetaUrl);
  return path.resolve(modulePath) === path.resolve(argvPath);
}

function safeReadProjectMetadata(cwd = process.cwd()) {
  try {
    const packageJsonPath = path.join(cwd, 'package.json');
    const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf8'));
    return {
      packageManager: packageJson.packageManager || DEFAULT_PACKAGE_MANAGER,
      nodeRange: packageJson.engines?.node || DEFAULT_NODE_RANGE,
    };
  } catch {
    return {
      packageManager: DEFAULT_PACKAGE_MANAGER,
      nodeRange: DEFAULT_NODE_RANGE,
    };
  }
}

function normalizeEnvValue(value) {
  return typeof value === 'string' ? value : '';
}

export function detectPackageManager(env = process.env) {
  const userAgent = normalizeEnvValue(env.npm_config_user_agent).toLowerCase();
  const execPath = normalizeEnvValue(env.npm_execpath).toLowerCase();

  if (userAgent.includes('pnpm/')) return 'pnpm';
  if (userAgent.includes('npm/')) return 'npm';
  if (userAgent.includes('yarn/')) return 'yarn';
  if (userAgent.includes('bun/')) return 'bun';

  if (execPath.includes('pnpm')) return 'pnpm';
  if (execPath.includes('npm-cli.js') || execPath.includes('/npm') || execPath.includes('\\npm')) return 'npm';
  if (execPath.includes('yarn')) return 'yarn';
  if (execPath.includes('bun')) return 'bun';

  return 'unknown';
}

export function evaluatePackageManager(env = process.env, cwd = process.cwd()) {
  const metadata = safeReadProjectMetadata(cwd);
  const requiredManager = metadata.packageManager.split('@')[0] || 'pnpm';
  const detectedManager = detectPackageManager(env);
  const userAgent = normalizeEnvValue(env.npm_config_user_agent);
  const execPath = normalizeEnvValue(env.npm_execpath);
  const hasRuntimeMetadata = userAgent.length > 0 || execPath.length > 0;

  if (env.AE_SKIP_PACKAGE_MANAGER_CHECK === '1') {
    return {
      ok: true,
      reason: 'skipped_by_env',
      detectedManager,
      requiredManager,
      packageManager: metadata.packageManager,
      nodeRange: metadata.nodeRange,
      userAgent,
      execPath,
    };
  }

  if (detectedManager === requiredManager) {
    return {
      ok: true,
      reason: 'pnpm_detected',
      detectedManager,
      requiredManager,
      packageManager: metadata.packageManager,
      nodeRange: metadata.nodeRange,
      userAgent,
      execPath,
    };
  }

  if (!hasRuntimeMetadata) {
    return {
      ok: true,
      reason: 'missing_runtime_metadata',
      detectedManager,
      requiredManager,
      packageManager: metadata.packageManager,
      nodeRange: metadata.nodeRange,
      userAgent,
      execPath,
    };
  }

  return {
    ok: false,
    reason: 'unsupported_package_manager',
    detectedManager,
    requiredManager,
    packageManager: metadata.packageManager,
    nodeRange: metadata.nodeRange,
    userAgent,
    execPath,
  };
}

export function buildFailureMessage(result) {
  const detected = result.detectedManager === 'unknown' ? 'unknown (likely not pnpm)' : result.detectedManager;
  return [
    '',
    '[ae-framework] Installation blocked: this repository requires pnpm.',
    '',
    `Detected package manager: ${detected}`,
    `Required package manager: ${result.packageManager}`,
    `Required Node.js range: ${result.nodeRange}`,
    '',
    'Why this fails:',
    '- This repository uses a pnpm workspace configuration (workspace:*).',
    '- npm/yarn/bun can fail to resolve workspace dependencies correctly in this project.',
    '',
    'Recommended setup:',
    '  corepack enable',
    `  corepack prepare ${result.packageManager} --activate`,
    '  pnpm install',
    '',
    'If you need a temporary bypass in a special environment:',
    '  AE_SKIP_PACKAGE_MANAGER_CHECK=1',
    '',
  ].join('\n');
}

export function runPackageManagerCheck(env = process.env, cwd = process.cwd(), stderr = process.stderr) {
  const result = evaluatePackageManager(env, cwd);
  if (result.ok) {
    return 0;
  }

  stderr.write(buildFailureMessage(result));
  return 1;
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  process.exitCode = runPackageManagerCheck();
}
