import { execa } from 'execa';
import { loadConfigWithSource } from '../../core/config.js';
import { readFile, stat } from 'node:fs/promises';
import { getThreshold } from '../../utils/quality-policy-loader.js';

type CoverageThresholds = {
  branches: number;
  lines: number;
  functions: number;
  statements: number;
};

export async function qaRun(options?: { light?: boolean }) {
  const { config: cfg, source: configSource } = await loadConfigWithSource();
  const pm = (await detectPM()) ?? 'npm';
  const runner = await detectRunner();
  const isCI = isCi();
  const light = Boolean(options?.light || process.env['AE_QA_LIGHT'] === '1' || isCI);
  const qualityProfile = resolveQualityProfile(isCI);
  const configCoverage = getConfigCoverageThreshold(configSource.raw);
  
  console.log(`[ae:qa] running QA with ${runner} via ${pm}${light ? ' (light mode)' : ''}`);
  
  if (runner === 'jest') {
    const policyCoverage = loadPolicyCoverageThresholds(qualityProfile, isCI);
    const coverageThreshold = policyCoverage ?? cfg.qa.coverageThreshold;
    const threshold = JSON.stringify({ global: coverageThreshold });

    if (!isCI && configCoverage) {
      const sourceLabel = configSource.path ?? 'ae.config';
      console.warn(`[ae:qa] ${sourceLabel} coverageThreshold is a local hint only; policy/quality.json is the source of truth`);
    }

    if (!policyCoverage && !isCI && configCoverage) {
      console.warn('[ae:qa] quality policy not available; falling back to ae.config coverageThreshold (local hint only)');
    }

    try {
      if (light) {
        // Fallback to fast suite when available
        const script = pm === 'pnpm' ? 'test:fast' : 'test';
        await execa(pm, ['run', script], { stdio: 'inherit' });
      } else {
        await execa(pm, [
          'run', 
          'test', 
          '--', 
          '--coverage',
          `--coverageThreshold=${threshold}`
        ], { stdio: 'inherit' });
      }
    } catch (error) {
      console.error('[ae:qa] Coverage threshold not met or test failures');
      throw error;
    }
  } else if (runner === 'vitest') {
    const script = light ? 'test:fast' : 'test';
    console.log(`[ae:qa] running ${script} script for vitest`);
    await execa(pm, ['run', script], { stdio: 'inherit' });
  } else {
    console.warn('[ae:qa] unknown test runner, running default test command');
    const script = light ? 'test:fast' : 'test';
    await execa(pm, ['run', script], { stdio: 'inherit' });
  }
  
  console.log('[ae:qa] QA checks completed');
}

async function detectPM(): Promise<'pnpm' | 'npm' | 'yarn' | null> {
  try { await stat('pnpm-lock.yaml'); return 'pnpm'; } catch {}
  try { await stat('package-lock.json'); return 'npm'; } catch {}
  try { await stat('yarn.lock'); return 'yarn'; } catch {}
  return null;
}

async function detectRunner(): Promise<'jest' | 'vitest' | 'unknown'> {
  try {
    const pkg = JSON.parse(await readFile('package.json', 'utf8'));
    const deps = { ...pkg.dependencies, ...pkg.devDependencies };
    const testScript = pkg.scripts?.test || '';
    
    // Check test script first for more accurate detection
    if (testScript.includes('vitest')) return 'vitest';
    if (testScript.includes('jest')) return 'jest';
    
    // Fallback to dependencies
    if (deps?.vitest) return 'vitest';
    if (deps?.jest) return 'jest';
  } catch {}
  return 'unknown';
}

function isCi(): boolean {
  const flag = process.env['CI'];
  return flag === 'true' || flag === '1' || flag === 'yes';
}

function resolveQualityProfile(isCI: boolean): string {
  return process.env['AE_QUALITY_PROFILE'] || (isCI ? 'ci' : 'development');
}

function getConfigCoverageThreshold(raw: unknown): CoverageThresholds | null {
  if (!raw || typeof raw !== 'object') return null;
  const qa = (raw as { qa?: { coverageThreshold?: CoverageThresholds } }).qa;
  return qa?.coverageThreshold ?? null;
}

function loadPolicyCoverageThresholds(environment: string, isCI: boolean): CoverageThresholds | null {
  try {
    const lines = getThreshold('coverage', 'lines', environment);
    const functions = getThreshold('coverage', 'functions', environment);
    const branches = getThreshold('coverage', 'branches', environment);
    const statements = getThreshold('coverage', 'statements', environment);

    if (
      typeof lines !== 'number' ||
      typeof functions !== 'number' ||
      typeof branches !== 'number' ||
      typeof statements !== 'number'
    ) {
      if (isCI) {
        throw new Error('coverage thresholds are missing in policy/quality.json');
      }
      return null;
    }

    return { lines, functions, branches, statements };
  } catch (error) {
    if (isCI) {
      throw error;
    }
    return null;
  }
}
