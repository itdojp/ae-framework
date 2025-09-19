import { execa } from 'execa';
import { loadConfig } from '../../core/config.js';
import { readFile, stat } from 'node:fs/promises';
import { resolveCoverageThresholds } from '../../utils/coverage-thresholds.js';

export async function qaRun(options?: { light?: boolean }) {
  const cfg = await loadConfig();
  const envProfile = process.env['AE_QUALITY_PROFILE'] || (process.env['CI'] === 'true' ? 'ci' : 'development');
  const { effective, hint, mismatch } = await resolveCoverageThresholds(cfg, envProfile);
  const pm = (await detectPM()) ?? 'npm';
  const runner = await detectRunner();
  const light = Boolean(options?.light || process.env['AE_QA_LIGHT'] === '1' || process.env['CI'] === 'true');
  
  console.log(`[ae:qa] running QA with ${runner} via ${pm}${light ? ' (light mode)' : ''}`);
  console.log(`[ae:qa] Using coverage thresholds from policy/quality.json (profile: ${envProfile})`);
  console.log(`[ae:qa] thresholds → lines=${effective.lines}, functions=${effective.functions}, branches=${effective.branches}, statements=${effective.statements}`);
  if (hint) {
    // Always warn when ae.config contains thresholds; policy remains the source of truth.
    console.warn('[ae:qa] WARN: ae.config.qa.coverageThreshold is treated as a hint. Policy is the source of truth.');
    console.warn(`[ae:qa] hint → lines=${hint.lines}, functions=${hint.functions}, branches=${hint.branches}, statements=${hint.statements}`);
    if (mismatch) {
      console.warn('[ae:qa] HINT differs from policy thresholds. Enforcement will follow policy.');
    }
    console.warn('[ae:qa] To change enforcement, update policy/quality.json (coverage.thresholds.*) or set AE_QUALITY_PROFILE.');
  }
  
  if (runner === 'jest') {
    // Inject effective thresholds from policy into Jest
    const threshold = JSON.stringify({ global: effective });
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

// resolveCoverageThresholds moved to utils for testability

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
