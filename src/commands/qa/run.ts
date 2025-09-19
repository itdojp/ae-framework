import { execa } from 'execa';
import { loadConfig, type AeConfig } from '../../core/config.js';
import { readFile, stat } from 'node:fs/promises';
import { getQualityGate } from '../../utils/quality-policy-loader.js';

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
    if (mismatch) {
      console.warn('[ae:qa] WARN: ae.config.qa.coverageThreshold is treated as a hint and differs from policy. Policy is the source of truth.');
      console.warn(`[ae:qa] hint → lines=${hint.lines}, functions=${hint.functions}, branches=${hint.branches}, statements=${hint.statements}`);
      console.warn('[ae:qa] To change enforcement, update policy/quality.json (coverage.thresholds.*) or set AE_QUALITY_PROFILE.');
    } else {
      console.log('[ae:qa] Note: ae.config.qa.coverageThreshold is treated as a hint; policy governs enforcement.');
    }
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

export type CoverageThresholds = { branches: number; lines: number; functions: number; statements: number };

/**
 * Resolve effective coverage thresholds from centralized policy, treating ae.config as a hint.
 * Falls back to ae.config when policy load fails.
 */
export async function resolveCoverageThresholds(cfg: AeConfig, envProfile: string): Promise<{
  effective: CoverageThresholds;
  hint: CoverageThresholds | null;
  mismatch: boolean;
}> {
  const hint = cfg?.qa?.coverageThreshold ?? null;
  try {
    const gate = getQualityGate('coverage', envProfile);
    const eff: CoverageThresholds = {
      lines: Number(gate.thresholds.lines ?? 80),
      functions: Number(gate.thresholds.functions ?? 80),
      branches: Number(gate.thresholds.branches ?? 80),
      statements: Number(gate.thresholds.statements ?? 80),
    };
    const mismatch = hint ? (
      hint.lines !== eff.lines ||
      hint.functions !== eff.functions ||
      hint.branches !== eff.branches ||
      hint.statements !== eff.statements
    ) : false;
    return { effective: eff, hint, mismatch };
  } catch (e) {
    // Policy load failed — fall back to config hint with a warning
    if (hint) {
      console.warn('[ae:qa] WARN: Failed to load policy/quality.json. Falling back to ae.config.qa.coverageThreshold.');
      return { effective: hint, hint, mismatch: false };
    }
    // Final fallback
    const eff: CoverageThresholds = { lines: 80, functions: 80, branches: 80, statements: 80 };
    console.warn('[ae:qa] WARN: No policy and no ae.config thresholds found. Falling back to defaults (80%).');
    return { effective: eff, hint: null, mismatch: false };
  }
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
