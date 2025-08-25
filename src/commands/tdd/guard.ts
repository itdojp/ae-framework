import { execa } from 'execa';
import pkg from 'micromatch';
const { match } = pkg;
import { loadConfig } from '../../core/config.js';
import { readFile, stat } from 'node:fs/promises';

export async function tddGuard() {
  const cfg = await loadConfig();
  const g = cfg.tddGuard;
  
  if (!g.enabled) {
    console.log('[ae:tdd:guard] disabled by config');
    return;
  }
  
  if (g.ciOnly && !process.env.CI) {
    console.log('[ae:tdd:guard] skipped (ciOnly=true, not in CI)');
    return;
  }
  
  if (process.env[g.allowSkipWithEnv] === '1') {
    console.log(`[ae:tdd:guard] skipped by ${g.allowSkipWithEnv}=1`);
    return;
  }
  
  const pm = (await detectPM()) ?? 'npm';
  const runner = await detectRunner();
  
  // Get changed files
  let targets: string[] = [];
  try {
    const { stdout } = await execa('git', ['diff', '--name-only', g.changedSince]);
    const changed = stdout.split('\n').filter(Boolean);
    targets = match(changed, g.include, { ignore: g.exclude });
  } catch (error) {
    console.warn('[ae:tdd:guard] git diff failed, running all tests');
    targets = []; // Will run all tests
  }
  
  if (g.onlyChanged && targets.length === 0) {
    console.log('[ae:tdd:guard] no relevant changes found');
    return;
  }
  
  console.log(`[ae:tdd:guard] running tests with ${runner} via ${pm}`);
  
  if (runner === 'jest') {
    if (targets.length > 0) {
      await execa(pm, ['run', 'test', '--', '--findRelatedTests', ...targets], { stdio: 'inherit' });
    } else {
      await execa(pm, ['run', 'test'], { stdio: 'inherit' });
    }
    await execa(pm, ['run', 'test', '--', '--coverage', '--coverageReporters=text-summary'], { stdio: 'inherit' });
  } else {
    // vitest fallback: run all tests (findRelatedTests is limited)
    console.log('[ae:tdd:guard] using vitest (running all tests)');
    await execa(pm, ['run', 'test'], { stdio: 'inherit' });
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