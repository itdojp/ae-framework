import { execa } from 'execa';
import { loadConfig } from '../../core/config.js';
import { readFile, stat } from 'node:fs/promises';

export async function qaRun() {
  const cfg = await loadConfig();
  const pm = (await detectPM()) ?? 'npm';
  const runner = await detectRunner();
  
  console.log(`[ae:qa] running QA with ${runner} via ${pm}`);
  
  if (runner === 'jest') {
    const threshold = JSON.stringify({ global: cfg.qa.coverageThreshold });
    try {
      await execa(pm, [
        'run', 
        'test', 
        '--', 
        '--coverage',
        `--coverageThreshold=${threshold}`
      ], { stdio: 'inherit' });
    } catch (error) {
      console.error('[ae:qa] Coverage threshold not met or test failures');
      throw error;
    }
  } else if (runner === 'vitest') {
    console.log('[ae:qa] vitest coverage thresholds will be extended in future PR. Running normal tests.');
    await execa(pm, ['run', 'test'], { stdio: 'inherit' });
  } else {
    console.warn('[ae:qa] unknown test runner, running default test command');
    await execa(pm, ['run', 'test'], { stdio: 'inherit' });
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