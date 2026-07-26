import * as os from 'node:os';
import { glob } from 'glob';
import { run } from '../../core/exec.js';
import { err, ok, isErr, type Result } from '../../core/result.js';
import type { AppError } from '../../core/errors.js';

async function detectPM(): Promise<'pnpm'|'npm'|'yarn'|'npx'> {
  const fs = await import('node:fs/promises');
  try { 
    await fs.stat('pnpm-lock.yaml'); 
    return 'pnpm'; 
  } catch {}
  try { 
    await fs.stat('package-lock.json'); 
    return 'npm'; 
  } catch {}
  try { 
    await fs.stat('yarn.lock'); 
    return 'yarn'; 
  } catch {}
  return 'npx';
}

interface QAFlakeOptions {
  times?: number;
  pattern?: string;
  timeoutMs?: number;
  workers?: string | number;
}

function toPortableTestPath(value: string): string {
  return value.replace(/\\/gu, '/');
}

function parseWorkers(workers?: string | number): string | undefined {
  if (workers === undefined) return undefined;
  if (typeof workers === 'number') return String(workers);
  if (typeof workers === 'string') {
    if (workers.endsWith('%')) {
      // Convert percentage to actual number
      const percent = parseInt(workers.slice(0, -1));
      const cores = os.cpus().length;
      return String(Math.max(1, Math.floor((cores * percent) / 100)));
    }
    return workers;
  }
  return undefined;
}

async function detectTestRunner(): Promise<'jest' | 'vitest'> {
  const fs = await import('node:fs/promises');
  try {
    const pkg = await fs.readFile('package.json', 'utf8');
    const json = JSON.parse(pkg);
    
    // Check if vitest is used in test script
    if (json.scripts?.test?.includes('vitest')) {
      return 'vitest';
    }
    
    // Check dependencies
    const allDeps = { ...json.dependencies, ...json.devDependencies };
    if (allDeps.vitest) return 'vitest';
    if (allDeps.jest) return 'jest';
    
    // Default to vitest for this project
    return 'vitest';
  } catch {
    return 'vitest';
  }
}

async function detectTestFiles(pattern?: string): Promise<{ pattern: string; files: string[] }> {
  if (pattern) {
    try {
      const files = (await glob(pattern, { nodir: true })).map(toPortableTestPath);
      return { pattern, files: files.sort((left, right) => left.localeCompare(right)) };
    } catch {
      return { pattern, files: [] };
    }
  }

  // Auto-fallback patterns in order
  const fallbackPatterns = [
    'tests/**/*.test.ts',
    'test/**/*.test.ts', 
    'tests/**'
  ];

  for (const fallbackPattern of fallbackPatterns) {
    try {
      const files = (await glob(fallbackPattern, { nodir: true })).map(toPortableTestPath);
      if (files.length > 0) {
        return {
          pattern: fallbackPattern,
          files: files.sort((left, right) => left.localeCompare(right)),
        };
      }
    } catch {
      // Continue to next pattern
    }
  }

  // If nothing found, use the first fallback as default with a safe fallback string
  return { pattern: fallbackPatterns[0] ?? 'tests/**/*.test.ts', files: [] };
}

export async function qaFlake(options: QAFlakeOptions = {}): Promise<Result<{ failures: number; total: number; seeds: number[] }, AppError>> {
  const { times = 10, pattern = 'tests/**/*.test.ts', timeoutMs = 300000, workers } = options;
  const pm = await detectPM();
  const testRunner = await detectTestRunner();
  
  // Detect test files with fallback patterns
  const testDetection = await detectTestFiles(pattern);
  const finalPattern = testDetection.pattern;
  const testFiles = testDetection.files;
  const fileCount = testFiles.length;
  
  let fails = 0; 
  const seeds: number[] = [];
  const failedSeeds: { seed: number; run: number }[] = [];
  
  console.log(`[ae][flake] Running tests ${times} times to detect flakiness...`);
  console.log(`[ae][flake] Package manager: ${pm}`);
  console.log(`[ae][flake] Test runner: ${testRunner}`);
  console.log(`[ae][flake] Pattern: ${finalPattern} (${fileCount} files detected)`);
  if (timeoutMs !== 300000) console.log(`[ae][flake] Timeout: ${timeoutMs}ms`);
  if (workers) console.log(`[ae][flake] Workers: ${workers}`);
  
  if (fileCount === 0) {
    console.log(`[ae][flake] ⚠️  Warning: No test files found with pattern '${finalPattern}'`);
  }
  
  for (let i = 0; i < times; i++) {
    const seed = Math.floor(Math.random() * 1e9);
    console.log(`[ae][flake] Run ${i + 1}/${times} (seed=${seed})`);
    
    // Build command args based on package manager and test runner
    let command: string;
    let args: string[] = [];
    
    if (pm === 'pnpm') {
      command = 'pnpm';
      args = ['test'];
    } else if (pm === 'npx') {
      command = 'npx';
      args = testRunner === 'vitest' ? ['vitest', 'run'] : ['jest'];
    } else {
      command = pm;
      args = ['run', 'test'];
    }
    
    // Add test runner specific options
    if (testRunner === 'vitest') {
      // Vitest does not expand quoted globs and --dir accepts only a directory.
      // Pass the reviewed, concrete glob matches as positional file filters.
      if (testFiles.length > 0) {
        args.push(...testFiles);
      } else if (finalPattern) {
        // Preserve a concrete non-glob filter for repositories where discovery
        // cannot enumerate files, while keeping the empty-match warning above.
        args.push(finalPattern);
      }
      if (workers) {
        const parsedWorkers = parseWorkers(workers);
        if (parsedWorkers) {
          // Note: Some Vitest configurations may conflict with --maxWorkers
          console.log(`[ae][flake] Warning: Using --maxWorkers ${parsedWorkers} (may conflict with existing config)`);
          args.push('--maxWorkers', parsedWorkers);
        }
      }
    } else if (testRunner === 'jest') {
      // Jest options - use finalPattern from detection 
      if (finalPattern) {
        args.push('--testPathPattern', finalPattern);
      }
      if (workers) {
        const parsedWorkers = parseWorkers(workers);
        if (parsedWorkers) {
          args.push('--maxWorkers', parsedWorkers);
        }
      }
    }
    
    const result = await run(`flake-run-${i + 1}`, command, args, {
      env: { ...process.env, AE_SEED: String(seed) }, 
      stdio: 'inherit',
      timeout: timeoutMs,
      killSignal: 'SIGTERM'
    });
    
    if (result.ok) {
      console.log(`[ae][flake] ✅ Run ${i + 1} passed`);
    } else if (isErr(result)) { 
      fails++; 
      seeds.push(seed);
      failedSeeds.push({ seed, run: i + 1 });
      const errorMsg = 'detail' in result.error ? result.error.detail : result.error.code;
      console.log(`[ae][flake] ❌ Run ${i + 1} failed with seed=${seed} (${errorMsg ?? 'unknown error'})`);
    }
  }
  
  console.log(`\n[ae][flake] Summary: failed ${fails}/${times}` + (seeds.length ? ` seeds=${seeds.join(',')}` : ''));
  
  if (fails > 0) {
    console.log(`[ae][flake] 🚨 Flakiness detected! Tests failed ${fails} times out of ${times} runs.`);
    console.log(`[ae][flake] Failed runs and seeds:`);
    failedSeeds.forEach(({ run, seed }) => {
      console.log(`[ae][flake]   Run ${run}: seed=${seed}`);
    });
    
    console.log(`[ae][flake] Reproduction commands:`);
    if (testRunner === 'vitest') {
      failedSeeds.forEach(({ run, seed }) => {
        const reproArgs = ['vitest', 'run'];
        if (testFiles.length > 0) {
          reproArgs.push(...testFiles);
        } else if (finalPattern) {
          reproArgs.push(finalPattern);
        }
        if (workers) {
          const parsedWorkers = parseWorkers(workers);
          if (parsedWorkers) {
            reproArgs.push('--maxWorkers', parsedWorkers);
          }
        }
        console.log(`[ae][flake]   Run ${run}: AE_SEED=${seed} npx ${reproArgs.join(' ')}`);
      });
    } else {
      failedSeeds.forEach(({ run, seed }) => {
        const reproArgs = ['jest'];
        if (finalPattern) reproArgs.push('--testPathPattern', finalPattern);
        if (workers) {
          const parsedWorkers = parseWorkers(workers);
          if (parsedWorkers) reproArgs.push('--maxWorkers', parsedWorkers);
        }
        console.log(`[ae][flake]   Run ${run}: AE_SEED=${seed} npx ${reproArgs.join(' ')}`);
      });
    }
  } else {
    console.log(`[ae][flake] ✅ No flakiness detected. All ${times} runs passed.`);
  }
  
  if (fails > 0) {
    return err({ code: 'E_EXEC', step: 'qa:flake', detail: `${fails}/${times} runs failed` });
  }
  
  return ok({ failures: fails, total: times, seeds });
}
