import * as os from 'node:os';
import { glob, hasMagic } from 'glob';
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

// Windows CreateProcess limits the complete command line to 32,767 UTF-16
// code units. Keep a conservative budget after accounting for the executable,
// fixed runner flags, quoting, and package-manager shim expansion.
export const VITEST_COMMAND_LINE_BUDGET = 24_000;

function estimatedQuotedArgLength(value: string): number {
  // Doubling is a safe upper bound for Windows quote/backslash escaping.
  return (value.length * 2) + 3;
}

export function chunkVitestFileArgs(
  files: string[],
  fixedArgs: string[],
  budget = VITEST_COMMAND_LINE_BUDGET,
): string[][] {
  const fixedLength = fixedArgs.reduce((total, value) => total + estimatedQuotedArgLength(value), 0);
  if (fixedLength >= budget) {
    throw new Error(`fixed Vitest arguments exceed the command-line budget (${budget})`);
  }

  const batches: string[][] = [];
  let current: string[] = [];
  let currentLength = fixedLength;

  for (const file of files) {
    const fileLength = estimatedQuotedArgLength(file);
    if (fixedLength + fileLength > budget) {
      throw new Error(`test path exceeds the command-line budget: ${file}`);
    }
    if (current.length > 0 && currentLength + fileLength > budget) {
      batches.push(current);
      current = [];
      currentLength = fixedLength;
    }
    current.push(file);
    currentLength += fileLength;
  }

  if (current.length > 0) {
    batches.push(current);
  }
  return batches;
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
    const portablePattern = toPortableTestPath(pattern);
    try {
      const files = (await glob(portablePattern, { nodir: true })).map(toPortableTestPath);
      return { pattern: portablePattern, files: files.sort((left, right) => left.localeCompare(right)) };
    } catch {
      return { pattern: portablePattern, files: [] };
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
  const concreteFallback = finalPattern && !hasMagic(finalPattern) ? toPortableTestPath(finalPattern) : null;
  
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
    if (hasMagic(finalPattern)) {
      return err({
        code: 'E_CONFIG',
        key: 'pattern',
        detail: `glob pattern matched no test files: ${finalPattern}`,
      });
    }
  }

  let command: string;
  let baseArgs: string[];
  if (pm === 'pnpm') {
    command = 'pnpm';
    baseArgs = ['test'];
  } else if (pm === 'npx') {
    command = 'npx';
    baseArgs = testRunner === 'vitest' ? ['vitest', 'run'] : ['jest'];
  } else {
    command = pm;
    baseArgs = ['run', 'test'];
  }

  const runnerOptionArgs: string[] = [];
  if (workers) {
    const parsedWorkers = parseWorkers(workers);
    if (parsedWorkers) {
      if (testRunner === 'vitest') {
        console.log(`[ae][flake] Warning: Using --maxWorkers ${parsedWorkers} (may conflict with existing config)`);
      }
      runnerOptionArgs.push('--maxWorkers', parsedWorkers);
    }
  }

  let vitestFileBatches: string[][] = [[]];
  if (testRunner === 'vitest') {
    try {
      if (testFiles.length > 0) {
        vitestFileBatches = chunkVitestFileArgs(
          testFiles,
          [command, ...baseArgs, ...runnerOptionArgs],
        );
      } else if (concreteFallback) {
        vitestFileBatches = [[concreteFallback]];
      }
    } catch (error) {
      return err({
        code: 'E_CONFIG',
        key: 'pattern',
        detail: error instanceof Error ? error.message : 'failed to prepare bounded Vitest arguments',
      });
    }
    if (vitestFileBatches.length > 1) {
      console.log(`[ae][flake] Split ${fileCount} matched files into ${vitestFileBatches.length} command-line-safe batches`);
    }
  }
  
  for (let i = 0; i < times; i++) {
    const seed = Math.floor(Math.random() * 1e9);
    console.log(`[ae][flake] Run ${i + 1}/${times} (seed=${seed})`);
    
    let runFailed = false;
    let firstErrorDetail: string | undefined;
    const runDeadline = Date.now() + timeoutMs;

    if (testRunner === 'vitest') {
      for (let batchIndex = 0; batchIndex < vitestFileBatches.length; batchIndex += 1) {
        const remainingTimeoutMs = runDeadline - Date.now();
        if (remainingTimeoutMs <= 0) {
          runFailed = true;
          firstErrorDetail ??= `flake run exceeded the total timeout (${timeoutMs}ms)`;
          break;
        }
        const batch = vitestFileBatches[batchIndex] ?? [];
        const args = [...baseArgs, ...batch, ...runnerOptionArgs];
        const stepName = vitestFileBatches.length === 1
          ? `flake-run-${i + 1}`
          : `flake-run-${i + 1}-batch-${batchIndex + 1}-of-${vitestFileBatches.length}`;
        const result = await run(stepName, command, args, {
          env: { ...process.env, AE_SEED: String(seed) },
          stdio: 'inherit',
          timeout: vitestFileBatches.length === 1 ? timeoutMs : remainingTimeoutMs,
          killSignal: 'SIGTERM',
        });
        if (isErr(result)) {
          runFailed = true;
          if (!firstErrorDetail) {
            firstErrorDetail = 'detail' in result.error ? result.error.detail : result.error.code;
          }
        }
      }
    } else if (testRunner === 'jest') {
      const args = [...baseArgs];
      if (finalPattern) {
        args.push('--testPathPattern', finalPattern);
      }
      args.push(...runnerOptionArgs);
      const result = await run(`flake-run-${i + 1}`, command, args, {
        env: { ...process.env, AE_SEED: String(seed) },
        stdio: 'inherit',
        timeout: timeoutMs,
        killSignal: 'SIGTERM',
      });
      if (isErr(result)) {
        runFailed = true;
        firstErrorDetail = 'detail' in result.error ? result.error.detail : result.error.code;
      }
    }

    if (!runFailed) {
      console.log(`[ae][flake] ✅ Run ${i + 1} passed`);
    } else {
      fails++;
      seeds.push(seed);
      failedSeeds.push({ seed, run: i + 1 });
      console.log(`[ae][flake] ❌ Run ${i + 1} failed with seed=${seed} (${firstErrorDetail ?? 'unknown error'})`);
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
        vitestFileBatches.forEach((batch, batchIndex) => {
          const reproArgs = ['vitest', 'run', ...batch, ...runnerOptionArgs];
          const batchLabel = vitestFileBatches.length === 1 ? '' : ` batch ${batchIndex + 1}/${vitestFileBatches.length}`;
          console.log(`[ae][flake]   Run ${run}${batchLabel}: AE_SEED=${seed} npx ${reproArgs.join(' ')}`);
        });
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
