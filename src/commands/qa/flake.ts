import { execa } from 'execa';
import * as os from 'node:os';

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

export async function qaFlake(options: QAFlakeOptions = {}) {
  const { times = 10, pattern, timeoutMs = 300000, workers } = options;
  const pm = await detectPM();
  const testRunner = await detectTestRunner();
  let fails = 0; 
  const seeds: number[] = [];
  const failedSeeds: { seed: number; run: number }[] = [];
  
  console.log(`[ae][flake] Running tests ${times} times to detect flakiness...`);
  console.log(`[ae][flake] Package manager: ${pm}`);
  console.log(`[ae][flake] Test runner: ${testRunner}`);
  if (pattern) console.log(`[ae][flake] Pattern: ${pattern}`);
  if (timeoutMs !== 300000) console.log(`[ae][flake] Timeout: ${timeoutMs}ms`);
  if (workers) console.log(`[ae][flake] Workers: ${workers}`);
  
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
      // Vitest options
      if (pattern) {
        // Try to use as directory pattern first, or as test name pattern
        if (pattern.includes('/') || pattern.includes('*')) {
          args.push('--dir', pattern);
        } else {
          args.push('--testNamePattern', pattern);
        }
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
      // Jest options  
      if (pattern) {
        args.push('--testPathPattern', pattern);
      }
      if (workers) {
        const parsedWorkers = parseWorkers(workers);
        if (parsedWorkers) {
          args.push('--maxWorkers', parsedWorkers);
        }
      }
    }
    
    const r = await execa(command, args, {
      env: { ...process.env, AE_SEED: String(seed) }, 
      reject: false, 
      stdio: 'inherit',
      timeout: timeoutMs,
      killSignal: 'SIGTERM'
    });
    
    if (r.exitCode !== 0) { 
      fails++; 
      seeds.push(seed);
      failedSeeds.push({ seed, run: i + 1 });
      console.log(`[ae][flake] ❌ Run ${i + 1} failed with seed=${seed} (exit ${r.exitCode})`);
    } else {
      console.log(`[ae][flake] ✅ Run ${i + 1} passed`);
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
        if (pattern) {
          if (pattern.includes('/') || pattern.includes('*')) {
            reproArgs.push('--dir', pattern);
          } else {
            reproArgs.push('--testNamePattern', pattern);
          }
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
        if (pattern) reproArgs.push('--testPathPattern', pattern);
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
  
  process.exit(fails ? 1 : 0);
}