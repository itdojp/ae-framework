import { execa } from 'execa';

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

export async function qaFlake(times = 10) {
  const pm = await detectPM();
  let fails = 0; 
  const seeds: number[] = [];
  
  console.log(`[ae][flake] Running tests ${times} times to detect flakiness...`);
  console.log(`[ae][flake] Package manager: ${pm}`);
  
  for (let i = 0; i < times; i++) {
    const seed = Math.floor(Math.random() * 1e9);
    console.log(`[ae][flake] Run ${i + 1}/${times} (seed=${seed})`);
    
    const args = pm === 'pnpm' ? ['test'] : pm === 'npx' ? ['vitest', 'run'] : ['run', 'test'];
    const r = await execa(pm === 'npx' ? 'npx' : pm, args, {
      env: { ...process.env, AE_SEED: String(seed) }, 
      reject: false, 
      stdio: 'inherit'
    });
    
    if (r.exitCode !== 0) { 
      fails++; 
      seeds.push(seed); 
      console.log(`[ae][flake] ❌ Run ${i + 1} failed with seed=${seed}`);
    } else {
      console.log(`[ae][flake] ✅ Run ${i + 1} passed`);
    }
  }
  
  console.log(`\n[ae][flake] Summary: failed ${fails}/${times}` + (seeds.length ? ` seeds=${seeds.join(',')}` : ''));
  
  if (fails > 0) {
    console.log(`[ae][flake] 🚨 Flakiness detected! Tests failed ${fails} times out of ${times} runs.`);
    console.log(`[ae][flake] Failed seeds: ${seeds.join(', ')}`);
    console.log(`[ae][flake] To reproduce failures, run: AE_SEED=<seed> npm test`);
  } else {
    console.log(`[ae][flake] ✅ No flakiness detected. All ${times} runs passed.`);
  }
  
  process.exit(fails ? 1 : 0);
}