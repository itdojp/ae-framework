import { Bench } from 'tinybench';
import * as os from 'node:os';
import { mkdir, writeFile } from 'node:fs/promises';
import { loadConfig } from '../../core/config.js';
import { getSeed } from '../../core/seed.js';

export async function benchRun() {
  const cfg = await loadConfig();
  const seed = getSeed() ?? cfg.bench.seed;
  
  // Ensure artifacts directory exists
  await mkdir('artifacts', { recursive: true });
  
  const bench = new Bench({ 
    iterations: cfg.bench.iterations 
  });
  
  // Placeholder task: will be replaced with actual processing later
  bench.add('noop', () => Math.sqrt(144));
  
  console.log(`[ae:bench] running with seed=${seed}, iterations=${cfg.bench.iterations}, warmup=${cfg.bench.warmupMs}ms`);
  
  await bench.run();
  
  // Gather environment information
  const env = {
    node: process.version,
    platform: os.platform(),
    arch: os.arch(),
    cpu: os.cpus()?.[0]?.model || 'unknown',
    totalMem: os.totalmem(),
    seed,
  };
  
  // Create summary
  const summary = bench.tasks.map(task => ({
    name: task.name,
    hz: task.result?.hz,
    meanMs: (task.result?.mean ?? 0) * 1000,
    sdMs: (task.result?.sd ?? 0) * 1000,
    samples: task.result?.samples?.length ?? 0,
  }));
  
  // Ensure stable JSON schema with minimum required fields
  const payload = {
    summary: summary.map(task => ({
      name: task.name,
      meanMs: task.meanMs || 0,
      hz: task.hz || 0,
    })),
    meta: {
      date: new Date().toISOString(),
      env,
      config: cfg.bench,
    },
  };
  
  // Write JSON report
  await writeFile('artifacts/bench.json', JSON.stringify(payload, null, 2));
  
  // Write Markdown report
  const markdown = `# Bench Report
- Date: ${payload.meta.date}
- Node: ${env.node}
- Machine: ${env.platform}/${env.arch} ${env.cpu}
- Iter: ${cfg.bench.iterations}, Warmup: ${cfg.bench.warmupMs}ms, Seed: ${env.seed}

| task | mean(ms) | stdev(ms) | hz |
|---|---:|---:|---:|
${summary.map(s => `| ${s.name} | ${s.meanMs.toFixed(3)} | ${s.sdMs.toFixed(3)} | ${s.hz?.toFixed(1) || 'N/A'} |`).join('\n')}
`;
  
  await writeFile('artifacts/bench.md', markdown);
  
  console.log('[ae:bench] artifacts generated -> artifacts/bench.{json,md}');
}