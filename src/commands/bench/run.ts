import { Bench } from 'tinybench';
import * as os from 'node:os';
import { mkdir, writeFile } from 'node:fs/promises';
import { loadConfig } from '../../core/config.js';
import { getSeed } from '../../core/seed.js';

function percentile(samples: number[], ratio: number): number {
  if (samples.length === 0) {
    return 0;
  }
  const sorted = [...samples].sort((left, right) => left - right);
  const index = Math.max(0, Math.ceil(sorted.length * ratio) - 1);
  return sorted[Math.min(index, sorted.length - 1)] ?? 0;
}

function downsample(samples: number[], maxSamples: number): number[] {
  if (samples.length <= maxSamples) {
    return samples;
  }
  // Cap percentile input size to keep bench post-processing bounded even for ultra-fast tasks.
  const sampled: number[] = [];
  const step = Math.ceil(samples.length / maxSamples);
  for (let index = 0; index < samples.length; index += step) {
    const value = samples[index];
    if (value !== undefined) {
      sampled.push(value);
    }
  }
  return sampled;
}

function roundMetric(value: number, digits = 3): number {
  if (!Number.isFinite(value)) {
    return 0;
  }
  return Number(value.toFixed(digits));
}

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
  
  let peakRssBytes = process.memoryUsage().rss;
  const rssSampler = setInterval(() => {
    peakRssBytes = Math.max(peakRssBytes, process.memoryUsage().rss);
  }, 10);

  try {
    await bench.run();
  } finally {
    clearInterval(rssSampler);
    peakRssBytes = Math.max(peakRssBytes, process.memoryUsage().rss);
  }
  
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
  const p95InputSamplesMs: number[] = [];
  const coldStartSamplesMs: number[] = [];
  let failedTasks = 0;
  const summary = bench.tasks.map(task => {
    const samplesMs = (task.result?.samples ?? []).map(sample => sample * 1000);
    const sampledForP95 = downsample(samplesMs, 5000);
    const coldStartMs = samplesMs[0] ?? 0;
    const hasFailure = Boolean(task.result?.error) || Boolean(task.result?.aborted) || !task.result;
    if (hasFailure) {
      failedTasks += 1;
    }
    for (const sampleMs of sampledForP95) {
      p95InputSamplesMs.push(sampleMs);
    }
    if (samplesMs.length > 0) {
      coldStartSamplesMs.push(coldStartMs);
    }

    return {
      name: task.name,
      hz: task.result?.hz ?? 0,
      meanMs: (task.result?.mean ?? 0) * 1000,
      sdMs: (task.result?.sd ?? 0) * 1000,
      samples: samplesMs.length,
      p95: percentile(sampledForP95, 0.95),
      errorRate: hasFailure ? 100 : 0,
      coldStartMs,
    };
  });

  const totalTasks = bench.tasks.length;
  const metrics = {
    p95: roundMetric(percentile(p95InputSamplesMs, 0.95), 3),
    errorRate: roundMetric(totalTasks === 0 ? 0 : (failedTasks / totalTasks) * 100, 2),
    coldStartMs: roundMetric(
      coldStartSamplesMs.length === 0
        ? 0
        : coldStartSamplesMs.reduce((sum, value) => sum + value, 0) / coldStartSamplesMs.length,
      3
    ),
    peakRssMb: roundMetric(peakRssBytes / (1024 * 1024), 2),
  };
  
  // Ensure stable JSON schema with minimum required fields
  const payload = {
    schemaVersion: 'benchmark-report/v1',
    summary: summary.map(task => ({
      name: task.name,
      meanMs: roundMetric(task.meanMs, 3),
      hz: roundMetric(task.hz, 3),
      sdMs: roundMetric(task.sdMs, 3),
      samples: task.samples,
      p95: roundMetric(task.p95, 3),
      errorRate: roundMetric(task.errorRate, 2),
      coldStartMs: roundMetric(task.coldStartMs, 3),
    })),
    metrics,
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
- P95(ms): ${payload.metrics.p95.toFixed(3)}
- Error Rate(%): ${payload.metrics.errorRate.toFixed(2)}
- Cold Start(ms): ${payload.metrics.coldStartMs.toFixed(3)}
- Peak RSS(MB): ${payload.metrics.peakRssMb.toFixed(2)}

| task | mean(ms) | p95(ms) | stdev(ms) | error(%) | hz |
|---|---:|---:|---:|---:|---:|
${summary.map(s => `| ${s.name} | ${s.meanMs.toFixed(3)} | ${s.p95.toFixed(3)} | ${s.sdMs.toFixed(3)} | ${s.errorRate.toFixed(2)} | ${s.hz.toFixed(1)} |`).join('\n')}
`;
  
  await writeFile('artifacts/bench.md', markdown);
  
  console.log('[ae:bench] artifacts generated -> artifacts/bench.{json,md}');
}
