import { Bench } from 'tinybench';
import * as os from 'node:os';
import { mkdir, writeFile } from 'node:fs/promises';
import { loadConfig } from '../../core/config.js';
import { getSeed } from '../../core/seed.js';

function percentile(samples: number[], ratio: number): number {
  if (samples.length === 0) {
    throw new Error('[ae:bench] percentile requires at least one sample');
  }
  const sorted = [...samples].sort((left, right) => left - right);
  const index = Math.max(0, Math.ceil(sorted.length * ratio) - 1);
  return sorted[Math.min(index, sorted.length - 1)] ?? 0;
}

function roundMetric(value: number, digits = 3): number {
  if (!Number.isFinite(value)) {
    throw new Error(`[ae:bench] metric is not finite: ${value}`);
  }
  return Number(value.toFixed(digits));
}

export async function benchRun() {
  const cfg = await loadConfig();
  const seed = getSeed() ?? cfg.bench.seed;

  const iterations = Math.max(1, Math.trunc(cfg.bench.iterations));
  const warmupMs = Math.max(0, Math.trunc(cfg.bench.warmupMs));

  const benchmarkArtifactsDir = 'artifacts/reference/benchmarks';
  const benchmarkJsonPath = `${benchmarkArtifactsDir}/bench.json`;
  const benchmarkMarkdownPath = `${benchmarkArtifactsDir}/bench.md`;

  // Ensure benchmark artifact directory exists
  await mkdir(benchmarkArtifactsDir, { recursive: true });

  const bench = new Bench({
    iterations,
    warmup: warmupMs > 0,
    warmupTime: warmupMs,
  });

  // Placeholder task: will be replaced with actual processing later
  bench.add('noop', () => Math.sqrt(144));

  console.log(`[ae:bench] running with seed=${seed}, iterations=${iterations}, warmup=${warmupMs}ms`);

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
    const result = task.result;
    const hasFailure = !result || Boolean(result.error) || Boolean(result.aborted);
    if (hasFailure) {
      failedTasks += 1;
      const reason = result?.error?.message || 'task failed or aborted';
      throw new Error(`[ae:bench] task failed: ${task.name}: ${reason}`);
    }
    const samplesMs = result.samples.map(sample => sample * 1000);
    if (samplesMs.length === 0) {
      throw new Error(`[ae:bench] task has no samples: ${task.name}`);
    }
    const hz = result.hz;
    const meanMs = result.mean * 1000;
    const sdMs = result.sd * 1000;
    if (![hz, meanMs, sdMs].every(Number.isFinite)) {
      throw new Error(`[ae:bench] task metrics are not finite: ${task.name}`);
    }
    const coldStartMs = samplesMs[0] as number;
    for (const sampleMs of samplesMs) {
      p95InputSamplesMs.push(sampleMs);
    }
    coldStartSamplesMs.push(coldStartMs);

    return {
      name: task.name,
      hz,
      meanMs,
      sdMs,
      samples: samplesMs.length,
      p95: percentile(samplesMs, 0.95),
      errorRate: hasFailure ? 100 : 0,
      coldStartMs,
    };
  });

  const totalTasks = bench.tasks.length;
  if (totalTasks === 0) {
    throw new Error('[ae:bench] no benchmark tasks are registered');
  }
  if (coldStartSamplesMs.length === 0) {
    throw new Error('[ae:bench] cold start metric cannot be computed');
  }

  const metrics = {
    p95: roundMetric(percentile(p95InputSamplesMs, 0.95), 3),
    errorRate: roundMetric((failedTasks / totalTasks) * 100, 2),
    coldStartMs: roundMetric(coldStartSamplesMs.reduce((sum, value) => sum + value, 0) / coldStartSamplesMs.length, 3),
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
      config: {
        ...cfg.bench,
        warmupMs,
        iterations,
      },
    },
  };

  // Write JSON report
  await writeFile(benchmarkJsonPath, JSON.stringify(payload, null, 2));

  // Write Markdown report
  const markdown = `# Bench Report
- Date: ${payload.meta.date}
- Node: ${env.node}
- Machine: ${env.platform}/${env.arch} ${env.cpu}
- Iter: ${iterations}, Warmup: ${warmupMs}ms, Seed: ${env.seed}
- P95(ms): ${payload.metrics.p95.toFixed(3)}
- Error Rate(%): ${payload.metrics.errorRate.toFixed(2)}
- Cold Start(ms): ${payload.metrics.coldStartMs.toFixed(3)}
- Peak RSS(MB): ${payload.metrics.peakRssMb.toFixed(2)}

| task | mean(ms) | p95(ms) | stdev(ms) | error(%) | hz |
|---|---:|---:|---:|---:|---:|
${summary.map(s => `| ${s.name} | ${s.meanMs.toFixed(3)} | ${s.p95.toFixed(3)} | ${s.sdMs.toFixed(3)} | ${s.errorRate.toFixed(2)} | ${s.hz.toFixed(1)} |`).join('\n')}
`;

  await writeFile(benchmarkMarkdownPath, markdown);

  console.log(`[ae:bench] artifacts generated -> ${benchmarkArtifactsDir}/bench.{json,md}`);
}
