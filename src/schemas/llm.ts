import { z } from 'zod';

export const OpenAIChat = z.object({
  choices: z.array(z.object({ message: z.object({ content: z.string().default('') }) })).nonempty()
}).passthrough();

export const AnthropicMsg = z.object({
  content: z.unknown()
}).passthrough();

export const GeminiResp = z.object({
  response: z.unknown()
}).passthrough();

// Benchmark JSON schema for parsing artifacts/bench.json
export const BenchmarkResult = z.object({
  schemaVersion: z.literal('benchmark-report/v1'),
  summary: z.array(z.object({
    name: z.string(),
    hz: z.number().nonnegative(),
    meanMs: z.number().nonnegative(),
    sdMs: z.number().nonnegative(),
    samples: z.number().int().nonnegative(),
    p95: z.number().nonnegative(),
    errorRate: z.number().min(0).max(100),
    coldStartMs: z.number().nonnegative()
  })).min(1),
  metrics: z.object({
    p95: z.number().nonnegative(),
    errorRate: z.number().min(0).max(100),
    coldStartMs: z.number().nonnegative(),
    peakRssMb: z.number().nonnegative(),
  }),
  meta: z.object({
    date: z.string().min(1),
    env: z.object({
      node: z.string().min(1),
      platform: z.string().min(1),
      arch: z.string().min(1),
      cpu: z.string().min(1),
      totalMem: z.number().int().nonnegative(),
      seed: z.number(),
    }).passthrough(),
    config: z.object({
      warmupMs: z.number().int().nonnegative(),
      iterations: z.number().int().nonnegative(),
      seed: z.number(),
    }).passthrough(),
  }),
}).passthrough();
