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
  schemaVersion: z.string().optional(),
  summary: z.array(z.object({
    name: z.string(),
    hz: z.number(),
    meanMs: z.number(),
    sdMs: z.number().optional(),
    samples: z.number().optional(),
    p95: z.number().optional(),
    errorRate: z.number().optional(),
    coldStartMs: z.number().optional()
  })),
  metrics: z.object({
    p95: z.number(),
    errorRate: z.number(),
    coldStartMs: z.number(),
    peakRssMb: z.number(),
  }).optional(),
  meta: z.object({
    date: z.string().optional(),
    env: z.unknown().optional(),
    config: z.unknown().optional(),
  }).optional(),
  date: z.string().optional(),
  env: z.unknown().optional(),
  config: z.unknown().optional()
}).passthrough();
