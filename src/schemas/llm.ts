import { z } from 'zod';

export const OpenAIChat = z.object({
  choices: z.array(z.object({ message: z.object({ content: z.string().default('') }) })).nonempty()
}).passthrough();

export const AnthropicMsg = z.object({
  content: z.any()
}).passthrough();

export const GeminiResp = z.object({
  response: z.any()
}).passthrough();

// Benchmark JSON schema for parsing artifacts/bench.json
export const BenchmarkResult = z.object({
  summary: z.array(z.object({
    name: z.string(),
    hz: z.number(),
    meanMs: z.number(),
    sdMs: z.number().optional(),
    samples: z.number().optional()
  })),
  date: z.string().optional(),
  env: z.any().optional(),
  config: z.any().optional()
}).passthrough();