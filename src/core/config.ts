import { z } from 'zod';
import { pathToFileURL } from 'node:url';
import { readFile } from 'node:fs/promises';

export const AeConfigSchema = z.object({
  tddGuard: z.object({
    enabled: z.boolean().default(true),
    onlyChanged: z.boolean().default(true),
    changedSince: z.string().default('origin/main'),
    include: z.array(z.string()).default(['src/**/*.ts', 'tests/**/*.ts']),
    exclude: z.array(z.string()).default(['**/*.md']),
    allowSkipWithEnv: z.string().default('AE_SKIP_GUARD'),
    ciOnly: z.boolean().default(false),
  }).default({}),
  qa: z.object({
    coverageThreshold: z.object({
      branches: z.number().default(90),
      lines: z.number().default(90),
      functions: z.number().default(90),
      statements: z.number().default(90),
    }).default({})
  }).default({}),
  bench: z.object({
    warmupMs: z.number().default(300),
    iterations: z.number().default(30),
    seed: z.number().default(12345),
  }).default({}),
}).strict();

export type AeConfig = z.infer<typeof AeConfigSchema>;

export async function loadConfig(): Promise<AeConfig> {
  // ae.config.ts/js/json の順に探す。なければデフォルト
  const base: Partial<AeConfig> = {};
  const cwd = process.cwd();
  
  for (const filename of ['ae.config.ts', 'ae.config.js', 'ae.config.json']) {
    try {
      const filePath = `${cwd}/${filename}`;
      
      if (filename.endsWith('.json')) {
        const content = await readFile(filePath, 'utf8');
        const raw = JSON.parse(content);
        Object.assign(base, raw);
        break;
      } else {
        // TypeScript/JavaScript files
        const fileUrl = pathToFileURL(filePath).href;
        const mod = await import(fileUrl);
        Object.assign(base, mod.default ?? mod);
        break;
      }
    } catch (error) {
      // File not found, try next
      continue;
    }
  }
  
  return AeConfigSchema.parse(base);
}