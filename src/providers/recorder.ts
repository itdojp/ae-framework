import type { LLM } from './index.js';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';

export function withRecorder(base: LLM, opts?: { dir?: string; replay?: boolean }) : LLM {
  const dir = opts?.dir ?? 'artifacts/cassettes';
  const replay = opts?.replay ?? false;
  
  return {
    name: `rec(${base.name})`,
    async complete(input) {
      await mkdir(dir, { recursive: true });
      
      const key = `${(input.system ?? '').slice(0,24)}__${input.prompt.slice(0,48)}`
        .replace(/\W+/g,'_')
        .replace(/^_+|_+$/g,'');
      const file = path.join(dir, `${key}.json`);
      
      if (replay) {
        try {
          const hit = JSON.parse(await readFile(file, 'utf8'));
          return hit.output;
        } catch (error) {
          throw new Error(`Cassette not found: ${file}. Run with --record first.`);
        }
      }
      
      const out = await base.complete(input);
      await writeFile(file, JSON.stringify({ input, output: out }, null, 2));
      return out;
    }
  };
}