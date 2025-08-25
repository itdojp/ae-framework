import type { LLM } from './index.js';
import { readFile, writeFile, mkdir, access } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import * as path from 'node:path';

export function withRecorder(base: LLM, opts?: { dir?: string; replay?: boolean }) : LLM {
  const dir = opts?.dir ?? 'artifacts/cassettes';
  const replay = opts?.replay ?? false;
  
  return {
    name: `rec(${base.name})`,
    async complete(input) {
      await mkdir(dir, { recursive: true });
      
      // Generate hash-based key for better reliability
      const hashKey = createHash('sha1')
        .update(JSON.stringify({ system: input.system, prompt: input.prompt }))
        .digest('hex')
        .slice(0, 16);
      
      // Legacy key format for backward compatibility
      const legacyKey = `${(input.system ?? '').slice(0,24)}__${input.prompt.slice(0,48)}`
        .replace(/\W+/g,'_')
        .replace(/^_+|_+$/g,'');
      
      const hashFile = path.join(dir, `${hashKey}.json`);
      const legacyFile = path.join(dir, `${legacyKey}.json`);
      
      if (replay) {
        try {
          // Try hash-based file first
          let file = hashFile;
          try {
            await access(hashFile);
          } catch {
            // Fall back to legacy file if hash file doesn't exist
            file = legacyFile;
          }
          
          const hit = JSON.parse(await readFile(file, 'utf8'));
          return hit.output;
        } catch (error) {
          if (error && typeof error === 'object' && 'code' in error && (error as any).code === 'ENOENT') {
            throw new Error(`Cassette not found: ${hashFile} or ${legacyFile}. Run with --record first.`);
          } else if (error instanceof SyntaxError) {
            throw new Error(`Cassette file is invalid JSON.`);
          } else {
            throw error;
          }
        }
      }
      
      let out: string;
      try {
        out = await base.complete(input);
      } catch (error) {
        // If base provider fails (including timeout), use echo as fallback
        console.warn(`[recorder] Base provider failed, using echo fallback:`, error instanceof Error ? error.message : 'Unknown error');
        const echoProvider = (await import('./llm-echo.js')).default;
        out = await echoProvider.complete(input);
      }
      
      // Always save with hash-based filename for new recordings
      await writeFile(hashFile, JSON.stringify({ input, output: out }, null, 2));
      return out;
    }
  };
}