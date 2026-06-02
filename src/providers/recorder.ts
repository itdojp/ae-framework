import type { LLM } from './index.js';
import { chmod, mkdir, readFile, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import * as path from 'node:path';
import { safeErrorForLogging, safeStringForCassette } from '../security/sensitive-redaction.js';

// Cache echo provider to avoid repeated imports
let echoProviderPromise: Promise<{ default: LLM }> | null = null;

const isErrnoException = (value: unknown): value is { code: string } => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  if (!('code' in value)) {
    return false;
  }
  return typeof (value as { code?: unknown }).code === 'string';
};

const hashValue = (value: string | undefined): string | undefined => {
  if (typeof value !== 'string') {
    return undefined;
  }
  return createHash('sha256').update(value).digest('hex').slice(0, 16);
};

export function withRecorder(base: LLM, opts?: { dir?: string; replay?: boolean; record?: boolean }) : LLM {
  const dir = opts?.dir ?? 'artifacts/cassettes';
  const replay = opts?.replay ?? false;
  const record = opts?.record ?? false;
  
  return {
    name: `rec(${base.name})`,
    async complete(input) {
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
          // Try hash-based file first, then fall back to legacy file.
          let content: unknown;
          const readCassette = async (filePath: string): Promise<unknown> => {
            try {
              const parsed: unknown = JSON.parse(await readFile(filePath, 'utf8'));
              return parsed;
            } catch (innerError) {
              if (innerError instanceof SyntaxError) {
                throw new Error('Cassette file is invalid JSON');
              }
              throw innerError;
            }
          };
          try {
            content = await readCassette(hashFile);
          } catch (innerError) {
            if (isErrnoException(innerError) && innerError.code === 'ENOENT') {
              content = await readCassette(legacyFile);
            } else {
              throw innerError;
            }
          }
          const hit = content as { output: string };
          if (typeof hit.output !== 'string') {
            throw new Error(`Cassette file is missing a string output: ${hashFile}`);
          }
          return hit.output;
        } catch (error) {
          if (isErrnoException(error) && error.code === 'ENOENT') {
            throw new Error(`Cassette not found: ${hashFile}. Run with --record first.`);
          } else {
            throw error;
          }
        }
      }

      if (!record) {
        return await base.complete(input);
      }

      await mkdir(dir, { recursive: true, mode: 0o700 });
      if (process.platform !== 'win32') {
        await chmod(dir, 0o700);
      }

      console.warn(
        `[recorder] RECORD mode persists redacted LLM cassettes in ${dir}. ` +
          'Review retention policy and do not publish cassette artifacts containing sensitive context.'
      );
      
      let out: string;
      try {
        out = await base.complete(input);
      } catch (error) {
        // If base provider fails (including timeout), use echo as fallback
        console.warn('[recorder] Base provider failed, using echo fallback:', safeErrorForLogging(error));
        if (!echoProviderPromise) {
          echoProviderPromise = import('./llm-echo.js');
        }
        const echoProvider = (await echoProviderPromise).default;
        out = await echoProvider.complete(input);
      }
      
      const cassette = {
        schemaVersion: 1,
        redacted: true,
        inputHash: hashKey,
        input: {
          promptHash: hashValue(input.prompt),
          systemHash: hashValue(input.system),
          ...(typeof input.temperature === 'number' ? { temperature: input.temperature } : {}),
        },
        output: safeStringForCassette(out),
      };

      // Always save with hash-based filename for new recordings.
      await writeFile(hashFile, JSON.stringify(cassette, null, 2), { mode: 0o600 });
      if (process.platform !== 'win32') {
        await chmod(hashFile, 0o600);
      }
      return out;
    }
  };
}
