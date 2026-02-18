import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const scriptPath = resolve('scripts/codex/adapter-stdio.mjs');
const requestSchemaPath = resolve('schema/codex-task-request.schema.json');
const responseSchemaPath = resolve('schema/codex-task-response.schema.json');

function parseJsonLine(stdout: string) {
  const trimmed = stdout.trim();
  expect(trimmed.length).toBeGreaterThan(0);
  return JSON.parse(trimmed);
}

function withTempRepo(run: (dir: string) => void) {
  const dir = mkdtempSync(join(tmpdir(), 'codex-stdio-'));
  try {
    run(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function writeAdapterModule(tempRoot: string, moduleBody: string) {
  const adapterPath = join(tempRoot, 'dist', 'src', 'agents', 'codex-task-adapter.js');
  mkdirSync(join(tempRoot, 'dist', 'src', 'agents'), { recursive: true });
  writeFileSync(adapterPath, moduleBody, 'utf8');
}

function runAdapter(tempRoot: string, input: string) {
  return spawnSync(process.execPath, [scriptPath], {
    cwd: tempRoot,
    input,
    encoding: 'utf8',
    env: {
      ...process.env,
      CODEX_TASK_REQUEST_SCHEMA: requestSchemaPath,
      CODEX_TASK_RESPONSE_SCHEMA: responseSchemaPath,
    },
  });
}

describe('codex adapter stdio contract', () => {
  it('returns exit 0 and TaskResponse JSON for valid request', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'ok',
                analysis: 'analysis',
                recommendations: ['r1'],
                nextActions: ['n1'],
                warnings: [],
                shouldBlockProgress: false
              };
            }
          };
        }
      `);

      const result = runAdapter(
        tempRoot,
        JSON.stringify({ description: 'run intent', subagent_type: 'intent', context: {} }),
      );

      expect(result.status).toBe(0);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          summary: 'ok',
          shouldBlockProgress: false,
        }),
      );
    });
  });

  it('returns exit 2 when response shouldBlockProgress is true', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'blocked',
                analysis: 'analysis',
                recommendations: [],
                nextActions: [],
                warnings: ['w1'],
                shouldBlockProgress: true
              };
            }
          };
        }
      `);

      const result = runAdapter(
        tempRoot,
        JSON.stringify({ prompt: 'run formal', subagent_type: 'formal' }),
      );

      expect(result.status).toBe(2);
      const payload = parseJsonLine(result.stdout);
      expect(payload.shouldBlockProgress).toBe(true);
    });
  });

  it('returns exit 3 with machine-readable error for invalid request schema', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'ok',
                analysis: 'ok',
                recommendations: [],
                nextActions: [],
                warnings: [],
                shouldBlockProgress: false
              };
            }
          };
        }
      `);

      const result = runAdapter(
        tempRoot,
        JSON.stringify({ description: 'missing phase' }),
      );

      expect(result.status).toBe(3);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'INVALID_REQUEST_SCHEMA',
        }),
      );
      expect(Array.isArray(payload.details?.errors)).toBe(true);
    });
  });

  it('returns exit 1 with machine-readable error for adapter exceptions', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              throw new Error('boom');
            }
          };
        }
      `);

      const result = runAdapter(
        tempRoot,
        JSON.stringify({ description: 'run', subagent_type: 'intent' }),
      );

      expect(result.status).toBe(1);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'ADAPTER_ERROR',
        }),
      );
    });
  });
});
