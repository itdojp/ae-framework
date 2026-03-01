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

function runAdapter(tempRoot: string, input: string, envOverrides: NodeJS.ProcessEnv = {}) {
  return spawnSync(process.execPath, [scriptPath], {
    cwd: tempRoot,
    input,
    encoding: 'utf8',
    env: {
      ...process.env,
      CODEX_TASK_REQUEST_SCHEMA: requestSchemaPath,
      CODEX_TASK_RESPONSE_SCHEMA: responseSchemaPath,
      ...envOverrides,
    },
  });
}

describe('codex adapter stdio contract', () => {
  it('returns exit 3 with machine-readable error when stdin is empty', () => {
    withTempRepo((tempRoot) => {
      const result = runAdapter(tempRoot, '');
      expect(result.status).toBe(3);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'EMPTY_STDIN',
        }),
      );
    });
  });

  it('returns exit 3 with machine-readable error for malformed input JSON', () => {
    withTempRepo((tempRoot) => {
      const result = runAdapter(tempRoot, '{ invalid');
      expect(result.status).toBe(3);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'INVALID_JSON',
        }),
      );
    });
  });

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

  it('normalizes missing prompt/description before delegating to adapter', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask(request) {
              return {
                summary: request.description,
                analysis: request.prompt,
                recommendations: [],
                nextActions: ['continue'],
                warnings: [],
                shouldBlockProgress: false
              };
            }
          };
        }
      `);

      const result = runAdapter(
        tempRoot,
        JSON.stringify({ description: 'single-source', subagent_type: 'intent' }),
      );

      expect(result.status).toBe(0);
      const payload = parseJsonLine(result.stdout);
      expect(payload.summary).toBe('single-source');
      expect(payload.analysis).toBe('single-source');
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
                nextActions: ['Provide missing input and rerun'],
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

  it('returns exit 1 with machine-readable error for schema load failure', () => {
    withTempRepo((tempRoot) => {
      const result = runAdapter(
        tempRoot,
        JSON.stringify({ description: 'run', subagent_type: 'intent' }),
        { CODEX_TASK_REQUEST_SCHEMA: join(tempRoot, 'missing-schema.json') },
      );

      expect(result.status).toBe(1);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'SCHEMA_LOAD_FAILED',
        }),
      );
    });
  });

  it('returns exit 1 with machine-readable error for invalid response schema', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'missing fields'
              };
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
          code: 'INVALID_RESPONSE_SCHEMA',
        }),
      );
      expect(Array.isArray(payload.details?.errors)).toBe(true);
    });
  });

  it('returns exit 1 when shouldBlockProgress=false and nextActions is empty', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'ok',
                analysis: 'analysis',
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
        JSON.stringify({ description: 'run', subagent_type: 'intent' }),
      );

      expect(result.status).toBe(1);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'INVALID_RESPONSE_SCHEMA',
        }),
      );
    });
  });

  it('returns exit 2 when blocked response omits blocked metadata but has actionable nextActions', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'blocked',
                analysis: 'analysis',
                recommendations: [],
                nextActions: ['fix and rerun'],
                warnings: [],
                shouldBlockProgress: true
              };
            }
          };
        }
      `);

      const result = runAdapter(
        tempRoot,
        JSON.stringify({ description: 'run', subagent_type: 'intent' }),
      );

      expect(result.status).toBe(2);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          shouldBlockProgress: true,
        }),
      );
    });
  });

  it('returns exit 1 when shouldBlockProgress=true and nextActions is empty', () => {
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
                warnings: [],
                shouldBlockProgress: true
              };
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
          code: 'INVALID_RESPONSE_SCHEMA',
        }),
      );
    });
  });
});
