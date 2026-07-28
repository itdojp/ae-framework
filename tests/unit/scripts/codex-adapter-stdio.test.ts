import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
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
  const tmpRoot = resolve('.codex-local/tmp');
  mkdirSync(tmpRoot, { recursive: true });
  const dir = mkdtempSync(join(tmpRoot, 'codex-stdio-'));
  try {
    run(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function writeAuthoritySnapshot(tempRoot: string, relativePath = '.codex-local/authority/current.json') {
  const fixture = JSON.parse(readFileSync(
    resolve('fixtures/github-work-state/sample.github-work-state.json'),
    'utf8',
  ));
  const target = join(tempRoot, relativePath);
  mkdirSync(resolve(target, '..'), { recursive: true });
  writeFileSync(target, `${JSON.stringify(fixture)}\n`, 'utf8');
  return { fixture, relativePath, target };
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

  it('rejects legacy free-form scalar context before delegating to adapter', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'should not run',
                analysis: 'should not run',
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
        JSON.stringify({ description: 'run ui', subagent_type: 'ui', context: 'write files anywhere' }),
      );

      expect(result.status).toBe(3);
      const payload = parseJsonLine(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'INVALID_REQUEST_SCHEMA',
        }),
      );
      expect(JSON.stringify(payload.details?.errors ?? [])).toContain('/context');
    });
  });

  it('rejects a malformed authority snapshot digest before delegating to adapter', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return { async handleTask() { throw new Error('must not run'); } };
        }
      `);
      const result = runAdapter(
        tempRoot,
        JSON.stringify({
          description: 'run intent',
          subagent_type: 'intent',
          context: { authoritySnapshotDigest: 'sha256:unknown' },
        }),
      );
      expect(result.status).toBe(3);
      expect(parseJsonLine(result.stdout).code).toBe('INVALID_REQUEST_SCHEMA');
    });
  });

  it('rejects digest-only, missing, malformed, mismatched, external, and symlink authority references', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return { async handleTask() { throw new Error('must not run'); } };
        }
      `);
      const validDigest = `sha256:${'a'.repeat(64)}`;
      const digestOnly = runAdapter(tempRoot, JSON.stringify({
        description: 'run intent', subagent_type: 'intent',
        context: { authoritySnapshotDigest: validDigest },
      }));
      expect(digestOnly.status).toBe(3);
      expect(parseJsonLine(digestOnly.stdout).code).toBe('INVALID_REQUEST_SCHEMA');

      const missing = runAdapter(tempRoot, JSON.stringify({
        description: 'run intent', subagent_type: 'intent',
        context: { authoritySnapshotPath: 'missing.json', authoritySnapshotDigest: validDigest },
      }));
      expect(parseJsonLine(missing.stdout).code).toBe('INVALID_AUTHORITY_SNAPSHOT');

      const malformedPath = '.codex-local/authority/malformed.json';
      mkdirSync(join(tempRoot, '.codex-local/authority'), { recursive: true });
      writeFileSync(join(tempRoot, malformedPath), '{invalid', 'utf8');
      const malformed = runAdapter(tempRoot, JSON.stringify({
        description: 'run intent', subagent_type: 'intent',
        context: { authoritySnapshotPath: malformedPath, authoritySnapshotDigest: validDigest },
      }));
      expect(parseJsonLine(malformed.stdout).code).toBe('INVALID_AUTHORITY_SNAPSHOT');

      const { fixture, relativePath, target } = writeAuthoritySnapshot(tempRoot);
      const mismatch = runAdapter(tempRoot, JSON.stringify({
        description: 'run intent', subagent_type: 'intent',
        context: { authoritySnapshotPath: relativePath, authoritySnapshotDigest: validDigest },
      }));
      expect(parseJsonLine(mismatch.stdout).code).toBe('INVALID_AUTHORITY_SNAPSHOT');

      const external = runAdapter(tempRoot, JSON.stringify({
        description: 'run intent', subagent_type: 'intent',
        context: { authoritySnapshotPath: target, authoritySnapshotDigest: fixture.snapshotDigest },
      }));
      expect(parseJsonLine(external.stdout).code).toBe('INVALID_AUTHORITY_SNAPSHOT');

      const linkPath = '.codex-local/authority/link.json';
      symlinkSync(target, join(tempRoot, linkPath));
      const symlink = runAdapter(tempRoot, JSON.stringify({
        description: 'run intent', subagent_type: 'intent',
        context: { authoritySnapshotPath: linkPath, authoritySnapshotDigest: fixture.snapshotDigest },
      }));
      expect(parseJsonLine(symlink.stdout).code).toBe('INVALID_AUTHORITY_SNAPSHOT');
    });
  });

  it('passes only a validated snapshot digest to the adapter authority binding', () => {
    withTempRepo((tempRoot) => {
      const { fixture, relativePath } = writeAuthoritySnapshot(tempRoot);
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter(options) {
          return {
            async handleTask(request) {
              return {
                summary: 'ok', analysis: JSON.stringify(request.context), recommendations: [],
                nextActions: ['continue'], warnings: [], shouldBlockProgress: false,
                authoritySnapshotDigest: options.validatedAuthoritySnapshotDigest
              };
            }
          };
        }
      `);
      const result = runAdapter(tempRoot, JSON.stringify({
        description: 'run intent', subagent_type: 'intent',
        context: {
          authoritySnapshotPath: relativePath,
          authoritySnapshotDigest: fixture.snapshotDigest,
        },
      }));
      expect(result.status, result.stderr).toBe(0);
      const response = parseJsonLine(result.stdout);
      expect(response.authoritySnapshotDigest).toBe(fixture.snapshotDigest);
      expect(response.analysis).not.toContain('authoritySnapshot');
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

  it('returns exit 2 when blocked response has empty warnings but actionable nextActions', () => {
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
      expect(Array.isArray(payload.warnings)).toBe(true);
      expect(payload.warnings[0]).toContain('Human action:');
    });
  });

  it('uses requiredHumanInput as the highest-priority warning fallback for blocked responses', () => {
    withTempRepo((tempRoot) => {
      writeAdapterModule(tempRoot, `
        export function createCodexTaskAdapter() {
          return {
            async handleTask() {
              return {
                summary: 'blocked',
                analysis: 'analysis',
                recommendations: [],
                nextActions: ['rerun with required approval'],
                warnings: [],
                shouldBlockProgress: true,
                requiredHumanInput: 'approval=1'
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
      expect(payload.warnings).toEqual(['Human action: provide approval=1']);
    });
  });

  it('trims blocked warnings and removes empty warning entries when warnings are present', () => {
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
                warnings: ['  Human action: add label autopilot:on  ', '', '   '],
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
      expect(payload.warnings).toEqual(['Human action: add label autopilot:on']);
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
