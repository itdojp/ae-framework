import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { existsSync, rmSync } from 'node:fs';
import { resolve } from 'node:path';

const scriptPath = resolve('scripts/codex/spec-stdio.mjs');

const runBridge = (
  payload: Record<string, unknown>,
  options: { env?: Record<string, string | undefined> } = {},
) => {
  return spawnSync(process.execPath, [scriptPath], {
    input: `${JSON.stringify(payload)}\n`,
    encoding: 'utf8',
    env: { ...process.env, ...options.env },
    timeout: 60_000,
  });
};

const parseLastJsonLine = (stdout: string) => {
  const line = stdout.trim().split('\n').filter(Boolean).pop() || '{}';
  return JSON.parse(line);
};

describe('spec-stdio bridge', () => {
  it('works in direct execution path for validate', () => {
    const result = runBridge({
      action: 'validate',
      args: {
        inputPath: 'spec/0_first_valid_spec.md',
        relaxed: true,
        maxWarnings: 200,
      },
    }, {
      env: {
        // A cold checkout may need the bridge to build the local spec compiler
        // package before validating. The trusted context is outside caller JSON.
        AE_CODEX_SPEC_STDIO_TRUSTED_CONTEXT: '1',
      },
    });
    expect(result.status).toBe(0);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(true);
    expect(parsed.data?.summary).toBeDefined();
  });

  it('returns non-zero on unknown action', () => {
    const result = runBridge({ action: 'unknown-action' });
    expect(result.status).toBe(2);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('Unknown action');
  });

  it('returns non-zero on missing action', () => {
    const result = runBridge({ args: {} });
    expect(result.status).toBe(2);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('Missing action');
  });

  it('returns non-zero(2) on malformed JSON input', () => {
    const result = spawnSync(process.execPath, [scriptPath], {
      input: '{"action":"validate",',
      encoding: 'utf8',
      timeout: 60_000,
    });
    expect(result.status).toBe(2);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('Invalid JSON input');
  });

  it('rejects absolute and parent-directory paths before tool sinks run', () => {
    const invalidRequests = [
      {
        action: 'validate',
        args: { inputPath: '/tmp/feature.ae-spec.md' },
        expected: 'must be relative to the approved workspace',
      },
      {
        action: 'compile',
        args: { inputPath: 'spec/0_first_valid_spec.md', outputPath: '../ae-ir.json' },
        expected: 'must not contain dot-segment path components',
      },
      {
        action: 'codegen',
        args: { irPath: 'artifacts/spec-synthesis/ae-ir.json', outDir: '/var/tmp/generated' },
        expected: 'must be relative to the approved workspace',
      },
    ];

    for (const request of invalidRequests) {
      const { expected, ...payload } = request;
      const result = runBridge(payload);
      expect(result.status).toBe(1);
      const parsed = parseLastJsonLine(result.stdout);
      expect(parsed.ok).toBe(false);
      expect(parsed.error).toContain(expected);
    }
  });

  it('requires trusted approval before compile writes under the artifact root', () => {
    const result = runBridge({
      action: 'compile',
      args: {
        inputPath: 'spec/0_first_valid_spec.md',
        outputPath: 'artifacts/spec-synthesis/spec-stdio-test/ae-ir.json',
        relaxed: true,
        validate: false,
      },
    });

    expect(result.status).toBe(1);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('AE-IR output writes requires trusted approval');
  });

  it('allows approved compile writes only under the artifact root by default', () => {
    const outputDir = resolve('artifacts/spec-synthesis/spec-stdio-test');
    const outputPath = resolve(outputDir, 'ae-ir.json');
    rmSync(outputDir, { recursive: true, force: true });

    const result = runBridge({
      action: 'compile',
      approval: {
        approved: true,
        scope: 'codex-spec-stdio',
      },
      args: {
        inputPath: 'spec/0_first_valid_spec.md',
        outputPath: 'artifacts/spec-synthesis/spec-stdio-test/ae-ir.json',
        relaxed: true,
        validate: false,
      },
    }, {
      env: {
        AE_CODEX_SPEC_STDIO_TRUSTED_APPROVAL: '1',
      },
    });

    expect(result.status).toBe(0);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(true);
    expect(parsed.data?.outputPath).toBe('artifacts/spec-synthesis/spec-stdio-test/ae-ir.json');
    expect(existsSync(outputPath)).toBe(true);

    rmSync(outputDir, { recursive: true, force: true });
  });

  it('rejects approved compile writes outside the artifact root unless workspace writes are explicitly allowed', () => {
    const result = runBridge({
      action: 'compile',
      approval: {
        approved: true,
        scope: 'codex-spec-stdio',
      },
      args: {
        inputPath: 'spec/0_first_valid_spec.md',
        outputPath: '.ae/ae-ir.json',
      },
    }, {
      env: {
        AE_CODEX_SPEC_STDIO_TRUSTED_APPROVAL: '1',
      },
    });

    expect(result.status).toBe(1);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('must stay under the approved artifact root');
  });

  it('requires trusted approval before codegen child-process execution', () => {
    const result = runBridge({
      action: 'codegen',
      args: {
        irPath: 'artifacts/spec-synthesis/ae-ir.json',
        outDir: 'artifacts/spec-synthesis/generated',
        targets: ['typescript'],
      },
    });

    expect(result.status).toBe(1);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('Code generation child process and filesystem writes requires trusted approval');
  });
});
