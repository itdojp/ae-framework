import { existsSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { runDoctorEnv } from '../../../scripts/doctor/doctor-env.mjs';

type SpawnResult = {
  status?: number;
  stdout?: string;
  stderr?: string;
  error?: Error;
};

function withTempRepo(testFn: (rootDir: string) => void): void {
  const rootDir = mkdtempSync(path.join(tmpdir(), 'ae-doctor-env-'));
  try {
    testFn(rootDir);
  } finally {
    rmSync(rootDir, { recursive: true, force: true });
  }
}

function writePackageJson(rootDir: string): void {
  writeFileSync(path.join(rootDir, 'package.json'), JSON.stringify({
    name: 'doctor-env-fixture',
    private: true,
    packageManager: 'pnpm@10.0.0',
    engines: {
      node: '>=20.11 <23',
    },
    scripts: {},
  }, null, 2));
}

function createSpawnStub(results: Record<string, SpawnResult>) {
  return (command: string) => {
    const entry = results[command];
    if (!entry) {
      return { status: 1, stdout: '', stderr: '', error: new Error(`command not found: ${command}`) };
    }
    return {
      status: entry.status ?? 0,
      stdout: entry.stdout ?? '',
      stderr: entry.stderr ?? '',
      error: entry.error,
    };
  };
}

function captureStdout(fn: () => void): string {
  const originalWrite = process.stdout.write;
  let output = '';
  process.stdout.write = ((chunk: unknown, encoding?: unknown, callback?: unknown) => {
    if (typeof chunk === 'string') {
      output += chunk;
    } else if (chunk) {
      output += Buffer.from(chunk as Uint8Array).toString(typeof encoding === 'string' ? encoding : undefined);
    }
    if (typeof callback === 'function') {
      callback();
    }
    return true;
  }) as typeof process.stdout.write;
  try {
    fn();
  } finally {
    process.stdout.write = originalWrite;
  }
  return output;
}

describe('doctor-env script', () => {
  it('returns exit 1 when required pnpm command is missing', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir);
      const spawn = createSpawnStub({
        corepack: { status: 0, stdout: '0.31.0\n' },
      });

      const output = captureStdout(() => {
        const outcome = runDoctorEnv([
          'node',
          'doctor-env.mjs',
          '--root',
          rootDir,
          '--format',
          'json',
        ], {
          spawn,
          processVersion: 'v20.12.0',
          platform: 'linux',
          arch: 'x64',
          nowIso: () => '2026-02-17T00:00:00.000Z',
        });
        expect(outcome.exitCode).toBe(1);
        expect(outcome.result?.summary.status).toBe('error');
      });

      const parsed = JSON.parse(output);
      expect(parsed.summary.exitCode).toBe(1);
      expect(parsed.checks).toEqual(expect.arrayContaining([
        expect.objectContaining({ id: 'pnpm.command', status: 'error' }),
      ]));
    });
  });

  it('returns exit 2 when warnings exist but required checks pass', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir);
      const spawn = createSpawnStub({
        pnpm: { status: 0, stdout: '10.0.0\n' },
        corepack: { status: 1, stdout: '', stderr: 'not found' },
      });

      const outcome = runDoctorEnv([
        'node',
        'doctor-env.mjs',
        '--root',
        rootDir,
      ], {
        spawn,
        processVersion: 'v20.12.0',
        platform: 'linux',
        arch: 'x64',
        nowIso: () => '2026-02-17T00:00:00.000Z',
      });

      expect(outcome.exitCode).toBe(2);
      expect(outcome.result?.summary.status).toBe('warn');
      expect(outcome.result?.summary.counts.error).toBe(0);
      expect(outcome.result?.summary.counts.warn).toBeGreaterThan(0);
    });
  });

  it('returns exit 0 and writes artifacts when all checks pass', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir);
      mkdirSync(path.join(rootDir, 'dist', 'src', 'cli'), { recursive: true });
      writeFileSync(path.join(rootDir, 'dist', 'src', 'cli', 'index.js'), 'console.log("ok");');
      const spawn = createSpawnStub({
        pnpm: { status: 0, stdout: '10.1.2\n' },
        corepack: { status: 0, stdout: '0.31.0\n' },
      });

      const outcome = runDoctorEnv([
        'node',
        'doctor-env.mjs',
        '--root',
        rootDir,
      ], {
        spawn,
        processVersion: 'v22.1.0',
        platform: 'linux',
        arch: 'x64',
        nowIso: () => '2026-02-17T00:00:00.000Z',
      });

      expect(outcome.exitCode).toBe(0);
      expect(outcome.result?.summary.status).toBe('ok');

      const outputPath = path.join(rootDir, 'artifacts', 'doctor', 'env.json');
      expect(existsSync(outputPath)).toBe(true);
      const saved = JSON.parse(readFileSync(outputPath, 'utf8'));
      expect(saved.summary.exitCode).toBe(0);
      expect(saved.checks).toEqual(expect.arrayContaining([
        expect.objectContaining({ id: 'dist.cli', status: 'ok' }),
      ]));
    });
  });

  it('does not downgrade exit code on windows-only platform hint', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir);
      mkdirSync(path.join(rootDir, 'dist', 'src', 'cli'), { recursive: true });
      writeFileSync(path.join(rootDir, 'dist', 'src', 'cli', 'index.js'), 'console.log("ok");');
      const spawn = createSpawnStub({
        pnpm: { status: 0, stdout: '10.0.0\n' },
        corepack: { status: 0, stdout: '0.31.0\n' },
      });

      const outcome = runDoctorEnv([
        'node',
        'doctor-env.mjs',
        '--root',
        rootDir,
      ], {
        spawn,
        processVersion: 'v20.12.0',
        platform: 'win32',
        arch: 'x64',
      });

      expect(outcome.exitCode).toBe(0);
      expect(outcome.result?.summary.status).toBe('ok');
      expect(outcome.result?.checks).toEqual(expect.arrayContaining([
        expect.objectContaining({ id: 'os.platform', status: 'ok' }),
      ]));
    });
  });
});
