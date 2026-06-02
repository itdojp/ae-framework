import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mkdir, readdir, readFile, rm, stat } from 'node:fs/promises';
import path from 'node:path';
import { withRecorder } from '../../src/providers/recorder.js';
import type { LLM } from '../../src/providers/index.js';

const tmpRoot = path.join(process.cwd(), '.codex-local', 'tmp', 'recorder-tests');

async function makeCassetteDir(name: string): Promise<string> {
  await mkdir(tmpRoot, { recursive: true });
  return path.join(tmpRoot, `${name}-${Date.now()}-${Math.random().toString(16).slice(2)}`);
}

async function readOnlyCassette(dir: string): Promise<{ file: string; text: string }> {
  const files = await readdir(dir);
  expect(files).toHaveLength(1);
  const file = path.join(dir, files[0]!);
  return {
    file,
    text: await readFile(file, 'utf8'),
  };
}

describe('LLM recorder', () => {
  let warnSpy: ReturnType<typeof vi.spyOn>;

  beforeEach(() => {
    warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});
  });

  afterEach(async () => {
    warnSpy.mockRestore();
    await rm(tmpRoot, { recursive: true, force: true });
  });

  it('does not write cassettes unless record mode is explicitly enabled', async () => {
    const dir = await makeCassetteDir('default-off');
    const base: LLM = {
      name: 'base',
      complete: vi.fn().mockResolvedValue('live output'),
    };

    const recorder = withRecorder(base, { dir });
    const output = await recorder.complete({ prompt: 'token=raw-prompt-token' });

    expect(output).toBe('live output');
    await expect(readdir(dir)).rejects.toMatchObject({ code: 'ENOENT' });
    expect(warnSpy).not.toHaveBeenCalledWith(expect.stringContaining('RECORD mode'));
  });

  it('persists redacted cassettes with restrictive file permissions in explicit record mode', async () => {
    const dir = await makeCassetteDir('record-redacted');
    const base: LLM = {
      name: 'base',
      complete: vi.fn().mockResolvedValue('provider output Bearer raw-output-token token=raw-output-query'),
    };

    const recorder = withRecorder(base, { dir, record: true });
    const output = await recorder.complete({
      system: 'Cookie: sid=raw-system-cookie',
      prompt: 'use password=raw-prompt-password and api_key=raw-prompt-api-key',
      temperature: 0,
    });

    expect(output).toContain('raw-output-token');
    expect(warnSpy).toHaveBeenCalledWith(expect.stringContaining('RECORD mode persists redacted LLM cassettes'));

    const { file, text } = await readOnlyCassette(dir);
    const cassette = JSON.parse(text) as {
      redacted: boolean;
      inputHash: string;
      input: { promptHash: string; systemHash: string; temperature: number };
      output: string;
    };

    expect(cassette.redacted).toBe(true);
    expect(cassette.inputHash).toMatch(/^[a-f0-9]{16}$/);
    expect(cassette.input.promptHash).toMatch(/^[a-f0-9]{16}$/);
    expect(cassette.input.systemHash).toMatch(/^[a-f0-9]{16}$/);
    expect(cassette.input.temperature).toBe(0);
    expect(text).toContain('[REDACTED]');
    expect(text).not.toContain('raw-system-cookie');
    expect(text).not.toContain('raw-prompt-password');
    expect(text).not.toContain('raw-prompt-api-key');
    expect(text).not.toContain('raw-output-token');
    expect(text).not.toContain('raw-output-query');

    if (process.platform !== 'win32') {
      expect((await stat(dir)).mode & 0o777).toBe(0o700);
      expect((await stat(file)).mode & 0o777).toBe(0o600);
    }
  });

  it('redacts echo fallback output before cassette persistence', async () => {
    const dir = await makeCassetteDir('fallback-redacted');
    const base: LLM = {
      name: 'base',
      complete: vi.fn().mockRejectedValue(new Error('provider failed with token=raw-provider-error-token')),
    };

    const recorder = withRecorder(base, { dir, record: true });
    const output = await recorder.complete({
      system: 'system token=raw-system-token',
      prompt: 'prompt token=raw-fallback-token',
    });

    expect(output).toContain('raw-fallback-token');
    const { text } = await readOnlyCassette(dir);
    const serializedWarnings = JSON.stringify(warnSpy.mock.calls);

    expect(text).toContain('[REDACTED]');
    expect(text).not.toContain('raw-system-token');
    expect(text).not.toContain('raw-fallback-token');
    expect(text).not.toContain('raw-provider-error-token');
    expect(serializedWarnings).not.toContain('raw-provider-error-token');
  });

  it('replays a recorded cassette output without calling the base provider', async () => {
    const dir = await makeCassetteDir('replay');
    const input = { prompt: 'prompt token=raw-replay-token' };
    const recordBase: LLM = {
      name: 'record-base',
      complete: vi.fn().mockResolvedValue('recorded output token=raw-replay-output-token'),
    };
    const replayBase: LLM = {
      name: 'replay-base',
      complete: vi.fn().mockResolvedValue('should not be called'),
    };

    await withRecorder(recordBase, { dir, record: true }).complete(input);
    const replayed = await withRecorder(replayBase, { dir, replay: true }).complete(input);

    expect(replayed).toContain('[REDACTED]');
    expect(replayed).not.toContain('raw-replay-output-token');
    expect(replayBase.complete).not.toHaveBeenCalled();
  });
});
