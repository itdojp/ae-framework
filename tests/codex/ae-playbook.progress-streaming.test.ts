import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { formatDuration, formatHeartbeatLine, teeTo } from '../../scripts/codex/ae-playbook.mjs';

const tempDirs: string[] = [];

const wait = async (ms: number): Promise<void> =>
  new Promise((resolve) => setTimeout(resolve, ms));

afterEach(() => {
  while (tempDirs.length > 0) {
    const dir = tempDirs.pop();
    if (dir) rmSync(dir, { recursive: true, force: true });
  }
});

describe('ae-playbook progress streaming', () => {
  it('streams stdout/stderr while persisting merged log to file', async () => {
    const work = mkdtempSync(path.join(tmpdir(), 'ae-playbook-progress-'));
    tempDirs.push(work);
    const logFile = path.join(work, 'qa.log');
    const stdoutChunks: string[] = [];
    const stderrChunks: string[] = [];

    const result = await teeTo(
      logFile,
      async ({ onStdout, onStderr }) => {
        onStdout('stdout-line\n');
        await wait(5);
        onStderr('stderr-line\n');
        return { code: 0, stdout: '', stderr: '' };
      },
      {
        phaseName: 'qa',
        heartbeatMs: 0,
        stdoutWriter: (chunk) => stdoutChunks.push(chunk),
        stderrWriter: (chunk) => stderrChunks.push(chunk),
      },
    );

    const log = readFileSync(logFile, 'utf-8');
    expect(result.code).toBe(0);
    expect(stdoutChunks.join('')).toContain('stdout-line');
    expect(stderrChunks.join('')).toContain('stderr-line');
    expect(log).toContain('stdout-line');
    expect(log).toContain('stderr-line');
  });

  it('emits heartbeat lines during long-running phases', async () => {
    const work = mkdtempSync(path.join(tmpdir(), 'ae-playbook-heartbeat-'));
    tempDirs.push(work);
    const logFile = path.join(work, 'setup.log');
    const stdoutChunks: string[] = [];

    await teeTo(
      logFile,
      async ({ onStdout }) => {
        onStdout('begin\n');
        await wait(35);
        onStdout('end\n');
        return { code: 0, stdout: '', stderr: '' };
      },
      {
        phaseName: 'setup',
        heartbeatMs: 10,
        stdoutWriter: (chunk) => stdoutChunks.push(chunk),
      },
    );

    expect(stdoutChunks.some((chunk) => chunk.includes('[ae-playbook] [setup] heartbeat'))).toBe(true);
  });

  it('formats elapsed duration and heartbeat message', () => {
    expect(formatDuration(950)).toBe('950ms');
    expect(formatDuration(1100)).toBe('1s');
    expect(formatDuration(61_000)).toBe('1m1s');
    expect(formatHeartbeatLine('formal', 2_000)).toContain('[ae-playbook] [formal] heartbeat elapsed=2s');
  });
});
