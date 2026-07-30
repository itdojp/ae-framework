import { EventEmitter } from 'node:events';

import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';

const spawnMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawn: spawnMock,
}));

const {
  DEFAULT_FORCE_KILL_GRACE_MS,
  DEFAULT_RUN_TIMEOUT_MS,
  EnhancedFlakeDetector,
} = await import('../../scripts/enhanced-flake-detector.mjs');

class FakeChildProcess extends EventEmitter {
  stdout = new EventEmitter();
  stderr = new EventEmitter();
  kill = vi.fn();
}

describe('EnhancedFlakeDetector run timeout', () => {
  beforeEach(() => {
    vi.useFakeTimers();
    spawnMock.mockReset();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('allows the CI-fast suite four minutes before graceful termination', async () => {
    const child = new FakeChildProcess();
    spawnMock.mockReturnValue(child);
    const detector = new EnhancedFlakeDetector({ runs: 1 });

    const resultPromise = detector.runTestSuite(1);

    expect(spawnMock).toHaveBeenCalledWith(
      'pnpm',
      ['test:fast'],
      expect.objectContaining({ timeout: DEFAULT_RUN_TIMEOUT_MS }),
    );

    child.emit('close', 0);
    await expect(resultPromise).resolves.toMatchObject({ success: true, exitCode: 0 });

    await vi.advanceTimersByTimeAsync(
      DEFAULT_RUN_TIMEOUT_MS + DEFAULT_FORCE_KILL_GRACE_MS,
    );
    expect(child.kill).not.toHaveBeenCalled();
  });

  it('retains a bounded hard stop after the graceful timeout', async () => {
    const child = new FakeChildProcess();
    spawnMock.mockReturnValue(child);
    const detector = new EnhancedFlakeDetector({
      runs: 1,
      runTimeoutMs: 100,
      forceKillGraceMs: 25,
    });

    const resultPromise = detector.runTestSuite(1);

    await vi.advanceTimersByTimeAsync(124);
    expect(child.kill).not.toHaveBeenCalled();

    await vi.advanceTimersByTimeAsync(1);
    expect(child.kill).toHaveBeenCalledOnce();
    expect(child.kill).toHaveBeenCalledWith('SIGKILL');

    child.emit('close', null);
    await expect(resultPromise).resolves.toMatchObject({ success: false, exitCode: null });
  });

  it('keeps a graceful timeout result failing and cancels the hard stop', async () => {
    const child = new FakeChildProcess();
    spawnMock.mockReturnValue(child);
    const detector = new EnhancedFlakeDetector({
      runs: 1,
      runTimeoutMs: 100,
      forceKillGraceMs: 25,
    });

    const resultPromise = detector.runTestSuite(1);
    child.emit('close', null, 'SIGTERM');

    await expect(resultPromise).resolves.toMatchObject({ success: false, exitCode: null });
    await vi.advanceTimersByTimeAsync(125);
    expect(child.kill).not.toHaveBeenCalled();
  });
});
