import { describe, expect, it } from 'vitest';
import {
  readIntEnv,
  resolveRoundWaitMs,
  waitForNextRound,
} from '../../../scripts/ci/lib/round-control.mjs';

describe('round-control helpers', () => {
  it('reads integer env with fallback and min guard', () => {
    const original = process.env.AE_ROUND_TEST_VALUE;
    process.env.AE_ROUND_TEST_VALUE = '12';
    expect(readIntEnv('AE_ROUND_TEST_VALUE', 3, 0)).toBe(12);

    process.env.AE_ROUND_TEST_VALUE = 'x';
    expect(readIntEnv('AE_ROUND_TEST_VALUE', 3, 0)).toBe(3);

    process.env.AE_ROUND_TEST_VALUE = '-1';
    expect(readIntEnv('AE_ROUND_TEST_VALUE', 3, 0)).toBe(3);

    if (original === undefined) {
      delete process.env.AE_ROUND_TEST_VALUE;
    } else {
      process.env.AE_ROUND_TEST_VALUE = original;
    }
  });

  it('computes fixed and exponential wait durations', () => {
    expect(resolveRoundWaitMs({
      round: 1,
      baseSeconds: 8,
      strategy: 'fixed',
      maxSeconds: 120,
    })).toBe(8000);

    expect(resolveRoundWaitMs({
      round: 3,
      baseSeconds: 8,
      strategy: 'exponential',
      maxSeconds: 120,
    })).toBe(32000);

    expect(resolveRoundWaitMs({
      round: 5,
      baseSeconds: 10,
      strategy: 'exponential',
      maxSeconds: 40,
    })).toBe(40000);
  });

  it('handles wait resolution edge cases', () => {
    expect(resolveRoundWaitMs({
      round: 2,
      baseSeconds: 0,
      strategy: 'fixed',
      maxSeconds: 10,
    })).toBe(0);

    expect(resolveRoundWaitMs({
      round: 2,
      baseSeconds: 7,
      strategy: 'unknown',
      maxSeconds: 10,
    })).toBe(7000);

    expect(resolveRoundWaitMs({
      round: 1,
      baseSeconds: 9,
      strategy: 'exponential',
      maxSeconds: 60,
    })).toBe(9000);
  });

  it('skips sleep on the last round', async () => {
    const calls: number[] = [];
    const sleeper = async (ms: number) => {
      calls.push(ms);
    };

    const waited = await waitForNextRound({
      round: 1,
      maxRounds: 3,
      baseSeconds: 5,
      strategy: 'fixed',
      sleeper,
    });
    expect(waited).toBe(5000);
    expect(calls).toEqual([5000]);

    const waitedLast = await waitForNextRound({
      round: 3,
      maxRounds: 3,
      baseSeconds: 5,
      strategy: 'fixed',
      sleeper,
    });
    expect(waitedLast).toBe(0);
    expect(calls).toEqual([5000]);
  });

  it('supports exponential wait strategy in waitForNextRound', async () => {
    const calls: number[] = [];
    const sleeper = async (ms: number) => {
      calls.push(ms);
    };

    const waited = await waitForNextRound({
      round: 2,
      maxRounds: 4,
      baseSeconds: 6,
      strategy: 'exponential',
      maxSeconds: 18,
      sleeper,
    });
    expect(waited).toBe(12000);
    expect(calls).toEqual([12000]);
  });
});
