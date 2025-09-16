import { describe, it, expect, vi } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/resilience/backoff-strategies';

describe('CircuitBreaker: no unknown/duplicate consecutive events', () => {
  it('onStateChange emits only known states and avoids consecutive duplicates', async () => {
    vi.useFakeTimers();
    const seen: CircuitState[] = [];
    const cb = new CircuitBreaker({
      failureThreshold: 2,
      recoveryTimeout: 50,
      monitoringPeriod: 10000,
      onStateChange: (s) => { seen.push(s); }
    });
    const failing = vi.fn().mockRejectedValue(new Error('fail'));
    // Cause OPEN
    for (let i=0;i<2;i++){ try { await cb.execute(failing); } catch {} }
    // Move to HALF_OPEN and then CLOSED
    vi.advanceTimersByTime(60);
    const ok = vi.fn().mockResolvedValue('ok');
    await cb.execute(ok);

    // Known states only
    const allowed = new Set([CircuitState.CLOSED, CircuitState.OPEN, CircuitState.HALF_OPEN]);
    for (const s of seen) expect(allowed.has(s)).toBe(true);
    // No consecutive duplicates
    for (let i=1;i<seen.length;i++) expect(seen[i]).not.toBe(seen[i-1]);
    vi.useRealTimers();
  });
});

