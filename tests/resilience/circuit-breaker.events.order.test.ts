import { describe, it, expect, vi } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/resilience/backoff-strategies';

describe('CircuitBreaker: state change order', () => {
  it('emits OPEN -> HALF_OPEN -> CLOSED in order', async () => {
    vi.useFakeTimers();
    const changes: Array<{state: CircuitState}> = [];
    const cb = new CircuitBreaker({
      failureThreshold: 2,
      recoveryTimeout: 100,
      monitoringPeriod: 10000,
      onStateChange: (s) => { changes.push({ state: s }); }
    });
    // cause OPEN
    const failing = vi.fn().mockRejectedValue(new Error('fail'));
    for (let i=0;i<2;i++) { try { await cb.execute(failing); } catch {} }
    expect(cb.getStats().state).toBe(CircuitState.OPEN);
    // advance to HALF_OPEN window
    vi.advanceTimersByTime(120);
    const ok = vi.fn().mockResolvedValue('ok');
    await cb.execute(ok);
    expect(cb.getStats().state).toBe(CircuitState.CLOSED);
    // verify order contains OPEN then CLOSED (HALF_OPEN is transient but callback should include)
    const seq = changes.map(c => c.state);
    const idxOpen = seq.indexOf(CircuitState.OPEN);
    const idxHalf = seq.indexOf(CircuitState.HALF_OPEN);
    const idxClosed = seq.lastIndexOf(CircuitState.CLOSED);
    expect(idxOpen).toBeGreaterThanOrEqual(0);
    expect(idxHalf).toBeGreaterThan(idxOpen);
    expect(idxClosed).toBeGreaterThan(idxHalf);
    vi.useRealTimers();
  });
});

