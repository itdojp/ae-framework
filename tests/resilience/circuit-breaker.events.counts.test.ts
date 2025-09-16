import { describe, it, expect, vi } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/resilience/backoff-strategies';

describe('CircuitBreaker: state change counts', () => {
  it('produces expected number of state changes for OPEN→HALF_OPEN→CLOSED', async () => {
    vi.useFakeTimers();
    const changes: CircuitState[] = [];
    const cb = new CircuitBreaker({ failureThreshold: 2, recoveryTimeout: 100, monitoringPeriod: 10000, onStateChange: s => changes.push(s) });
    const fail = vi.fn().mockRejectedValue(new Error('fail'));
    for (let i=0;i<2;i++) { try { await cb.execute(fail); } catch {} }
    vi.advanceTimersByTime(120);
    const ok = vi.fn().mockResolvedValue('ok');
    await cb.execute(ok);
    const seq = changes.map(c=>c);
    expect(seq.length).toBeGreaterThanOrEqual(2);
    expect(seq).toContain(CircuitState.OPEN);
    expect(seq).toContain(CircuitState.CLOSED);
    for (let i=1;i<seq.length;i++) expect(seq[i]).not.toBe(seq[i-1]);
    vi.useRealTimers();
  });
});

