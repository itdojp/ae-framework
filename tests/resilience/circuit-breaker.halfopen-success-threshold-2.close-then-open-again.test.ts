import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN successThreshold=2 close then open again', () => {
  it(formatGWT('OPEN after failure', 'two successes in HALF_OPEN -> CLOSED', 'next failure opens again'), async () => {
    const timeout = 30;
    const cb = new CircuitBreaker('half-open-2-close-open', {
      failureThreshold: 1,
      successThreshold: 2,
      timeout,
      monitoringWindow: 100,
    });
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    await new Promise(r => setTimeout(r, timeout + 5));
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    // Now a failure should open immediately (failureThreshold=1)
    await expect(cb.execute(async () => { throw new Error('fail-again'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
  });
});

