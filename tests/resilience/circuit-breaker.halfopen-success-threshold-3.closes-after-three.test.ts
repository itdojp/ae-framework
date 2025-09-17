import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN successThreshold=3 closes after three successes', () => {
  it(formatGWT('OPEN after failure', 'three successes in HALF_OPEN', 'transition to CLOSED'), async () => {
    const timeout = 30;
    const cb = new CircuitBreaker('half-open-3-close', {
      failureThreshold: 1,
      successThreshold: 3,
      timeout,
      monitoringWindow: 100,
    });
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    await new Promise(r => setTimeout(r, timeout + 5));
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});

