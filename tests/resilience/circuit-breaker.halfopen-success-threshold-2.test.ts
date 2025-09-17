import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker HALF_OPEN successThreshold=2', () => {
  it(formatGWT('OPEN after failure', 'two successes in HALF_OPEN', 'transition to CLOSED'), async () => {
    const timeout = 30;
    const cb = new CircuitBreaker('half-open-2', {
      failureThreshold: 1,
      successThreshold: 2,
      timeout,
      monitoringWindow: 100,
    });
    // cause OPEN
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    await new Promise(r => setTimeout(r, timeout + 5));
    // first success → remain HALF_OPEN
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    // second success → CLOSED
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});
