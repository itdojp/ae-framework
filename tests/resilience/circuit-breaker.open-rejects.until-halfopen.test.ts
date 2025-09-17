import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker OPEN rejects until half-open window', () => {
  it(formatGWT('OPEN state', 'rejects until timeout elapses', 'then HALF_OPEN allows a success to close'), async () => {
    const cb = new CircuitBreaker('open-rejects', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout: 50,
      monitoringWindow: 100,
    });
    await expect(cb.execute(async () => { throw new Error('f'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // Should reject while still OPEN
    await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
    // Wait to enter HALF_OPEN
    await new Promise(r => setTimeout(r, 55));
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});
