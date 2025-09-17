import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid transitions (short unit)', () => {
  it(
    formatGWT('CLOSED→OPEN→HALF_OPEN→fail→OPEN→HALF_OPEN→success×2→CLOSED→fail→OPEN', 'short timeouts', 'states are consistent and no unknowns'),
    async () => {
      const timeout = 22;
      const cb = new CircuitBreaker('rapid-transitions-short', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });

      // trip to OPEN
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // move to HALF_OPEN, then immediate failure => OPEN again
      await new Promise((r) => setTimeout(r, timeout + 2));
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // HALF_OPEN again → two successes → CLOSED
      await new Promise((r) => setTimeout(r, timeout + 2));
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      expect(cb.getState()).toBe(CircuitState.CLOSED);

      // immediate failure from CLOSED → OPEN
      await expect(cb.execute(async () => { throw new Error('e3'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

