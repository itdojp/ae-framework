import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN closes after 3 successes (th=3, alt)', () => {
  it(
    formatGWT('HALF_OPEN', 'three consecutive successes (th=3)', 'transitions to CLOSED'),
    async () => {
      const timeout = 24;
      const cb = new CircuitBreaker('halfopen-close-after-3-alt', {
        failureThreshold: 1,
        successThreshold: 3,
        timeout,
        monitoringWindow: 100,
      });

      // Trip to OPEN first
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // Transition to HALF_OPEN then 3 successes -> CLOSED
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      await expect(cb.execute(async () => 3)).resolves.toBe(3);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
    }
  );
});

