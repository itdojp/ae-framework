import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN closes after 4 successes (th=4, alt)', () => {
  it(
    formatGWT('HALF_OPEN', 'four consecutive successes (th=4)', 'transitions to CLOSED'),
    async () => {
      const timeout = 24;
      const cb = new CircuitBreaker('halfopen-close-after-4-alt', {
        failureThreshold: 1,
        successThreshold: 4,
        timeout,
        monitoringWindow: 100,
      });

      // Trip to OPEN first
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // Transition to HALF_OPEN then 4 successes
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      await expect(cb.execute(async () => 3)).resolves.toBe(3);
      await expect(cb.execute(async () => 4)).resolves.toBe(4);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
    }
  );
});

