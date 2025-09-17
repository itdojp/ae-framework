import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker two successes then failure -> OPEN (th=4, alt)', () => {
  it(
    formatGWT('OPEN after initial fail', 'two successes then failure in HALF_OPEN (th=4)', 'returns to OPEN'),
    async () => {
      const timeout = 26;
      const cb = new CircuitBreaker('halfopen-2succ-then-fail-th4-alt', {
        failureThreshold: 1,
        successThreshold: 4,
        timeout,
        monitoringWindow: 100,
      });

      // trip to OPEN
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // move to HALF_OPEN
      await new Promise((r) => setTimeout(r, timeout + 2));

      // two successes
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);

      // then failure -> OPEN
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

