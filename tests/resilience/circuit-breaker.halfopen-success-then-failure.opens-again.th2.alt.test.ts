import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker success then failure -> OPEN (th=2, alt)', () => {
  it(
    formatGWT('OPEN after first fail', 'one success then failure in HALF_OPEN (th=2)', 'returns to OPEN'),
    async () => {
      const timeout = 25;
      const cb = new CircuitBreaker('halfopen-1succ-then-fail-th2-alt', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });

      // trip to OPEN
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // move to HALF_OPEN
      await new Promise((r) => setTimeout(r, timeout + 2));

      // first success
      await expect(cb.execute(async () => 1)).resolves.toBe(1);

      // then failure should re-open
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

