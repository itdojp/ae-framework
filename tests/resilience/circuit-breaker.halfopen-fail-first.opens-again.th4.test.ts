import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker fail first in HALF_OPEN -> OPEN (th=4)', () => {
  it(
    formatGWT('OPEN after initial fail', 'fail immediately in HALF_OPEN (th=4)', 'returns to OPEN'),
    async () => {
      const timeout = 26;
      const cb = new CircuitBreaker('halfopen-fail-first-th4', {
        failureThreshold: 1,
        successThreshold: 4,
        timeout,
        monitoringWindow: 100,
      });

      // trip to OPEN
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // move to HALF_OPEN then fail again => should re-open
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

