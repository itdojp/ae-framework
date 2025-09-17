import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker fail first in HALF_OPEN -> OPEN (th=3, alt)', () => {
  it(
    formatGWT('OPEN after initial fail', 'fail immediately in HALF_OPEN (th=3)', 'returns to OPEN'),
    async () => {
      const timeout = 26;
      const cb = new CircuitBreaker('halfopen-fail-first-th3-alt', {
        failureThreshold: 1,
        successThreshold: 3,
        timeout,
        monitoringWindow: 100,
      });

      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

