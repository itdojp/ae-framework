import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker fail→success→fail in HALF_OPEN -> OPEN (th=3)', () => {
  it(
    formatGWT('OPEN after initial fail', 'then success once, then fail in HALF_OPEN (th=3)', 'returns to OPEN'),
    async () => {
      const timeout = 26;
      const cb = new CircuitBreaker('halfopen-fsf-th3', {
        failureThreshold: 1,
        successThreshold: 3,
        timeout,
        monitoringWindow: 100,
      });

      // trip to OPEN
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // HALF_OPEN -> success once
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);

      // then fail -> back to OPEN
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

