import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker OPEN rejects until timeout (short)', () => {
  it(
    formatGWT('OPEN state', 'multiple execute attempts before timeout', 'all reject and state remains OPEN'),
    async () => {
      const timeout = 24;
      const cb = new CircuitBreaker('open-rejects-until-timeout', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });

      // trip to OPEN
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // attempts before timeout should reject and remain OPEN
      for (let k = 0; k < 3; k++) {
        await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(Error);
        expect(cb.getState()).toBe(CircuitState.OPEN);
      }

      // after timeout → HALF_OPEN
      await new Promise((r) => setTimeout(r, timeout + 2));
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    }
  );
});

