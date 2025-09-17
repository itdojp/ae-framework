import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN partial successes remain HALF_OPEN', () => {
  it(
    formatGWT('OPEN after initial failure', 'partial successes in HALF_OPEN (th=4)', 'state remains HALF_OPEN'),
    async () => {
      const timeout = 25;
      const cb = new CircuitBreaker('partial-successes', {
        failureThreshold: 1,
        successThreshold: 4,
        timeout,
        monitoringWindow: 100,
      });
      await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      // 3 successes (< threshold) should keep HALF_OPEN
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    }
  );
});

