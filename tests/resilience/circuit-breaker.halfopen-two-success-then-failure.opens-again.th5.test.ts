import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN two success then failure -> OPEN (th=5)', () => {
  it(
    formatGWT('HALF_OPEN partial successes', 'two successes then failure at threshold=5', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('halfopen-2succ-then-fail-th5', { failureThreshold: 1, successThreshold: 5, timeout, monitoringWindow: 100 });
      // open first
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      // partial successes
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      // then failure should re-open (since threshold not met)
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

