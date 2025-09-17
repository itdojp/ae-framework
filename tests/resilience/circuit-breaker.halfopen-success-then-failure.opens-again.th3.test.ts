import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN success then failure opens again (th=3)', () => {
  it(
    formatGWT('OPEN after fail', 'one success then failure in HALF_OPEN (th=3)', 'returns to OPEN'),
    async () => {
      const timeout = 22;
      const cb = new CircuitBreaker('halfopen-mix-th3', { failureThreshold: 1, successThreshold: 3, timeout, monitoringWindow: 60 });
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      // failure while still below threshold should re-open
      await expect(cb.execute(async () => { throw new Error('fail-again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

