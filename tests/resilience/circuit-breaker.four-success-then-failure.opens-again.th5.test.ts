import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker 4 successes then failure -> OPEN (th=5)', () => {
  it(
    formatGWT('OPEN after initial fail', 'four successes then failure in HALF_OPEN (th=5)', 'returns to OPEN'),
    async () => {
      const timeout = 26;
      const cb = new CircuitBreaker('halfopen-4succ-then-fail-th5', { failureThreshold: 1, successThreshold: 5, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('first'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      for (let i = 0; i < 4; i++) {
        await expect(cb.execute(async () => 1)).resolves.toBe(1);
      }
      await expect(cb.execute(async () => { throw new Error('fail-again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

