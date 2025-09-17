import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker three successes then failure -> OPEN (th=5)', () => {
  it(
    formatGWT('OPEN after initial fail', 'three successes then failure in HALF_OPEN (th=5)', 'returns to OPEN'),
    async () => {
      const timeout = 28;
      const cb = new CircuitBreaker('halfopen-3succ-then-fail-th5', { failureThreshold: 1, successThreshold: 5, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      for (let i = 0; i < 3; i++) {
        await expect(cb.execute(async () => 1)).resolves.toBe(1);
      }
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

