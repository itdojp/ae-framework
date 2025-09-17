import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker three successes then failure -> OPEN (th=4)', () => {
  it(
    formatGWT('OPEN after initial fail', 'three successes then failure in HALF_OPEN (th=4)', 'returns to OPEN'),
    async () => {
      const timeout = 24;
      const cb = new CircuitBreaker('halfopen-3succ-then-fail-th4', { failureThreshold: 1, successThreshold: 4, timeout, monitoringWindow: 80 });
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

