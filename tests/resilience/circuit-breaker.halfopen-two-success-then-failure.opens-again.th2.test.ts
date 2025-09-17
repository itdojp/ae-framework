import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker two successes then failure -> OPEN (th=2)', () => {
  it(
    formatGWT('OPEN after initial fail', 'two successes then failure in HALF_OPEN (th=2)', 'returns to OPEN (since closed then failure)'),
    async () => {
      const timeout = 22;
      const cb = new CircuitBreaker('halfopen-2succ-then-fail-th2', { failureThreshold: 1, successThreshold: 2, timeout, monitoringWindow: 60 });
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

