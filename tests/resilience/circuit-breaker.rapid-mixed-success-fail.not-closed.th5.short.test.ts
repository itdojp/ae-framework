import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid mixed success/fail not closed (th=5, short)', () => {
  it(
    formatGWT('rapid transitions', 'success → fail → success (threshold=5)', 'remains HALF_OPEN (not CLOSED)'),
    async () => {
      const timeout = 20;
      const th = 5;
      const cb = new CircuitBreaker('rapid-mixed-th5', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      // open
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      // success then fail then success → should not close at th=5
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => { throw new Error('x'); })).rejects.toBeInstanceOf(Error);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).not.toBe(CircuitState.CLOSED);
    }
  );
});

