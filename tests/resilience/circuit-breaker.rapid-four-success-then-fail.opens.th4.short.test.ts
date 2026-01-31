import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid four successes then fail -> OPEN (th=4, short)', () => {
  it(
    formatGWT('rapid transitions', 'four successes then fail at threshold(4)', 'closes then reopens to OPEN on failure'),
    async () => {
      const timeout = 20;
      const th = 4;
      const cb = new CircuitBreaker('rapid-4s-then-f-th4', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      // Four successes to close
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
      // Failure after closed should open again (given failureThreshold=1)
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});
