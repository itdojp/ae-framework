import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid four successes then fail -> OPEN (short)', () => {
  it(
    formatGWT('rapid transitions', 'four successes then fail before threshold(5)', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const th = 5;
      const cb = new CircuitBreaker('rapid-4s-then-f', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      for (let i = 0; i < 4; i++) {
        await expect(cb.execute(async () => 1)).resolves.toBe(1);
      }
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

