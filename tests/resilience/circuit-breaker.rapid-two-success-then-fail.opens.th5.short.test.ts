import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid two successes then fail -> OPEN (th=5, short)', () => {
  it(
    formatGWT('rapid transitions', 'two successes then fail before threshold(5)', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const th = 5;
      const cb = new CircuitBreaker('rapid-2s-then-f-th5', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

