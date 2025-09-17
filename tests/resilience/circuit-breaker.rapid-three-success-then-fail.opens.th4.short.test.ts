import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid three successes then fail -> OPEN (th=4, short)', () => {
  it(
    formatGWT('rapid transitions', 'three successes then fail before threshold(4)', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const th = 4;
      const cb = new CircuitBreaker('rapid-3s-then-f-th4', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      for (let i = 0; i < 3; i++) {
        await expect(cb.execute(async () => 1)).resolves.toBe(1);
      }
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

