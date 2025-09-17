import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid three successes then fail -> OPEN (short)', () => {
  it(
    formatGWT('rapid transitions', 'three successes then fail before threshold(4)', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const th = 4;
      const cb = new CircuitBreaker('rapid-3s-then-f', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 80 });
      // open
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // half-open
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      // fail before threshold -> OPEN again
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

