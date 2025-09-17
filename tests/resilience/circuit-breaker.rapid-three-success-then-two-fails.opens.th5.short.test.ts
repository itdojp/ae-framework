import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid three successes then two fails -> OPEN (th=5, short)', () => {
  it(
    formatGWT('rapid transitions', 'three successes then two fails before threshold(5)', 'remains/returns to OPEN'),
    async () => {
      const timeout = 20;
      const th = 5;
      const cb = new CircuitBreaker('rapid-3s-then-2f-th5', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      // initial failure to OPEN
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      // three successes in HALF_OPEN
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      // then two failures keep it OPEN
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await expect(cb.execute(async () => { throw new Error('again2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

