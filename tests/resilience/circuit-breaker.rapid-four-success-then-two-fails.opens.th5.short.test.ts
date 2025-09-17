import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid four successes then two fails -> OPEN (th=5, short)', () => {
  it(
    formatGWT('rapid transitions', 'four successes then two fails before threshold(5)', 'remains/returns to OPEN'),
    async () => {
      const timeout = 20;
      const th = 5;
      const cb = new CircuitBreaker('rapid-4s-then-2f-th5', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      // Start with a failure to OPEN, then half-open successes
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      // Two rapid failures should re-open and stay OPEN
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // Even another immediate failure keeps it OPEN
      await expect(cb.execute(async () => { throw new Error('again2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

