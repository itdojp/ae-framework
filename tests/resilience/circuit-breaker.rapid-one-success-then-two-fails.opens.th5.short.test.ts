import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid one success then two fails -> OPEN (th=5, short)', () => {
  it(
    formatGWT('rapid transitions', 'one success then two fails before threshold(5)', 'remains OPEN'),
    async () => {
      const timeout = 20;
      const th = 5;
      const cb = new CircuitBreaker('rapid-1s-then-2f-th5', { failureThreshold: 1, successThreshold: th, timeout, monitoringWindow: 100 });
      // initial failure opens circuit
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // half-open after timeout, a single success not enough to close
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      // failure returns it to OPEN
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // immediate next failure keeps it OPEN
      await expect(cb.execute(async () => { throw new Error('again2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

