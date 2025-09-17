import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker close then rapid failure -> OPEN (th=2)', () => {
  it(
    formatGWT('OPEN after fail', 'two successes -> CLOSED then rapid failure', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('close-then-rapid-fail', { failureThreshold: 1, successThreshold: 2, timeout, monitoringWindow: 80 });
      await expect(cb.execute(async () => { throw new Error('f1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
      // Rapid subsequent failure in CLOSED should re-open on threshold=1
      await expect(cb.execute(async () => { throw new Error('f2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

