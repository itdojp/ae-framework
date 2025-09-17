import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker recovers then opens again on new failure', () => {
  it(
    formatGWT('fail to OPEN', 'recover to CLOSED with two successes', 'next failure opens again'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('recover-then-open', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });
      // Fail -> OPEN
      await expect(cb.execute(async () => { throw new Error('f1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // HALF_OPEN then two successes -> CLOSED
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
      // New failure -> OPEN again
      await expect(cb.execute(async () => { throw new Error('f2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

