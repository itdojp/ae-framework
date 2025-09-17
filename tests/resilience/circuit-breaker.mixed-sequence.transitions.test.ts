import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker mixed sequence transitions', () => {
  it(
    formatGWT('CLOSED → OPEN (fail)', 'HALF_OPEN → CLOSED (success×threshold)', 'CLOSED → OPEN (fail) again'),
    async () => {
      const timeout = 25;
      const cb = new CircuitBreaker('mixed-seq', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });

      // CLOSED -> OPEN by failure
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // After timeout: HALF_OPEN trial, two successes -> CLOSED
      await new Promise(r => setTimeout(r, timeout + 5));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);

      // Fail again -> OPEN, and reject until timeout
      await expect(cb.execute(async () => { throw new Error('fail-again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
    }
  );
});

