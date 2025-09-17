import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid transitions edge', () => {
  it(
    formatGWT('OPEN quickly after fail', 'HALF_OPEN trial then immediate fail', 'OPEN persists until timeout'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('rapid-edge', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });
      // Fail -> OPEN
      await expect(cb.execute(async () => { throw new Error('f'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // Wait to allow HALF_OPEN and immediately fail
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => { throw new Error('hf'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // While still in OPEN, immediate call is rejected
      await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
    }
  );
});

