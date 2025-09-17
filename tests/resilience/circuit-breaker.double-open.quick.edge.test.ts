import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker double OPEN quick edge', () => {
  it(
    formatGWT('CLOSED to OPEN by fail', 'HALF_OPEN immediate fail again', 'remains OPEN and rejects until timeout'),
    async () => {
      const timeout = 18;
      const cb = new CircuitBreaker('double-open', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });
      await expect(cb.execute(async () => { throw new Error('fail-1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => { throw new Error('fail-2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
    }
  );
});

