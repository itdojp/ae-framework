import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker CLOSED stays CLOSED on successes', () => {
  it(
    formatGWT('CLOSED state', 'several successful executions', 'state remains CLOSED'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('closed-stays-closed', {
        failureThreshold: 1,
        successThreshold: 2,
        timeout,
        monitoringWindow: 100,
      });

      for (let k = 0; k < 3; k++) {
        await expect(cb.execute(async () => k)).resolves.toBe(k);
        expect(cb.getState()).toBe(CircuitState.CLOSED);
      }
    }
  );
});

