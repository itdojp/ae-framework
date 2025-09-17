import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN successThreshold=5 close then open again', () => {
  it(
    formatGWT(
      'OPEN after failure',
      'five successes in HALF_OPEN -> CLOSED',
      'subsequent failure opens again'
    ),
    async () => {
      const timeout = 30;
      const cb = new CircuitBreaker('half-open-5-close-open', {
        failureThreshold: 1,
        successThreshold: 5,
        timeout,
        monitoringWindow: 100,
      });

      // 1) Fail once → OPEN
      await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // 2) Wait until HALF_OPEN
      await new Promise((r) => setTimeout(r, timeout + 5));
      expect([CircuitState.HALF_OPEN, CircuitState.OPEN]).toContain(cb.getState());

      // 3) Five successes in HALF_OPEN should close the circuit
      for (let i = 0; i < 5; i++) {
        await expect(cb.execute(async () => 1)).resolves.toBe(1);
      }
      expect(cb.getState()).toBe(CircuitState.CLOSED);

      // 4) Next failure should immediately OPEN again
      await expect(cb.execute(async () => { throw new Error('fail-again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});
