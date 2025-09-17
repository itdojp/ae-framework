import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('CircuitBreaker: HALF_OPEN consecutive triggers boundary', () => {
  it(
    formatGWT('half-open consecutive failures', 'handleCall', 'stays OPEN until required successes'),
    async () => {
      const timeout = 25; // ms
      const cb = new CircuitBreaker('halfopen-consecutive', {
        failureThreshold: 1,
        successThreshold: 3,
        timeout,
        monitoringWindow: 80,
      });

      // Force OPEN
      await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // Wait to HALF_OPEN
      await new Promise((r) => setTimeout(r, timeout + 5));
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);

      // Consecutive triggers: failure should re-open immediately, preventing close until 3 successes
      await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // Move again to HALF_OPEN and provide partial successes then a failure → should go back to OPEN
      await new Promise((r) => setTimeout(r, timeout + 5));
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);

      await cb.execute(async () => 'ok');
      await cb.execute(async () => 'ok');
      // one more failure before reaching required successes
      await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});
