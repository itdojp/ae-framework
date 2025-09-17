import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: HALF_OPEN two fails then success keeps OPEN (th=3, alt3)', () => {
  it(
    formatGWT('HALF_OPEN with th=3', 'two fails then success', 'remains or returns to OPEN'),
    async () => {
      const timeout = 24;
      const cb = new CircuitBreaker('halfopen-2fail-then-success-th3-alt3', {
        failureThreshold: 1,
        successThreshold: 3,
        timeout,
        monitoringWindow: 100,
      });

      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => { throw new Error('e3'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // next try success still should require more successes before CLOSED; state stays not CLOSED
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).not.toBe(CircuitState.CLOSED);
    }
  );
});

