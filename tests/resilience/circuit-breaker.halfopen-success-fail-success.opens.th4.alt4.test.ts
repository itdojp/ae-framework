import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: HALF_OPEN success→fail→success -> stays not CLOSED (th=4, alt4)', () => {
  it(
    formatGWT('HALF_OPEN with th=4', 'one success then fail then success', 'state is not CLOSED (requires 4 successes)'),
    async () => {
      const timeout = 26;
      const cb = new CircuitBreaker('halfopen-s-f-s-th4-alt4', {
        failureThreshold: 1,
        successThreshold: 4,
        timeout,
        monitoringWindow: 100,
      });

      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      expect(cb.getState()).not.toBe(CircuitState.CLOSED);
    }
  );
});

