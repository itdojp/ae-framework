import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CLOSED after HALF_OPEN then immediate fail -> OPEN (th=3)', () => {
  it(
    formatGWT('HALF_OPEN reaches CLOSED', 'then next failure re-opens (th=3)', 'OPEN state observed'),
    async () => {
      const timeout = 24;
      const cb = new CircuitBreaker('closed-then-fail-reopen-th3', {
        failureThreshold: 1,
        successThreshold: 3,
        timeout,
        monitoringWindow: 100,
      });

      // Trip to OPEN
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // Move to HALF_OPEN and reach CLOSED
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      await expect(cb.execute(async () => 3)).resolves.toBe(3);
      expect(cb.getState()).toBe(CircuitState.CLOSED);

      // Immediate failure should re-open
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

