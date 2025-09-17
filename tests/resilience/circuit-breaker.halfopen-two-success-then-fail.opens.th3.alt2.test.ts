import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: HALF_OPEN two successes then failure -> OPEN (th=3, alt2)', () => {
  it(
    formatGWT('HALF_OPEN with th=3', 'two successes then failure', 'OPEN state observed'),
    async () => {
      const timeout = 24;
      const cb = new CircuitBreaker('halfopen-2succ-then-fail-th3-alt2', {
        failureThreshold: 1,
        successThreshold: 3,
        timeout,
        monitoringWindow: 100,
      });

      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

