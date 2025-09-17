import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker sequence with successThreshold=3 (quick)', () => {
  it(
    formatGWT('OPEN after fail', '3 successes in HALF_OPEN', 'CLOSED then fail -> OPEN'),
    async () => {
      const timeout = 25;
      const cb = new CircuitBreaker('st3-seq', { failureThreshold: 1, successThreshold: 3, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('f'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

