import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker sequence with successThreshold=5 (quick)', () => {
  it(
    formatGWT('OPEN after fail', '5 successes in HALF_OPEN', 'CLOSED then fail -> OPEN'),
    async () => {
      const timeout = 30;
      const cb = new CircuitBreaker('st5-seq', { failureThreshold: 1, successThreshold: 5, timeout, monitoringWindow: 120 });
      await expect(cb.execute(async () => { throw new Error('f'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      for (let i = 0; i < 5; i++) {
        await expect(cb.execute(async () => 1)).resolves.toBe(1);
      }
      expect(cb.getState()).toBe(CircuitState.CLOSED);
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

