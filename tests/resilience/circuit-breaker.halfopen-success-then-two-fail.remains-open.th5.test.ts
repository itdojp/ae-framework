import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN success then two failures remains OPEN (th=5)', () => {
  it(
    formatGWT('HALF_OPEN single success', 'then two failures at threshold=5', 'returns to OPEN and not CLOSED'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('halfopen-s-ff-th5', { failureThreshold: 1, successThreshold: 5, timeout, monitoringWindow: 100 });
      // open
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      // one success
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      // two failures bring it to OPEN again
      await expect(cb.execute(async () => { throw new Error('f1'); })).rejects.toBeInstanceOf(Error);
      await expect(cb.execute(async () => { throw new Error('f2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

