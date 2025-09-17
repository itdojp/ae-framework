import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker HALF_OPEN fail first -> OPEN (th=5)', () => {
  it(
    formatGWT('HALF_OPEN initial failure', 'execute failing operation at threshold=5', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('halfopen-fail-first-th5', { failureThreshold: 1, successThreshold: 5, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('first-fail'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // allow transition to HALF_OPEN again
      await new Promise(r => setTimeout(r, timeout + 2));
      // one success alone should not close
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    }
  );
});

