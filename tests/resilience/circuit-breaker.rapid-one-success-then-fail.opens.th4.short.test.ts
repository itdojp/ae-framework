import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid one success then fail -> OPEN (th=4, short)', () => {
  it(
    formatGWT('rapid transitions', 'one success then fail before threshold(4)', 'returns to OPEN'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('rapid-1s-then-f-th4', { failureThreshold: 1, successThreshold: 4, timeout, monitoringWindow: 100 });
      await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise((r) => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

