import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker rapid HALF_OPEN→OPEN sequence (short)', () => {
  it(
    formatGWT('rapid transitions', 'OPEN→HALF_OPEN→OPEN with quick failure', 'never CLOSED until threshold met'),
    async () => {
      const timeout = 20;
      const cb = new CircuitBreaker('rapid', { failureThreshold: 1, successThreshold: 3, timeout, monitoringWindow: 80 });
      // Open
      await expect(cb.execute(async () => { throw new Error('x'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // Half-open window
      await new Promise((r) => setTimeout(r, timeout + 2));
      expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
      // quick failure → back to OPEN
      await expect(cb.execute(async () => { throw new Error('y'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
  );
});

