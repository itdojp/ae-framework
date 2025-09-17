import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: mixed transitions reopen verify (th=4)', () => {
  it(
    formatGWT('OPEN→HALF_OPEN→success×3→fail→OPEN', 'then success×4→CLOSED', 'states follow expected sequence'),
    async () => {
      const timeout = 26;
      const cb = new CircuitBreaker('mixed-transitions-reopen-th4', {
        failureThreshold: 1,
        successThreshold: 4,
        timeout,
        monitoringWindow: 100,
      });

      // trip
      await expect(cb.execute(async () => { throw new Error('e1'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // half open and partial successes then fail → OPEN
      await new Promise((r)=>setTimeout(r, timeout+2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      await expect(cb.execute(async () => 3)).resolves.toBe(3);
      await expect(cb.execute(async () => { throw new Error('e2'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);

      // half open again, full successes to close
      await new Promise((r)=>setTimeout(r, timeout+2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 2)).resolves.toBe(2);
      await expect(cb.execute(async () => 3)).resolves.toBe(3);
      await expect(cb.execute(async () => 4)).resolves.toBe(4);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
    }
  );
});

