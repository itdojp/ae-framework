import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: CircuitBreaker HALF_OPEN failure immediately reopens (successThreshold ∈ {3,4,5})', () => {
  for (const th of [3, 4, 5]) {
    it(
      formatGWT(
        `OPEN after initial failure (th=${th})`,
        `less than ${th} successes in HALF_OPEN, then a failure`,
        'returns to OPEN immediately'
      ),
      async () => {
        const timeout = 35;
        const cb = new CircuitBreaker(`half-open-fail-th-${th}`, {
          failureThreshold: 1,
          successThreshold: th,
          timeout,
          monitoringWindow: 100,
        });

        // Initial failure → OPEN
        await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
        expect(cb.getState()).toBe(CircuitState.OPEN);

        // Wait to allow HALF_OPEN
        await new Promise((r) => setTimeout(r, timeout + 5));
        expect([CircuitState.HALF_OPEN, CircuitState.OPEN]).toContain(cb.getState());

        // Fewer than successThreshold successes
        for (let i = 0; i < th - 1; i++) {
          await expect(cb.execute(async () => 1)).resolves.toBe(1);
          // During HALF_OPEN we must not be CLOSED yet
          expect([CircuitState.HALF_OPEN, CircuitState.CLOSED]).toContain(cb.getState());
        }

        // One failure in HALF_OPEN → immediately OPEN
        await expect(cb.execute(async () => { throw new Error('fail-again'); })).rejects.toBeInstanceOf(Error);
        expect(cb.getState()).toBe(CircuitState.OPEN);
      }
    );
  }
});

