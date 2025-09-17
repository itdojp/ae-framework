import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker mixed timeouts sequence (quick)', () => {
  it(
    formatGWT('fail at tiny timeout', 'recover then fail at mid timeout', 'OPEN -> HALF_OPEN -> CLOSED -> OPEN'),
    async () => {
      const tiny = new CircuitBreaker('tiny', { failureThreshold: 1, successThreshold: 1, timeout: 8, monitoringWindow: 50 });
      await expect(tiny.execute(async () => { throw new Error('x'); })).rejects.toBeInstanceOf(Error);
      expect(tiny.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, 10));
      await expect(tiny.execute(async () => 1)).resolves.toBe(1);
      expect(tiny.getState()).toBe(CircuitState.CLOSED);

      const mid = new CircuitBreaker('mid', { failureThreshold: 1, successThreshold: 2, timeout: 25, monitoringWindow: 50 });
      await expect(mid.execute(async () => { throw new Error('y'); })).rejects.toBeInstanceOf(Error);
      expect(mid.getState()).toBe(CircuitState.OPEN);
      // before timeout, remains OPEN
      await new Promise(r => setTimeout(r, 5));
      await expect(mid.execute(async () => 1)).rejects.toBeInstanceOf(Error);
      expect(mid.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, 22));
      await expect(mid.execute(async () => 1)).resolves.toBe(1);
      await expect(mid.execute(async () => 1)).resolves.toBe(1);
      expect(mid.getState()).toBe(CircuitState.CLOSED);
    }
  );
});

