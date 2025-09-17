import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker timeout extremes (quick)', () => {
  it(
    formatGWT('very small timeout', 'fail -> wait -> success closes', 'state transitions OPEN -> HALF_OPEN -> CLOSED'),
    async () => {
      const timeout = 8;
      const cb = new CircuitBreaker('tiny-timeout', { failureThreshold: 1, successThreshold: 1, timeout, monitoringWindow: 50 });
      await expect(cb.execute(async () => { throw new Error('x'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
    }
  );

  it(
    formatGWT('medium timeout', 'fail -> call before timeout', 'rejects & remains OPEN until timeout elapses'),
    async () => {
      const timeout = 30;
      const cb = new CircuitBreaker('mid-timeout', { failureThreshold: 1, successThreshold: 2, timeout, monitoringWindow: 50 });
      await expect(cb.execute(async () => { throw new Error('x'); })).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      // call before timeout expires should still be OPEN
      await new Promise(r => setTimeout(r, 5));
      await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(Error);
      expect(cb.getState()).toBe(CircuitState.OPEN);
      await new Promise(r => setTimeout(r, timeout + 2));
      // now allow success trial 2 times, then CLOSED
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      await expect(cb.execute(async () => 1)).resolves.toBe(1);
      expect(cb.getState()).toBe(CircuitState.CLOSED);
    }
  );
});

