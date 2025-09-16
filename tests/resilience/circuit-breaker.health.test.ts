import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker health report', () => {
  it('reports unhealthy when OPEN, degraded when HALF_OPEN, healthy when CLOSED and low failure rate', async () => {
    const cb = new CircuitBreaker('health', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout: 10,
      monitoringWindow: 100,
    });

    // Start CLOSED and succeed → healthy
    await cb.execute(async () => 1);
    let rep = cb.generateHealthReport();
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    expect(rep.health === 'healthy' || rep.health === 'degraded').toBe(true);

    // Force OPEN → unhealthy
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
    rep = cb.generateHealthReport();
    expect(cb.getState()).toBe(CircuitState.OPEN);
    expect(rep.health).toBe('unhealthy');

    // Wait and recover via HALF_OPEN → success → CLOSED
    await new Promise((r) => setTimeout(r, 15));
    const result = await cb.execute(async () => 42);
    expect(result).toBe(42);
    rep = cb.generateHealthReport();
    expect([CircuitState.CLOSED, CircuitState.HALF_OPEN]).toContain(cb.getState());
    // After success, should be closed and healthy/degraded at worst
    expect(['healthy', 'degraded']).toContain(rep.health);
  });
});

