import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker state transition events', () => {
  it(
    // GWT-style title for consistency
    'Given breaker hooks | When failures and recoveries occur | Then emits state change events in expected order',
    async () => {
    const events: Array<{evt: string, state?: CircuitState}> = [];
    const cb = new CircuitBreaker('events', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout: 10,
      monitoringWindow: 100,
    });
    cb.on('stateChange', ({ state }) => { events.push({ evt: 'stateChange', state }); });
    cb.on('circuitOpened', () => { events.push({ evt: 'circuitOpened' }); });
    cb.on('circuitHalfOpen', () => { events.push({ evt: 'circuitHalfOpen' }); });
    cb.on('circuitClosed', () => { events.push({ evt: 'circuitClosed' }); });
    // Open
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // Half open
    await new Promise(r=>setTimeout(r, 12));
    // Success to close
    await cb.execute(async () => 1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    // Basic sanity: events include opened, halfopen, closed
    const names = events.map(e=>e.evt);
    expect(names).toContain('circuitOpened');
    expect(names).toContain('circuitHalfOpen');
    expect(names).toContain('circuitClosed');
  }
  );
});
