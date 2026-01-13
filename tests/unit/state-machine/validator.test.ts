import { describe, expect, it } from 'vitest';
import { validateStateMachineDefinition } from '../../../src/state-machine/validator.js';

const baseMachine = {
  schemaVersion: '1.0.0',
  id: 'machine',
  initial: 'IDLE',
  states: [{ name: 'IDLE' }, { name: 'RUNNING' }],
  events: ['START', 'STOP'],
  transitions: [
    { from: 'IDLE', event: 'START', to: 'RUNNING' },
    { from: 'RUNNING', event: 'STOP', to: 'IDLE' },
  ],
  metadata: { owner: 'team' },
};

describe('validateStateMachineDefinition', () => {
  it('accepts a valid definition', () => {
    const result = validateStateMachineDefinition(baseMachine);
    expect(result.ok).toBe(true);
    expect(result.issues).toHaveLength(0);
  });

  it('reports schema errors for invalid payloads', () => {
    const result = validateStateMachineDefinition({});
    expect(result.ok).toBe(false);
    expect(result.issues.some((issue) => issue.code === 'SCHEMA_INVALID')).toBe(true);
  });

  it('detects duplicate states and events', () => {
    const result = validateStateMachineDefinition({
      ...baseMachine,
      states: [{ name: 'IDLE' }, { name: 'IDLE' }],
      events: ['START', 'START'],
    });
    expect(result.ok).toBe(false);
    expect(result.issues.some((issue) => issue.code === 'DUPLICATE_STATE')).toBe(true);
    expect(result.issues.some((issue) => issue.code === 'DUPLICATE_EVENT')).toBe(true);
  });

  it('detects undefined references and ambiguous transitions', () => {
    const result = validateStateMachineDefinition({
      ...baseMachine,
      initial: 'MISSING',
      transitions: [
        { from: 'IDLE', event: 'START', to: 'RUNNING' },
        { from: 'IDLE', event: 'START', to: 'RUNNING' },
        { from: 'RUNNING', event: 'UNKNOWN', to: 'IDLE' },
      ],
    });
    expect(result.ok).toBe(false);
    expect(result.issues.some((issue) => issue.code === 'INITIAL_NOT_FOUND')).toBe(true);
    expect(result.issues.some((issue) => issue.code === 'UNDEFINED_EVENT_REF')).toBe(true);
    expect(result.issues.some((issue) => issue.code === 'AMBIGUOUS_TRANSITION')).toBe(true);
  });
});
