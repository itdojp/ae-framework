import { describe, expect, it } from 'vitest';
import { renderMermaidStateMachine } from '../../../src/state-machine/render.js';

const machine = {
  schemaVersion: '1.0.0',
  id: 'order-estimate',
  initial: 'Start State',
  states: [{ name: 'Start State' }, { name: 'End State' }],
  events: ['GO'],
  transitions: [
    {
      from: 'Start State',
      event: 'GO',
      guard: 'ready',
      actions: ['notify'],
      to: 'End State',
    },
  ],
};

describe('renderMermaidStateMachine', () => {
  it('renders a deterministic mermaid diagram', () => {
    const output = renderMermaidStateMachine(machine);
    expect(output).toContain('stateDiagram-v2');
    expect(output).toContain('state "Start State" as Start_State');
    expect(output).toContain('state "End State" as End_State');
    expect(output).toContain('[*] --> Start_State');
    expect(output).toContain('Start_State --> End_State: GO [ready] / notify');
  });

  it('escapes labels and ensures unique IDs', () => {
    const output = renderMermaidStateMachine({
      schemaVersion: '1.0.0',
      id: 'edge-cases',
      initial: 'Quote "State"\n',
      states: [
        { name: 'Quote "State"\n' },
        { name: 'A-B' },
        { name: 'A B' },
        { name: '!!!' },
      ],
      events: ['GO'],
      transitions: [
        { from: 'Quote "State"\n', event: 'GO', to: 'A-B' },
        { from: 'A-B', event: 'GO', to: 'A B' },
        { from: 'A B', event: 'GO', to: '!!!' },
      ],
    });

    expect(output).toContain('state "Quote \'State\'" as Quote_State');
    expect(output).toContain('state "A-B" as A_B');
    expect(output).toContain('state "A B" as A_B_1');
    expect(output).toContain('state "!!!" as state');
  });
});
