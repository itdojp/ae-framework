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
});
