export interface StateMachineState {
  name: string;
  description?: string;
  entry?: string[];
  exit?: string[];
  meta?: Record<string, unknown>;
}

export interface StateMachineTransition {
  from: string;
  to: string;
  event: string;
  guard?: string;
  actions?: string[];
  meta?: Record<string, unknown>;
}

export interface StateMachineDefinition {
  schemaVersion: string;
  id?: string;
  name?: string;
  description?: string;
  initial: string;
  states: StateMachineState[];
  events: string[];
  transitions: StateMachineTransition[];
  metadata?: Record<string, unknown>;
  correlation?: Record<string, unknown>;
}

function toMermaidId(name: string, used: Set<string>) {
  const base = name.replace(/[^A-Za-z0-9_]/g, '_');
  const prefixed = base.length > 0 && !/^[0-9]/.test(base) ? base : `S_${base}`;
  let candidate = prefixed || 'S';
  let counter = 1;
  while (used.has(candidate)) {
    candidate = `${prefixed}_${counter}`;
    counter += 1;
  }
  used.add(candidate);
  return candidate;
}

function buildLabel(transition: StateMachineTransition) {
  const parts: string[] = [transition.event];
  if (transition.guard) {
    parts.push(`[${transition.guard}]`);
  }
  if (transition.actions && transition.actions.length > 0) {
    parts.push(`/ ${transition.actions.join(', ')}`);
  }
  return parts.join(' ');
}

export function renderMermaidStateMachine(machine: StateMachineDefinition): string {
  const usedIds = new Set<string>();
  const stateIds = new Map<string, string>();
  for (const state of machine.states) {
    stateIds.set(state.name, toMermaidId(state.name, usedIds));
  }

  const lines: string[] = ['stateDiagram-v2'];
  const indent = '  ';
  const initialId = stateIds.get(machine.initial) ?? toMermaidId(machine.initial, usedIds);
  lines.push(`${indent}[*] --> ${initialId}`);

  for (const state of machine.states) {
    const id = stateIds.get(state.name) ?? toMermaidId(state.name, usedIds);
    if (id === state.name) {
      lines.push(`${indent}state ${id}`);
    } else {
      lines.push(`${indent}state "${state.name}" as ${id}`);
    }
  }

  for (const transition of machine.transitions) {
    const fromId = stateIds.get(transition.from) ?? toMermaidId(transition.from, usedIds);
    const toId = stateIds.get(transition.to) ?? toMermaidId(transition.to, usedIds);
    const label = buildLabel(transition);
    lines.push(`${indent}${fromId} --> ${toId}: ${label}`);
  }

  return lines.join('\n');
}
