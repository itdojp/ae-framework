import type { StateMachineDefinition, StateMachineTransition } from './types.js';

/**
 * Generate a Mermaid-safe state ID with deterministic collision handling.
 * - Non-alphanumeric characters are replaced with "_".
 * - IDs starting with digits are prefixed with "S_".
 * - Collisions are resolved by appending "_<n>".
 */
function toMermaidId(name: string, used: Set<string>) {
  const base = name.replace(/[^A-Za-z0-9_]/g, '_');
  const collapsed = base.replace(/_+/g, '_').replace(/^_+|_+$/g, '');
  const normalized = collapsed.length === 0 ? 'state' : collapsed;
  const prefixed = /^[0-9]/.test(normalized) ? `S_${normalized}` : normalized;
  let candidate = prefixed;
  let counter = 1;
  while (used.has(candidate)) {
    candidate = `${prefixed}_${counter}`;
    counter += 1;
  }
  used.add(candidate);
  return candidate;
}

function sanitizeMermaidText(value: string) {
  return value.replace(/\r?\n/g, ' ').trim();
}

function escapeMermaidLabel(value: string) {
  return sanitizeMermaidText(value).replace(/"/g, "'");
}

function buildLabel(transition: StateMachineTransition) {
  const parts: string[] = [sanitizeMermaidText(transition.event)];
  if (transition.guard) {
    parts.push(`[${sanitizeMermaidText(transition.guard)}]`);
  }
  if (transition.actions && transition.actions.length > 0) {
    const actions = transition.actions.map((action) => sanitizeMermaidText(action)).join(', ');
    parts.push(`/ ${actions}`);
  }
  return parts.join(' ');
}

function requireStateId(stateIds: Map<string, string>, stateName: string) {
  const id = stateIds.get(stateName);
  if (!id) {
    throw new Error(`State not found while rendering: ${stateName}`);
  }
  return id;
}

/**
 * Render a Mermaid stateDiagram-v2 from a validated state machine definition.
 */
export function renderMermaidStateMachine(machine: StateMachineDefinition): string {
  const usedIds = new Set<string>();
  const stateIds = new Map<string, string>();
  for (const state of machine.states) {
    stateIds.set(state.name, toMermaidId(state.name, usedIds));
  }

  const lines: string[] = ['stateDiagram-v2'];
  const indent = '  ';
  const initialId = requireStateId(stateIds, machine.initial);
  lines.push(`${indent}[*] --> ${initialId}`);

  for (const state of machine.states) {
    const id = requireStateId(stateIds, state.name);
    if (id === state.name && id === sanitizeMermaidText(state.name)) {
      lines.push(`${indent}state ${id}`);
    } else {
      lines.push(`${indent}state "${escapeMermaidLabel(state.name)}" as ${id}`);
    }
  }

  for (const transition of machine.transitions) {
    const fromId = requireStateId(stateIds, transition.from);
    const toId = requireStateId(stateIds, transition.to);
    const label = buildLabel(transition);
    lines.push(`${indent}${fromId} --> ${toId}: ${label}`);
  }

  return lines.join('\n');
}
