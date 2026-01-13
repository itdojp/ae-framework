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
