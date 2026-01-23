export type CounterexamplePropertyKind =
  | 'INVARIANT'
  | 'LIVENESS'
  | 'THEOREM'
  | 'CONFORMANCE'
  | 'UNKNOWN';

export interface CounterexampleViolatedProperty {
  kind: CounterexamplePropertyKind;
  name: string;
  message?: string;
  // Allow backends to attach extra details without widening the core contract.
  [key: string]: unknown;
}

export interface CounterexampleTraceStep {
  index: number;
  state: Record<string, unknown>;
  action?: string;
  meta?: Record<string, unknown>;
  [key: string]: unknown;
}

export interface Counterexample {
  schemaVersion: string;
  backend?: string;
  spec?: string;
  violated: CounterexampleViolatedProperty;
  trace: CounterexampleTraceStep[];
  hints?: Record<string, unknown>;
  raw?: Record<string, unknown>;
  [key: string]: unknown;
}

