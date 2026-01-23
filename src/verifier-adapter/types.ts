export type CounterexamplePropertyKind =
  | 'INVARIANT'
  | 'LIVENESS'
  | 'THEOREM'
  | 'CONFORMANCE'
  | 'UNKNOWN';

export type CounterexampleTraceIndex = number;

export type NonEmptyArray<T> = [T, ...T[]];

export interface CounterexampleViolatedProperty {
  kind: CounterexamplePropertyKind;
  name: string;
  message?: string;
}

export interface CounterexampleTraceStep {
  // Non-negative integer. Enforced at runtime by schema/counterexample.schema.json.
  index: CounterexampleTraceIndex;
  state: Record<string, unknown>;
  action?: string;
  meta?: Record<string, unknown>;
}

export interface Counterexample {
  schemaVersion: string;
  backend?: string;
  spec?: string;
  violated: CounterexampleViolatedProperty;
  // Non-empty array. Enforced at runtime by schema/counterexample.schema.json.
  trace: NonEmptyArray<CounterexampleTraceStep>;
  hints?: Record<string, unknown>;
  raw?: Record<string, unknown>;
}

// Naming alias for consistency with the existing CounterExample naming in FormalAgent.
export type CounterExample = Counterexample;
