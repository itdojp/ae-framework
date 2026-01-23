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

export type VerifierVerdict = 'satisfied' | 'violated' | 'unknown' | 'error' | 'not_run';

export interface VerificationProperty {
  kind: CounterexamplePropertyKind;
  name: string;
  status: 'satisfied' | 'violated' | 'unknown';
  message?: string;
}

export interface VerificationResult {
  backend: string;
  verdict: VerifierVerdict;
  properties: VerificationProperty[];
  counterexamples: Counterexample[];
  summary?: Record<string, unknown>;
}

export interface TlcSummary {
  engine: string;
  file: string;
  ran: boolean;
  status: string;
  output?: string;
  timestamp?: string;
}

export interface ApalacheSummary {
  tool?: 'apalache';
  engine?: 'apalache';
  file: string;
  ran: boolean;
  status: string;
  ok?: boolean | null;
  errorCount?: number;
  timeMs?: number | null;
  output?: string;
  timestamp?: string;
}
