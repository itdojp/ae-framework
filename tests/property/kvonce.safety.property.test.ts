import { describe, expect, it } from 'vitest';
import fc from 'fast-check';

type KvOnceEvent =
  | { type: 'success'; key: string; value: string; reason: null }
  | { type: 'retry'; key: string; value: null; reason: string }
  | { type: 'failure'; key: string; value: null; reason: string };

type KvOnceState = {
  store: Map<string, { written: boolean; value: string | null; retries: number }>;
  events: KvOnceEvent[];
};

interface Operation {
  action: 'put' | 'retry' | 'noop';
  key: string;
  value?: string;
}

const MAX_RETRIES = 3;

function initialiseState(): KvOnceState {
  return {
    store: new Map(),
    events: [],
  };
}

function ensureEntry(state: KvOnceState, key: string) {
  if (!state.store.has(key)) {
    state.store.set(key, { written: false, value: null, retries: 0 });
  }
  return state.store.get(key)!;
}

function put(state: KvOnceState, key: string, value: string) {
  const entry = ensureEntry(state, key);
  if (entry.written) {
    state.events.push({ type: 'failure', key, value: null, reason: 'duplicate' });
    return;
  }
  entry.written = true;
  entry.value = value;
  state.events.push({ type: 'success', key, value, reason: null });
}

function retry(state: KvOnceState, key: string) {
  const entry = ensureEntry(state, key);
  if (entry.retries < MAX_RETRIES) {
    entry.retries += 1;
    state.events.push({ type: 'retry', key, value: null, reason: 'transient' });
  } else {
    state.events.push({ type: 'failure', key, value: null, reason: 'max_retries' });
  }
}

function runOperations(ops: Operation[]): KvOnceState {
  const state = initialiseState();
  for (const op of ops) {
    if (op.action === 'put' && op.value !== undefined) {
      put(state, op.key, op.value);
    } else if (op.action === 'retry') {
      retry(state, op.key);
    }
  }
  return state;
}

describe('KvOnce PoC model', () => {
  const operationArb = fc.record<Operation>({
    action: fc.constantFrom('put', 'retry', 'noop'),
    key: fc.string({ minLength: 1, maxLength: 8 }),
    value: fc.option(fc.string({ minLength: 1, maxLength: 12 }), { nil: undefined }),
  });

  it('a key is written at most once successfully', () => {
    fc.assert(
      fc.property(fc.array(operationArb, { maxLength: 20 }), (ops) => {
        const state = runOperations(ops);
        const successCounts = new Map<string, number>();

        for (const event of state.events) {
          if (event.type === 'success') {
            successCounts.set(event.key, (successCounts.get(event.key) ?? 0) + 1);
          }
        }

        for (const [, count] of successCounts) {
          expect(count).toBeLessThanOrEqual(1);
        }
      })
    );
  });

  it('duplicate writes emit failure events', () => {
    fc.assert(
      fc.property(fc.array(operationArb, { maxLength: 20 }), (ops) => {
        const state = runOperations(ops);
        const seenSuccess = new Set<string>();

        for (const event of state.events) {
          if (event.type === 'success') {
            seenSuccess.add(event.key);
          }
          if (event.type === 'failure' && event.reason === 'duplicate') {
            expect(seenSuccess.has(event.key)).toBe(true);
          }
        }
      })
    );
  });
});
