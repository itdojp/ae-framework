# Domain Events → Contracts & Replay

Goals
- From `domainEvents[]`, generate:
  - Zod contracts (runtime validation)
  - Replay fixtures to verify aggregate invariants over event sequences

Artifacts
- `artifacts/domain/events.json` — normalized events and metadata
- `formal/summary.json` — aligned with replay verification
- `artifacts/properties/summary.json` — keep {seed, runs, version} when replay uses property-based exploration

Zod Contract Sketch
```ts
import { z } from 'zod';

export const DomainEvent = z.object({
  name: z.string(),
  occursOn: z.string().optional(),
  payload: z.record(z.any()).default({})
});

export type DomainEventT = z.infer<typeof DomainEvent>;
```

Replay Test Sketch
```ts
import { expect, describe, it } from 'vitest';
import { DomainEvent } from './contracts';

describe('replay invariants', () => {
  it('holds invariants for event sequence', async () => {
    const events = load('artifacts/domain/events.json').map(DomainEvent.parse);
    const state = createAggregate();
    for (const e of events) apply(state, e);
    for (const inv of invariants) expect(inv(state)).toBe(true);
  });
});
```

CLI
- `npm run test:replay` runs the replay suite and reports invariant failures with traceId.

PR Requirements
- Include event sequence snippet and link to `formal/summary.json`.

## Failure Case Sample
- See examples/inventory/artifacts/domain/events.replay-failure.sample.json
- Reported with traceId and violated invariants for CI/PR aggregation.
