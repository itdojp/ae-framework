# Replay Coverage Metrics (#411)

Metrics
- totalEvents: total count of events replayed
- byType: object mapping event name → count
- violations: list of violated invariants (if any)

Artifact
- Include in PR sidecar JSON `artifacts/summary/combined.json` under key `replay`.

Computation (pseudo)
```ts
const events = load('artifacts/domain/events.json');
const byType: Record<string, number> = {};
for (const e of events) byType[e.name] = (byType[e.name] || 0) + 1;
const totalEvents = events.length;
const violations = loadOptional('examples/inventory/artifacts/domain/events.replay-failure.sample.json')?.violatedInvariants ?? [];
writeJson('artifacts/summary/combined.json', { replay: { totalEvents, byType, violations } }, { merge: true });
```
