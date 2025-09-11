# Property-based Testing Harness (Proposal for #406)

Objectives
- Minimal harness to run property-based tests with reproducibility and traceability.

Requirements
- Persist `{seed, runs, version}` to `artifacts/properties/summary.json` (see schema).
- Support `--focus=traceId` to limit generation to specific scenarios.
- Output should be CI-friendly and aggregated in PR summary.

Harness Outline (pseudo)
```ts
// no dependency requirement in core; can be in adapter/package
import fc from 'fast-check';

export async function runPropertySuite(traceId: string) {
  const seed = Date.now();
  const runs = 100;
  const version = '0.1';
  const result = await fc.assert(/* property */);
  await writeJson('artifacts/properties/summary.json', { traceId, seed, runs, version, passed: true });
}
```

Notes
- Keep implementation in adapters or optional packages to avoid core bloat.
- Respect schemas in `docs/schemas/`.
