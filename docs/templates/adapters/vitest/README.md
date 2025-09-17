# Vitest Adapter Templates (Examples)

Vitest can emit JSON summary which can be aggregated in PR comments.

- Write a minimal JSON summary to `artifacts/adapters/vitest/summary.json`.
- Upload the directory as artifact in CI, and aggregate via `scripts/adapters/aggregate-artifacts.mjs`.

Minimal CI snippet:
```yaml
- name: Aggregate Vitest artifacts
  run: node scripts/adapters/aggregate-artifacts.mjs || true
  if: always()
```

Minimal JSON shape (`artifacts/adapters/vitest/summary.json`):
```json
{
  "adapter": "vitest",
  "summary": "passed=200 failed=0",
  "status": "ok",
  "traceId": null
}
```

Alternative compact shape:
```
{
  "tool": "vitest",
  "summary": { "passed": 42, "failed": 0, "skipped": 0 },
  "suites": [ { "name": "unit", "passed": 30, "failed": 0 } ]
}
```
Aggregated by `scripts/adapters/aggregate-artifacts.mjs` into a single PR summary.
