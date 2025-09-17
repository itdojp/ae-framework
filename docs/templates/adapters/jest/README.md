# Jest Adapter Templates (Examples)

This page shows minimal examples to aggregate Jest test results into JSON suitable for PR summaries.

- Upload raw JUnit XML as artifacts (optional) and aggregate from JSON in CI.
- Keep JSON in `artifacts/adapters/jest/summary.json` for summary scripts.

Minimal CI snippet:
```yaml
- name: Aggregate Jest artifacts
  run: node scripts/adapters/aggregate-artifacts.mjs || true
  if: always()
```

Minimal JSON shape (`artifacts/adapters/jest/summary.json`):
```json
{
  "adapter": "jest",
  "summary": "passed=120 failed=0",
  "status": "ok",
  "traceId": null
}
```

Alternative compact shape:
```
{
  "tool": "jest",
  "summary": { "passed": 12, "failed": 0, "skipped": 1 },
  "files": [ { "path": "tests/foo.test.ts", "passed": 5, "failed": 0 } ]
}
```
This artifact can be aggregated by `scripts/adapters/aggregate-artifacts.mjs` to generate a PR summary.
