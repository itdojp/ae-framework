# JUnit Adapter Templates (Examples)

This page shows minimal examples to aggregate JUnit results into JSON suitable for PR summaries.

- Upload raw JUnit XML as artifacts (optional)
- Produce a compact JSON at `artifacts/adapters/junit/summary.json`
- Aggregate via `scripts/adapters/aggregate-artifacts.mjs`

Minimal CI snippet:
```yaml
- name: Aggregate JUnit artifacts
  run: node scripts/adapters/aggregate-artifacts.mjs || true
  if: always()
```

Minimal JSON shape (`artifacts/adapters/junit/summary.json`):
```json
{
  "tool": "junit",
  "summary": { "passed": 120, "failed": 0, "skipped": 3 },
  "suites": [ { "name": "unit", "passed": 80, "failed": 0, "skipped": 2 } ]
}
```

This artifact can be aggregated by the adapter aggregator script and shown in a PR summary.
