# Property Harness Usage (scripts/testing/property-harness.mjs)

Run
```bash
npm run test:property
# or focus a specific trace
TRACE_ID=inv-001 npm run test:property:focus
```

Output (artifacts/properties/summary.json)
```json
{
  "traceId": "inv-001",
  "seed": 123456789,
  "runs": 50,
  "version": "0.1",
  "passed": true,
  "note": "fast-check not available or skipped"
}
```
