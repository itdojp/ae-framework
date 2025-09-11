# JUnit/XML Interop Notes

- Keep core dependency-free from XML parsers; normalization happens in adapters or CI.
- Upload raw JUnit artifacts for external tooling, but aggregate PR summary from JSON.
- Suggested paths:
  - `artifacts/<adapter>/summary.json` (normalized, PR aggregation source)
  - `artifacts/<adapter>/junit.xml` (optional raw)
- Include `traceId` in JSON where applicable.
