# Adapter Output Normalization

- Write normalized results to `artifacts/<adapter>/summary.json`.
- Conform to `docs/schemas/artifacts-adapter-summary.schema.json`.
- Provide a one-line summary for PR aggregation.

## JUnit/XML Notes
- Prefer emitting normalized JSON summaries alongside JUnit XML.
- Do not require core to parse XML; keep parsing in adapters/CI if needed.
- Example: upload both `junit.xml` and `artifacts/<adapter>/summary.json`.
