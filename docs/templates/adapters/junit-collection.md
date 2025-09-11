# JUnit + Summary Collection Flow (#408)

- Produce both raw JUnit XML and normalized JSON summary.
- Upload both as CI artifacts; aggregate PR summary from JSON only.

```mermaid
flowchart TD
  A[Run tests] --> B[Generate junit.xml]
  A --> C[Write artifacts/<adapter>/summary.json]
  B --> D[Upload junit.xml]
  C --> E[Upload summary.json]
  E --> F[PR Summary Aggregator]
```

Notes
- Keep XML parsing out of core; use JSON summaries for aggregation.
- Include `traceId` in JSON where applicable.
