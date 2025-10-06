# Tempo Dashboard Notes (Draft)

Issue: #1038 / #1011

## Objective
Visualise KvOnce envelope data alongside Tempo traces.

## Proposed Panels
1. **Run Overview**
   - datasource: JSON (report-envelopes via webhook) + Tempo
   - fields: `correlation.runId`, `summary.cases[].issueCount`, envelope status badges.
2. **Trace Drilldown**
   - Use `traceIds` from envelope to jump into Tempo search (link panel).
3. **Mutation / Lint context**
   - embed verify-lite envelope metrics (lint issue counts, mutation score) as context for trace failures.

## Next Steps
- Establish ingestion workflow (e.g., push envelope to Loki/JSON API) and create prototype dashboard.
- Document Grafana dashboard export once available.
