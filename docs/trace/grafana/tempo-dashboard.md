# Grafana Tempo Dashboard PoC

Issue refs: #1036 / #1011 / #1038

## Overview
This document sketches a minimal Grafana dashboard that surfaces KvOnce traces stored in Tempo. It assumes the `docker/otlp-tempo` stack is running and KvOnce spans contain `kvonce_run_id`, `kvonce_branch`, and `kvonce_payload_sha` attributes (see `scripts/trace/run-kvonce-conformance.sh`).

## Tempo datasource configuration
1. In Grafana, add a data source of type **Tempo** with the URL pointing to the Tempo instance (default `http://localhost:3200`).
2. Enable TraceQL support.

## Dashboard JSON snippet
```json
{
  "title": "KvOnce Trace Overview",
  "panels": [
    {
      "title": "Trace counts by branch",
      "type": "timeseries",
      "targets": [
        {
          "datasource": { "type": "tempo", "uid": "tempo" },
          "queryType": "traceql",
          "query": "{ kvonce_run_id != '' } | stats count() by kvonce_branch"
        }
      ]
    },
    {
      "title": "Recent errors",
      "type": "table",
      "targets": [
        {
          "datasource": { "type": "tempo", "uid": "tempo" },
          "queryType": "traceql",
          "query": "{ status = 'error' } | fields service.name, status_message, kvonce_run_id"
        }
      ]
    }
  ]
}
```

## Next steps
- [ ] Surface verify-lite envelope metrics alongside Tempo stats.
- [ ] Add panels that highlight mutation survivors per run.
- [ ] Provide `scripts/trace/export-dashboard.sh` to sync dashboards through CI.
