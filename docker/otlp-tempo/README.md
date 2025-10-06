# OTLP + Tempo PoC Stack

This docker-compose stack spins up a minimal OpenTelemetry Collector that forwards incoming OTLP traces to Tempo.

## Usage

```bash
cd docker/otlp-tempo
docker compose up -d
```

The collector listens on:

- OTLP gRPC: `localhost:4317`
- OTLP HTTP: `localhost:4318`

Tempo exposes:

- HTTP API / Grafana Tempo query endpoint: `http://localhost:3200`

To stop the stack:

```bash
docker compose down -v
```

## Integration Notes
- The collector configuration matches the Stage 1 PoC described in `docs/trace/otlp-collector-plan.md`.
- CI can export collected payloads as artifacts and feed them into `scripts/trace/prepare-otlp-trace.mjs`.
- For local testing, send OTLP spans (with `kvonce.event.*` attributes) to `localhost:4317` or `localhost:4318`.
