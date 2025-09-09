# Formal Checks: TLC/Alloy Integration (Week 1)

This document explains how formal model checking is executed in CI and where to find artifacts.

## What runs in CI

- TLC (TLA+) via GitHub Actions verify workflow
  - Workflow: `.github/workflows/verify.yml` (job `model-check`)
  - Tools: `actions/setup-java` + auto-download of `tla2tools.jar`
  - Runner script: `scripts/verify/run-model-checks.mjs`
  - Behavior: scans for `.tla` files under `artifacts/`, `specs/`, `docs/formal/`
  - Output artifacts: `artifacts/codex/model-check.json`, `artifacts/codex/*.tlc.log.txt`
  - Default: report-only (does not fail CI yet)

- Alloy (Alloy Analyzer): scaffolded detection
  - The runner lists `.als` files and includes them in `model-check.json`
  - Execution (headless) is supported when `ALLOY_JAR` is provided (safe default: `java -jar $ALLOY_JAR {file}`)
  - Optional:
    - `ALLOY_CMD_JSON`: JSON array of extra arguments (preferred, safe)
    - `ALLOY_CMD_ARGS`: whitespace‑separated extra arguments (fallback)
    - `ALLOY_FAIL_REGEX`: regex for failure detection (default: `Exception|ERROR|FAILED`, case‑insensitive)
    - `ALLOY_TIMEOUT_MS` (default 180000)

## Local run

```bash
# Run TLC locally (report-only):
npm run verify:model

# Optional: provide a custom TLA+ tools URL
TLA_TOOLS_URL=https://example.com/tla2tools.jar npm run verify:model

# Optional: prepare Alloy jar path and run headless
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# Extra arguments and timeout (optional)
ALLOY_JAR=$HOME/tools/alloy.jar ALLOY_CMD_ARGS="-someFlag" ALLOY_TIMEOUT_MS=180000 npm run verify:model
```

## Artifacts and interpretation

- `artifacts/codex/model-check.json`
  - tlc.results: array of `{ module, ok, code, log }`
  - tlc.skipped/errors: reasons for skip/errors
  - alloy.results/skipped/errors: detection and readiness info
- `artifacts/codex/*.tlc.log.txt`: Raw TLC logs per module

## Next steps

- Gate failures on model checking (opt-in label or directory presence)
- Implement headless Alloy execution (jar/CLI options) with timeouts
- Post PR comments summarizing formal results (green/red + links)
# Notes

- If `ALLOY_JAR` is not set, Alloy execution is skipped (detection only). Provide the jar path for headless runs.
- The runner treats non-zero exit or timeouts as failures; logs are saved under `artifacts/codex/*.alloy.log.txt`.
