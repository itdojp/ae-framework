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
  - Execution is opt-in and will be implemented in follow-up (set `ALLOY_JAR` to prepare)

## Local run

```bash
# Run TLC locally (report-only):
npm run verify:model

# Optional: provide a custom TLA+ tools URL
TLA_TOOLS_URL=https://example.com/tla2tools.jar npm run verify:model

# Optional (future): prepare Alloy jar path
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model
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

