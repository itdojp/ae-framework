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
    - `ALLOY_FAIL_REGEX`: regex for failure detection (default: `Exception|ERROR|FAILED|Counterexample|assertion`, case‑insensitive)
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

# Prefer JSON-array for complex arguments (quotes/spaces safe)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model
```

## Artifacts and interpretation

- `artifacts/codex/model-check.json`
  - tlc.results: array of `{ module, ok, code, log }`
  - tlc.skipped/errors: reasons for skip/errors
  - alloy.results/skipped/errors: detection and readiness info
 - `artifacts/codex/*.tlc.log.txt`: Raw TLC logs per module
 - `artifacts/codex/*.alloy.log.txt`: Raw Alloy logs per spec (when executed)

### PR summary

- Posts a Verification Summary comment on PRs with:
  - Traceability totals and linked examples
  - Model Check (TLC): ok/total and top non‑OK modules
  - Alloy: ok/total (when executed) and top non‑OK specs, or “detected N specs (execution skipped)” when jar not provided
  - Optional enforcement: add PR label `enforce-formal` to fail the PR when TLC/Alloy has failures (default is report-only)

### Headless Alloy examples

Run Alloy headless when you can provide a jar (or CLI):

```bash
# Minimal
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# With JSON-array args (quotes/spaces safe)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model

# With regex tuning and timeout
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assert(ion)?' \
  ALLOY_TIMEOUT_MS=180000 \
  npm run verify:model
```


## Next steps

- Gate failures on model checking (opt-in label or directory presence)
- Implement headless Alloy execution (jar/CLI options) with timeouts
- Post PR comments summarizing formal results (green/red + links)
# Notes

- If `ALLOY_JAR` is not set, Alloy execution is skipped (detection only). Provide the jar path for headless runs.
- The runner treats non-zero exit or timeouts as failures; logs are saved under `artifacts/codex/*.alloy.log.txt`.

## Failure pattern guidance (Alloy)

Different Alloy jars may emit different failure strings. You can tune `ALLOY_FAIL_REGEX` as needed.

Common patterns:

- `Exception` – any unhandled exceptions
- `ERROR` – generic error prefix
- `FAILED` – assertion/check failure markers
- `Counterexample` – counterexample found for an assertion
- `assertion` – assertion-related lines (some jars include lowercase)

Combine with `|` to build a case-insensitive regex. Example:

```
ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assertion'
```

Jar/version specific notes (examples, adjust as needed):

- Some builds emit `Counterexample found.
  Assertion XYZ is invalid` for failing `assert` blocks.
- Others use `FAILED` preceded by the assertion name or a check ID.
- Parser-level issues often include `Exception` or `ERROR` with a stack trace.

Tip: Start with the default and add the most common markers seen in your CI logs. Keep the regex concise to avoid false positives.

### Regex presets (examples)

Use one of these as a starting point via `ALLOY_FAIL_REGEX`.

- Default (balanced):
  - `Exception|ERROR|FAILED|Counterexample|assertion`
- Strict (catch more noise, may include false positives):
  - `Exception|ERROR|FAILED|FATAL|SEVERE|Counterexample|assert(ion)?|Traceback`
- Permissive (only clear assertion/counterexample failures):
  - `FAILED|Counterexample|assert(ion)?`
- Jar variant A (counterexample phrasing):
  - `Counterexample found|Assertion .* is invalid|FAILED`
- Parser-heavy (catch parse/semantic issues):
  - `Exception|ERROR|Parse|Lexer|Stack trace|Traceback`

Export example in CI or local shell:

```
ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assertion' npm run verify:model
```
