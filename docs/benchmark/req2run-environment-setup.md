---
docRole: ssot
lastVerified: '2026-03-12'
owner: benchmark-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Req2Run Benchmark Integration — Environment Setup

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

Req2Run ベンチマーク統合の環境セットアップ手順です。ローカル/CI の前提、リポジトリ配置（`REQ2RUN_BENCHMARK_REPO` / `/tmp/req2run-benchmark`）、インストール/ビルド、クイックランの手順を説明します。

This guide explains how to set up and run the Req2Run benchmark integration with ae-framework on local machines and in CI.

## Prerequisites
- Node.js 20+
- pnpm 8/10 via corepack (`corepack enable`)
- Git installed

Optional (local cloning mode):
- Access to the Req2Run benchmark repository

## Repository Location Options
ae-framework can consume the Req2Run benchmark problems from:

- Cloned repo directory (recommended for local debugging)
  - Set `REQ2RUN_BENCHMARK_REPO=/path/to/req2run-benchmark`
- Auto-managed temp directory (CI-friendly)
  - If `REQ2RUN_BENCHMARK_REPO` is unset, the runner expects the repo at `/tmp/req2run-benchmark`. Use a CI step to clone into that path.

Reference: `src/benchmark/req2run/runners/BenchmarkRunner.ts` uses `process.env.REQ2RUN_BENCHMARK_REPO || '/tmp/req2run-benchmark'`.

## Install and Build
```bash no-doctest
corepack enable
pnpm install --frozen-lockfile
pnpm run build
```

## Quick Run (Local)
Basic integration run with default config and reports written under `reports/benchmark`:

```bash no-doctest
# Option 1: use a local clone
export REQ2RUN_BENCHMARK_REPO="$HOME/dev/req2run-benchmark"

# Option 2: clone into the default path
mkdir -p /tmp && git clone https://github.com/itdojp/req2run-benchmark.git /tmp/req2run-benchmark || true

# Run basic suite
pnpm benchmark:basic

# Or list and run via CLI
pnpm benchmark:list
pnpm benchmark
```

Artifacts and reports:
- JSON/Markdown/CSV reports under `reports/benchmark/`
- CI examples: `src/benchmark/req2run/examples/`

## CI Integration (Minimal)
Add a step before running the benchmark to ensure the repository is present:

```yaml no-doctest
- name: Prepare Req2Run repository
  run: |
    git clone --depth 1 https://github.com/itdojp/req2run-benchmark /tmp/req2run-benchmark || true
    echo "REQ2RUN_BENCHMARK_REPO=/tmp/req2run-benchmark" >> $GITHUB_ENV

- name: Run Req2Run benchmark (CI profile)
  run: pnpm benchmark:ci
```

The CI profile writes results to `reports/benchmark` and shortens execution for pipeline stability. Tune depths, categories, and timeouts under `src/benchmark/req2run/config/default.ts` or by providing a config file.

### Light Mode and Dry Run
- For PRs where speed and stability are critical, use the light mode dry-run to validate configuration without executing:
  - `pnpm tsx src/cli/benchmark-cli.ts run --ci --light --dry-run`
- This mode:
  - Restricts to a few enabled problems
  - Runs serially (no parallelism)
  - Skips execution (prints what would run)
  - Is already used in `ae-ci` workflow as a sanity check

## Custom Configuration
You can generate and pass a benchmark config file:

```bash no-doctest
pnpm benchmark:init               # writes ./configs/benchmark-config.json
pnpm benchmark -- --config ./configs/benchmark-config.json
```

In code, the default report directory is `./reports/benchmark` (see `config.default.ts`).

## Troubleshooting
- Repo not found: ensure `REQ2RUN_BENCHMARK_REPO` points to a valid path or clone into `/tmp/req2run-benchmark`.
- Long runtimes: use the CI profile (`pnpm benchmark:ci`) or narrow the category/difficulty.
- Missing reports: check job logs for `reports/benchmark` path; ensure the process has write permissions.
