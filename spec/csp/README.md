# CSP Specs

> 🌍 Language / 言語: English | 日本語

This directory contains CSP / CSPM-style specifications for concurrency/protocol modeling.

## Current status

- CI integration is provided as a **non-blocking stub** until a concrete toolchain is selected.
- To execute CSP checks, set `CSP_RUN_CMD` (see below) or install a supported tool and wire it in.

## Files

- `sample.cspm`: minimal send/receive example (CSPM-like)

## Running (local)

```bash
pnpm run verify:csp -- --file spec/csp/sample.cspm
```

To run an actual CSP tool, provide `CSP_RUN_CMD`.

Example (placeholder):

```bash
# {file} will be replaced with the absolute file path
CSP_RUN_CMD='echo Running CSP tool on {file}' pnpm run verify:csp -- --file spec/csp/sample.cspm
```

Security note
- `CSP_RUN_CMD` is executed via a shell. Do not source it from untrusted input.
- In CI, avoid running `CSP_RUN_CMD` for untrusted PRs (e.g., from forks).

Artifacts:
- `artifacts/hermetic-reports/formal/csp-summary.json`

---

## 日本語（概要）

このフォルダには CSP（プロセス代数）系の仕様（`.csp` / `.cspm` 等）を配置し、並行/プロトコルの観点（デッドロック、発散、トレース整合など）を補強するための入口を提供します。

### 現状

- CI 統合は **non-blocking stub** として提供します（ツールチェーン未確定のため）。  
- 実際に CSP ツールを実行する場合は `CSP_RUN_CMD` を設定してください。

### ローカル実行（例）

```bash
pnpm run verify:csp -- --file spec/csp/sample.cspm
```

`CSP_RUN_CMD` 例（プレースホルダ、`{file}` は絶対パスへ展開）:

```bash
CSP_RUN_CMD='echo Running CSP tool on {file}' pnpm run verify:csp -- --file spec/csp/sample.cspm
```

セキュリティ注意
- `CSP_RUN_CMD` はシェル経由で実行されます。信頼できない入力から値を組み立てないでください。
- CI では、Fork PR 等の「不特定入力」に対して `CSP_RUN_CMD` を実行しない運用を推奨します。

成果物:
- `artifacts/hermetic-reports/formal/csp-summary.json`
