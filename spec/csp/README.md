# CSP Specs

> 🌍 Language / 言語: English | 日本語

This directory contains CSP / CSPM-style specifications for concurrency/protocol modeling.

## Current status

- CI integration is wired as **non-blocking**.
  - In `Formal Verify`, the `verify:csp` job installs and uses `cspx` on GitHub-hosted runners (label/dispatch gated).
  - The CI smoke target uses `spec/csp/cspx-smoke.cspm` to stay within cspx's currently supported subset.
- To execute CSP checks locally, set `CSP_RUN_CMD` (see below) or install a supported tool.

## Toolchain options (local)

The runner supports these backends (best-effort, in this order):

1) `CSP_RUN_CMD` (shell command)
2) `cspx` (typecheck / basic assertion check, OSS)
3) FDR `refines` (typecheck)
4) `cspmchecker` (typecheck, OSS)

`cspx` example (recommended):

```bash
# Smoke sample within cspx's currently supported frontend subset:
cspx --version
cspx typecheck --help | grep -- --summary-json
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

FDR (commercial) example:

```bash
refines --typecheck --format plain spec/csp/sample.cspm
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck
```

If your CSPM file includes FDR assertions (e.g., deadlock freedom), you can run them:

```bash
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode assertions
```

`cspmchecker` example:

```bash
cspmchecker spec/csp/sample.cspm
pnpm run verify:csp -- --file spec/csp/sample.cspm
```

## Files

- `sample.cspm`: minimal send/receive example (CSPM-like)
- `cspx-smoke.cspm`: minimal smoke sample designed to be accepted by `cspx` (v0.1 subset)

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
- `artifacts/hermetic-reports/formal/cspx-result.json` (when `cspx` backend is used)
- `metrics` in `cspx-result.json` is optional; ae-framework consumes required fields and ignores optional extensions.

`verify:csp` with `cspx` uses the contract pair:
- `--output artifacts/hermetic-reports/formal/cspx-result.json`
- `--summary-json artifacts/hermetic-reports/formal/csp-summary.json`

See also:
- `docs/quality/formal-csp.md` (usage / artifact schema / example outputs)
- `https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md`
- `https://github.com/itdojp/cspx/blob/main/docs/result-json.md`
- `https://github.com/itdojp/cspx/blob/main/docs/explainability.md`
- `https://github.com/itdojp/cspx/blob/main/docs/validation-report.md`

---

## 日本語（概要）

このフォルダには CSP（プロセス代数）系の仕様（`.csp` / `.cspm` 等）を配置し、並行/プロトコルの観点（デッドロック、発散、トレース整合など）を補強するための入口を提供します。

### 現状

- CI 統合は **non-blocking** です。  
  - `Formal Verify` の `verify:csp` ジョブでは、GitHub-hosted runner に `cspx` を導入して実行します（ラベル/dispatchで制御）。  
  - CI のスモーク対象は、cspx の現行対応サブセットに合わせて `spec/csp/cspx-smoke.cspm` を使用します。  
- 実際に CSP ツールを実行する場合は `CSP_RUN_CMD` を設定するか、対応ツール（`refines`/`cspmchecker`）を導入してください。

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
- `artifacts/hermetic-reports/formal/cspx-result.json`（`cspx` 利用時）
- `cspx-result.json` の `metrics` は optional です。ae-framework は必須フィールドを利用し、拡張フィールドを安全に読み飛ばします。

関連ドキュメント:
- `../../docs/quality/formal-csp.md`（使い方/成果物/実行結果例）
- `https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md`
- `https://github.com/itdojp/cspx/blob/main/docs/result-json.md`
- `https://github.com/itdojp/cspx/blob/main/docs/explainability.md`
- `https://github.com/itdojp/cspx/blob/main/docs/validation-report.md`

---

## ツール候補（ローカル）

ランナーは次のバックエンドを（利用可能なら）優先順に使用します。

1) `CSP_RUN_CMD`（シェル実行）
2) `cspx`（型検査/基本チェック、OSS）
3) FDR `refines`（型検査）
4) `cspmchecker`（型検査、OSS）

`cspx` 例（推奨）:

```bash
cspx --version
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

FDR（商用）例:

```bash
refines --typecheck --format plain spec/csp/sample.cspm
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck
```

FDR の assertion（例: deadlock free）を実行したい場合:

```bash
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode assertions
```

`cspmchecker` 例:

```bash
cspmchecker spec/csp/sample.cspm
pnpm run verify:csp -- --file spec/csp/sample.cspm
```
