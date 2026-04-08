---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- docs/quality/formal-tools-setup.md
lastVerified: '2026-04-08'
---
# CSP Verification (cspx runner)

> 🌍 Language / 言語: English | 日本語

---

## English

This document describes **how to run CSP checks** in ae-framework, and what artifacts to expect.

Scope:
- Runner: `pnpm run verify:csp` (`scripts/formal/verify-csp.mjs`)
- Recommended backend: `cspx` (OSS)
- CI: `Formal Verify` workflow (label/dispatch gated; non-blocking)

### What this runner does (important)

- **Non-blocking**: the runner always exits `0`. It writes a summary JSON and returns successfully even when the CSP check fails.
  - To *enforce* failures, consume `artifacts/hermetic-reports/formal/csp-summary.json` in a gate (not done by default).
- Backend selection order (best-effort):
  1) `CSP_RUN_CMD` (shell)
  2) `cspx`
  3) FDR `refines`
  4) `cspmchecker`

### Install (recommended: cspx)

Pre-reqs:
- Rust toolchain (`cargo`)
- `~/.cargo/bin` is in `PATH`

Install:
```bash
cargo install --git https://github.com/itdojp/cspx --rev 8a67639ea4d3f715e27feb8cd728f46866a905db --locked cspx
```

Verify:
```bash
cspx --version
cspx typecheck --help | grep -- --summary-json
```

Notes:
- CI installs pinned `cspx` when missing, and only forces reinstall when `--summary-json` is not supported (see `.github/workflows/formal-verify.yml`).
- This pin includes `--summary-json` (ae-framework aggregate contract).
- `metrics` in `cspx-result.json` is optional; ae-framework consumes required fields and ignores optional extensions safely.

### Troubleshooting

- If `csp-summary.json` reports `status: "unsupported"` and `artifacts/hermetic-reports/formal/csp-output.txt` (or the path in `outputFile`) shows a CLI error about `--summary-json` (for example, messages containing `unexpected argument`, `unknown argument`, or `wasn't expected`), your `cspx` is too old (upgrade per `docs/quality/formal-tools-setup.md`, or set `CSP_RUN_CMD`).
- If it reports `schema_version mismatch: expected 0.1`, check `cspx-result.json` and align `cspx` to the current contract (`schema_version=0.1`).
- If `detailsFile` is `null`, first verify that `backend` in `csp-summary.json` is `cspx:*`. If `backend` is `cspx:*` and `detailsFile` is `null`, `cspx` did not produce a details JSON; inspect `artifacts/hermetic-reports/formal/csp-output.txt` (or the path in `outputFile`) for the underlying CLI error. For `CSP_RUN_CMD` / `refines` / `cspmchecker` backends, `detailsFile: null` is expected.

### Run

Typecheck (safe default, used for CI smoke):
```bash
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

Assertions:
- `cspx` backend maps `--mode assertions` to a single canonical check:
  - `cspx check --assert "deadlock free" ...`
```bash
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode assertions
```

Custom backend command (shell):
```bash
# {file} is replaced with the absolute file path
CSP_RUN_CMD='echo Running CSP tool on {file}' \
  pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck
```

Security note:
- `CSP_RUN_CMD` is executed via a shell. Do not build it from untrusted input.

### Artifacts

Always produced:
- `artifacts/hermetic-reports/formal/csp-summary.json`

Produced when `cspx` is used:
- `artifacts/hermetic-reports/formal/cspx-result.json`

`cspx` backend invocation contract:
- `--output artifacts/hermetic-reports/formal/cspx-result.json`
- `--summary-json artifacts/hermetic-reports/formal/csp-summary.json`

### Example results (actual run on main)

Environment:
- `node v22.19.0`
- `pnpm 10.0.0`
- `cspx 0.1.0`

Command:
```bash
pnpm -s run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

Console output:
```text
CSP summary written: artifacts/hermetic-reports/formal/csp-summary.json
- file=spec/csp/cspx-smoke.cspm status=ran backend=cspx:typecheck
```

`csp-summary.json` (excerpt):
```json
{
  "tool": "csp",
  "file": "spec/csp/cspx-smoke.cspm",
  "backend": "cspx:typecheck",
  "detailsFile": "artifacts/hermetic-reports/formal/cspx-result.json",
  "resultStatus": "pass",
  "ran": true,
  "status": "ran",
  "exitCode": 0,
  "timestamp": "2026-02-05T23:49:08.300Z",
  "output": "cspx schema=0.1 status=pass exit_code=0 checks=typecheck:pass"
}
```

`cspx-result.json` (excerpt):
```json
{
  "schema_version": "0.1",
  "tool": { "name": "cspx", "version": "0.1.0" },
  "status": "pass",
  "exit_code": 0,
  "checks": [
    { "name": "typecheck", "status": "pass" }
  ]
}
```

Assertions example (expected failure for STOP-only sample):
- `spec/csp/cspx-smoke.cspm` defines `SYSTEM = STOP`, which is a deadlock state.
- Running `--mode assertions` triggers `deadlock free` and therefore reports `fail` with a counterexample tagged `deadlock`.

Upstream references (cspx):
- https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md
- https://github.com/itdojp/cspx/blob/main/docs/result-json.md
- https://github.com/itdojp/cspx/blob/main/docs/explainability.md
- https://github.com/itdojp/cspx/blob/main/docs/validation-report.md

---

## 日本語

本ドキュメントは、ae-framework における **CSP 検査（cspx ランナー）**の使い方と、生成される成果物（実行結果）を整理したものです。

対象範囲:
- 実行エントリ: `pnpm run verify:csp`（`scripts/formal/verify-csp.mjs`）
- 推奨バックエンド: `cspx`（OSS）
- CI: `Formal Verify` ワークフロー（ラベル/手動実行で起動、非ブロッキング）

### このランナーの前提（重要）

- **非ブロッキング**: 失敗しても `verify:csp` 自体は終了コード `0` で終了します。
  成否は `artifacts/hermetic-reports/formal/csp-summary.json` を参照して判断します（既定では「ゲート化」しません）。
- バックエンド選択は（利用可能なら）次の優先順位です:
  1) `CSP_RUN_CMD`（シェル実行）
  2) `cspx`
  3) FDR `refines`
  4) `cspmchecker`

### 導入（推奨: cspx）

前提:
- Rust ツールチェーン（`cargo`）
- `~/.cargo/bin` が `PATH` に含まれていること

インストール（再現性のため commit SHA 固定を推奨）:
```bash
cargo install --git https://github.com/itdojp/cspx --rev 8a67639ea4d3f715e27feb8cd728f46866a905db --locked cspx
```

確認:
```bash
cspx --version
cspx typecheck --help | grep -- --summary-json
```

補足:
- CI は commit SHA 固定で導入します（`.github/workflows/formal-verify.yml`）。
- この固定は ae-framework 連携用の `--summary-json` を含みます。
- `cspx-result.json` の `metrics` は任意項目です。ae-framework 側は必須フィールドを利用し、拡張フィールドを安全に読み飛ばします。

### トラブルシューティング

- `csp-summary.json` の `status` が `"unsupported"` で、`artifacts/hermetic-reports/formal/csp-output.txt`（または `csp-summary.json` の `outputFile`）に `--summary-json` に関する CLI エラー（例: `unexpected argument`, `unknown argument`, `wasn't expected` など）が出る場合、`cspx` が古く互換性がありません（`docs/quality/formal-tools-setup.md` の手順で更新、または `CSP_RUN_CMD` を設定）。
- `schema_version mismatch: expected 0.1` の場合は `cspx-result.json` の `schema_version` を確認し、現行の契約（`schema_version=0.1`）に合わせて `cspx` を更新してください。
- `detailsFile` が `null` の場合は、まず `csp-summary.json` の `backend` が `cspx:*` であることを確認してください。`backend` が `cspx:*` かつ `detailsFile` が `null` の場合、`cspx` が details JSON を生成できていません。`artifacts/hermetic-reports/formal/csp-output.txt`（または `outputFile`）の CLI エラーを確認してください（`backend` が `CSP_RUN_CMD` / `refines` / `cspmchecker` の場合、`detailsFile: null` は通常動作です）。

### 実行方法

型検査（安全な既定。CI スモークで使用）:
```bash
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

Assertions（assertions）:
- `cspx` バックエンドの `--mode assertions` は、v0.1 では **1種類の代表チェック**にマップしています:
  - `cspx check --assert "deadlock free" ...`
```bash
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode assertions
```

任意のツールをコマンドで実行（シェル経由）:
```bash
# {file} は対象ファイルの絶対パスへ置換されます
CSP_RUN_CMD='echo Running CSP tool on {file}' \
  pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck
```

セキュリティ注意:
- `CSP_RUN_CMD` はシェルで実行されます。信頼できない入力を連結して設定しないでください。

### 成果物（実行結果）

常に生成:
- `artifacts/hermetic-reports/formal/csp-summary.json`

`cspx` 利用時に生成:
- `artifacts/hermetic-reports/formal/cspx-result.json`

`cspx` バックエンド呼び出し契約:
- `--output artifacts/hermetic-reports/formal/cspx-result.json`
- `--summary-json artifacts/hermetic-reports/formal/csp-summary.json`

### 実行結果例（main での実測）

環境:
- `node v22.19.0`
- `pnpm 10.0.0`
- `cspx 0.1.0`

コマンド:
```bash
pnpm -s run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

標準出力:
```text
CSP summary written: artifacts/hermetic-reports/formal/csp-summary.json
- file=spec/csp/cspx-smoke.cspm status=ran backend=cspx:typecheck
```

`csp-summary.json`（抜粋）:
```json
{
  "tool": "csp",
  "file": "spec/csp/cspx-smoke.cspm",
  "backend": "cspx:typecheck",
  "detailsFile": "artifacts/hermetic-reports/formal/cspx-result.json",
  "resultStatus": "pass",
  "ran": true,
  "status": "ran",
  "exitCode": 0,
  "timestamp": "2026-02-05T23:49:08.300Z",
  "output": "cspx schema=0.1 status=pass exit_code=0 checks=typecheck:pass"
}
```

`cspx-result.json`（抜粋）:
```json
{
  "schema_version": "0.1",
  "tool": { "name": "cspx", "version": "0.1.0" },
  "status": "pass",
  "exit_code": 0,
  "checks": [
    { "name": "typecheck", "status": "pass" }
  ]
}
```

Assertions の結果例（STOP のため意図通り fail）:
- `spec/csp/cspx-smoke.cspm` は `SYSTEM = STOP` を定義しています（deadlock 状態）。
- `--mode assertions` は `deadlock free` を評価するため、`resultStatus: fail` と `deadlock` タグ付き counterexample を返します。

参照先（cspx）:
- https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md
- https://github.com/itdojp/cspx/blob/main/docs/result-json.md
- https://github.com/itdojp/cspx/blob/main/docs/explainability.md
- https://github.com/itdojp/cspx/blob/main/docs/validation-report.md
