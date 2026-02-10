# ae-framework Current System Overview (2026-02)

> Language / 言語: English | 日本語

---

## English (Summary)

This document captures the implementation-aligned architecture of `ae-framework` as of 2026-02-09, including the expanded formal-verification stack and CSP (`cspx`) integration contract.

---

## 日本語

## 1. この資料の目的と適用範囲

本資料は、`ae-framework` の現行実装をベースに、以下を短時間で把握するための全体構成ドキュメントです。

- 主要レイヤ（CLI/CI/仕様検証/成果物）
- 拡張済み形式検証スタック（Alloy/TLA/SMT/Apalache/Kani/SPIN/CSP/Lean4）
- `cspx` 連携の契約（summary/result artifact）
- 運用導線（ローカル実行、PRラベル実行、集約確認）

前提（根拠）:
- Node.js: `>=20.11 <23`（`package.json` `engines.node`）
- pnpm: `10.0.0`（`package.json` `packageManager`）
- CI: GitHub Actions（`.github/workflows/`）

## 2. レイヤ構成（実装準拠）

| レイヤ | 主構成 | 役割 |
| --- | --- | --- |
| 運用レイヤ | `.github/workflows/*`, `.github/actions/*` | PRゲート、ラベル/dispatch実行、成果物集約 |
| 実行レイヤ | `src/cli/*`, `package.json` scripts/bin, `scripts/*` | 開発者/エージェントが使う実行面 |
| 仕様・検証レイヤ | `spec/*`, `scripts/formal/*`, `tests/*` | 仕様検証、形式検証、テスト |
| 成果物レイヤ | `artifacts/*`, `reports/*` | CI/ローカル結果、集約JSON/Markdown |
| ドキュメントレイヤ | `docs/*` | 運用手順、契約、アーキテクチャ説明 |

## 3. 実行インタフェース

### 3.1 主要CLI（`package.json` `bin`）

- `ae`, `ae-framework`（メインCLI）
- `ae-phase`, `ae-approve`, `ae-slash`
- `ae-ui`, `ae-sbom`, `ae-resilience`, `ae-benchmark`, `ae-server`

### 3.2 形式検証の主要コマンド

- 統合実行: `pnpm run verify:formal`
- 個別実行:
  - `pnpm run verify:conformance`
  - `pnpm run verify:alloy`
  - `pnpm run verify:tla -- --engine=tlc|apalache`
  - `pnpm run verify:smt -- --solver=z3|cvc5 --file spec/smt/sample.smt2`
  - `node scripts/formal/verify-apalache.mjs --file spec/tla/DomainSpec.tla`
  - `pnpm run verify:kani`
  - `pnpm run verify:spin -- --file spec/spin/sample.pml --ltl p_done`
  - `pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck`
  - `pnpm run verify:lean`
- 集約: `pnpm run formal:summary`
- ツール検出: `pnpm run tools:formal:check`

### 3.3 MCPサーバ実装

`src/mcp-server/`:
- `intent-server.ts`
- `formal-server.ts`
- `test-generation-server.ts`
- `code-generation-server.ts`
- `verify-server.ts`
- `operate-server.ts`
- `container-server.ts`
- `tdd-server.ts`
- `spec-synthesis-server.ts`

## 4. CI実行モデル（推奨運用）

| 種別 | 代表ワークフロー | 目的 |
| --- | --- | --- |
| 必須軽量ゲート | `verify-lite.yml`, `coverage-check.yml`, `workflow-lint.yml` | 日常PRの安定ゲート |
| レビューゲート | `copilot-review-gate.yml` | Copilotレビュー存在 + スレッド解決確認 |
| レビュー対応（auto-fix） | `copilot-auto-fix.yml` | Copilot suggestion をPRへ自動適用（コミット/push）+ スレッド解決（任意） |
| 自動マージ（auto-merge） | `pr-ci-status-comment.yml` | 条件成立時に auto-merge を自動有効化し、人手マージを省略（任意） |
| 形式検証（opt-in） | `formal-verify.yml` | `run-formal` ラベル/dispatchで重い検証を実行 |
| 形式集約 | `formal-aggregate.yml` | formal出力をPRコメント向けに集約 |
| セキュリティ | `security.yml`, `sbom-generation.yml` | 依存・脆弱性・SBOM運用 |

補足:
- `formal-verify.yml` は non-blocking 設計。必要時のみ `enforce-formal` で Apalache の `ran/ok` をゲート化。

## 5. 形式検証スタック（拡張後）

### 5.1 共通方針

- 各ランナーは summary JSON を出力し、コマンド自体は non-blocking（終了コード `0`）で運用可能。
- 判定は summary の `status` / `resultStatus` / `ok` / `exitCode` を上位ゲートで解釈。

### 5.2 CSP (`cspx`) 連携契約

`verify:csp`（`scripts/formal/verify-csp.mjs`）のバックエンド選択順:
1. `CSP_RUN_CMD`
2. `cspx`
3. `refines` (FDR)
4. `cspmchecker`

`cspx` 利用時の固定成果物:
- `artifacts/hermetic-reports/formal/csp-summary.json`
- `artifacts/hermetic-reports/formal/cspx-result.json`

互換前提:
- `schema_version=0.1` を期待
- 非互換時は `status=unsupported` を返却
- `metrics` は optional（必須項目中心で解釈）

CI pin（再現性）:
- `.github/workflows/formal-verify.yml` の `CSPX_REF=8a67639ea4d3f715e27feb8cd728f46866a905db`

### 5.3 集約表示

`formal-aggregate.yml` は CSP について以下を表示:
- `backend`
- `status`
- `resultStatus`
- `exitCode`

## 6. 主要成果物（運用で最初に見るファイル）

| 用途 | 代表ファイル |
| --- | --- |
| 形式検証の総覧 | `artifacts/hermetic-reports/formal/summary.json` |
| Conformance要約 | `artifacts/hermetic-reports/conformance/summary.json` |
| CSP要約 | `artifacts/hermetic-reports/formal/csp-summary.json` |
| CSP詳細 | `artifacts/hermetic-reports/formal/cspx-result.json` |
| Apalache要約 | `artifacts/hermetic-reports/formal/apalache-summary.json` |
| PR向け形式集約 | `artifacts/formal/formal-aggregate.json`, `artifacts/formal/formal-aggregate.md` |

## 7. 運用開始の最短導線

1. ローカル最小確認:
   - `pnpm install`
   - `pnpm run lint`
   - `pnpm run test:fast`
2. 形式系の導入確認:
   - `pnpm run tools:formal:check`
   - `pnpm run verify:formal`
3. CSP拡張確認:
   - `pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck`
   - `artifacts/hermetic-reports/formal/csp-summary.json` を確認
4. PR運用:
   - 必要時に `run-formal` ラベルを付与
   - 集約結果を PR コメントと artifacts で確認

## 8. 関連ドキュメント

- 製品概要: `docs/product/OVERVIEW.md`
- 詳細説明: `docs/product/DETAIL.md`
- 利用手順: `docs/product/USER-MANUAL.md`
- Formal運用: `docs/quality/formal-runbook.md`
- CSP詳細: `docs/quality/formal-csp.md`
- 全ドキュメント索引: `docs/README.md`
