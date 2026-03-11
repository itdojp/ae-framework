---
docRole: ssot
lastVerified: '2026-03-11'
owner: architecture-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# ae-framework Current System Overview (2026-03)

> Language / 言語: English | 日本語

---

## English (Summary)

This document captures the implementation-aligned architecture of `ae-framework` as of 2026-03-03, including review-topology aware policy gates, Codex autopilot orchestration, trace-required check integration, release verify operations, and the expanded formal-verification stack with CSP (`cspx`) integration.

---

## 日本語

## 1. この資料の目的と適用範囲

本資料は、`ae-framework` の現行実装をベースに、以下を短時間で把握するための全体構成ドキュメントです。

- 主要レイヤ（CLI/CI/仕様検証/成果物）
- PR自動化レーン（review gate / auto-fix / autopilot / auto-merge）の責務分割
- 拡張済み形式検証スタック（Alloy/TLA/SMT/Apalache/Kani/SPIN/CSP/Lean4）
- `cspx` 連携の契約（summary/result artifact）
- 運用導線（ローカル実行、PRラベル実行、集約確認）

本資料での位置付けは、ae-framework を **assurance control plane** として説明することです。個々の coding agent、テストランナー、formal tool は producer であり、ae-framework の中核価値は次を束ねる制御面にあります。

- spec / contract の固定
- verification lane の起動と集約
- artifact validation
- policy / review / merge gate
- PR / release の判断材料の標準化

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

### 2.1 producer と control plane の分離

| 区分 | 主な要素 | 役割 |
| --- | --- | --- |
| Producer | coding agent, AE-Spec compiler, unit/integration tests, formal runners, conformance tools | 仕様・コード・検証結果を生成する |
| Control plane | Context Pack, artifact schemas, verify-lite summary, policy gate, change package, PR automation | 生成結果を contract と gate の観点で集約し、判断可能な証跡へ変換する |

設計上の含意:
- codegen は producer の一つであり、repo の SSOT は spec / contract / artifact に置く
- heavy verification は常時 mandatory ではなく、risk/profile に応じて昇格させる
- review / release の説明責任は raw log ではなく summary artifact に寄せる

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
| 必須ポリシーゲート | `policy-gate.yml` | risk/topology/approval 方針の判定（team/solo 切替対応、required checks評価） |
| レビューゲート | `copilot-review-gate.yml` | Copilotレビュー存在 + スレッド解決確認 |
| レビュー対応（auto-fix） | `copilot-auto-fix.yml` | Copilot suggestion をPRへ自動適用（コミット/push）+ スレッド解決（任意） |
| touchless運用レーン | `codex-autopilot-lane.yml` | `autopilot:on` PRの収束ループ（update-branch / auto-fix / gate再実行 / auto-merge試行） |
| 自動マージ（auto-merge） | `pr-ci-status-comment.yml` | 条件成立時に auto-merge を自動有効化し、人手マージを省略（任意） |
| トレース適合性 | `spec-generate-model.yml` | KvOnce trace conformance と `KvOnce Trace Validation` check を出力 |
| 形式検証（opt-in） | `formal-verify.yml` | `run-formal` ラベル/dispatchで重い検証を実行 |
| 形式集約 | `formal-aggregate.yml` | formal出力をPRコメント向けに集約 |
| セキュリティ | `security.yml`, `sbom-generation.yml` | 依存・脆弱性・SBOM運用 |
| リリース検証 | `post-deploy-verify.yml` | workflow_dispatch 起点の post-deploy verify と証跡保存 |

補足:
- `formal-verify.yml` は non-blocking 設計。必要時のみ `enforce-formal` で Apalache の `ran/ok` をゲート化。
- `policy-gate.yml` の approval 評価は `AE_REVIEW_TOPOLOGY` / `AE_POLICY_MIN_HUMAN_APPROVALS` で切替可能。
- `policy-gate.yml` は `policy/risk-policy.yml` の `required_checks` を常時評価し、`gate_checks` は high-risk 判定時に評価します。`run-trace` に紐づく `trace-conformance` / `KvOnce Trace Validation` も high-risk 条件を満たした場合のみゲート対象です。
- `codex-autopilot-lane.yml` は non-suggestion 指摘を fail-closed で扱い、`AE_AUTOPILOT_ACTIONABLE_COMMAND` 設定時のみ自動処理へ進みます。

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
| Policy Gate要約 | `artifacts/ci/policy-gate-summary.json`, `artifacts/ci/policy-gate-summary.md` |
| Autopilot契約成果物 | `artifacts/ci/pr-state-v1.json`, `artifacts/ci/execution-plan-v1.json` |
| Risk label要約 | `artifacts/ci/risk-labeler-summary.json`, `artifacts/ci/risk-labeler-summary.md` |
| Trace検証成果物 | `artifacts/kvonce-trace-summary.json`, `artifacts/kvonce-trace-envelope.json`, `artifacts/automation/kvonce-trace-validation-report.json` |

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
   - `verify-lite` / `policy-gate` / `gate` の required checks を green にする
   - `autopilot:on` を使う場合は `AE_CODEX_AUTOPILOT_ENABLED=1` と必要変数を設定し、`<!-- AE-CODEX-AUTOPILOT v1 -->` コメントで停止理由を確認
5. 追加検証（必要時）:
   - `run-formal` ラベルで重い形式検証を実行
   - `run-trace` ラベルで trace 連動の gate 条件を満たす
6. リリース運用:
   - `gh workflow run post-deploy-verify.yml ...` で post-deploy verify を実行
   - `artifacts/release/post-deploy-verify.json` を判定証跡として保管

## 8. 関連ドキュメント

- 製品概要: `docs/product/OVERVIEW.md`
- Assurance control plane の位置付け: `docs/product/ASSURANCE-CONTROL-PLANE.md`
- 詳細説明: `docs/product/DETAIL.md`
- 利用手順: `docs/product/USER-MANUAL.md`
- Assurance model: `docs/quality/ASSURANCE-MODEL.md`
- PR自動化運用: `docs/ci/pr-automation.md`
- リリース運用: `docs/operate/release-engineering.md`
- Formal運用: `docs/quality/formal-runbook.md`
- CSP詳細: `docs/quality/formal-csp.md`
- 全ドキュメント索引: `docs/README.md`

## 9. 更新サマリ（2026-03-03）

更新内容:
- `codex-autopilot-lane.yml` の収束フロー（actionable非suggestion対応を含む）を CIモデルへ統合
- `policy/risk-policy.yml` の trace-required 条件（`run-trace` + gate_checks）を明示
- 主要成果物に policy/risk/trace の実運用ファイルを追加
- PR運用導線を required checks 起点に更新

一次情報（実装ソース）:
- `.github/workflows/policy-gate.yml`
- `.github/workflows/codex-autopilot-lane.yml`
- `.github/workflows/spec-generate-model.yml`
- `policy/risk-policy.yml`
- `scripts/ci/codex-autopilot-lane.mjs`
- `.github/workflows/post-deploy-verify.yml`
- `scripts/ci/lib/automation-config.mjs`
- `src/cli/release-cli.ts`
