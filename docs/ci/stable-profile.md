---
docRole: ssot
lastVerified: '2026-03-25'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Stable CI Test Profile

> Language / 言語: English | 日本語

---

## English

This profile defines the deterministic and relatively fast test subset used as the baseline signal for pull request verification. Heavy or flaky suites remain behind labels or scheduled workflows so the required PR checks stay stable.

### Purpose

- keep PR-blocking feedback fast and reproducible
- separate required baseline signal from opt-in or scheduled heavy validation
- provide a common fallback when operators need to re-establish a green baseline before escalating to heavier suites

### Commands

- Full CI config: `pnpm run test:ci`
- Stable Vitest subset: `pnpm run test:ci:stable`
- Verify Lite equivalent (`types:check` / lint / build / conformance): `pnpm run test:ci:lite`
- Extended pipeline (integration / property / MBT / pact / mutation quick): `pnpm run test:ci:extended`

`test:ci:stable` currently excludes:
- `**/system-integration.test.ts`

### Workflow mapping

- Verify Lite (`.github/workflows/verify-lite.yml`) uses `test:ci:lite` to keep the required baseline fast.
- Heavy suites run from `.github/workflows/ci-extended.yml` and are typically enabled by labels such as `run-ci-extended`, `run-integration`, `run-property`, `run-mbt`, and `run-mutation`, or by scheduled runs.
- When a PR needs higher confidence without opening the full heavy lane, operators can still run targeted suites such as `test:unit`, `test:int`, `test:a11y`, or `test:coverage`.
- Playwright / E2E coverage stays label-gated (`run-e2e`) or scheduled so it does not destabilize the default PR baseline.

### Flake diagnostics

- When re-running integration-heavy failures, set `AE_INTEGRATION_TRACE_HANDLES=1` to collect `why-is-node-running` diagnostics.
- In GitHub Actions, re-run only the failed jobs with `gh run rerun <runId> --failed` to confirm reproducibility on the same CI context.
- For handle-level diagnostics, reproduce locally with `AE_INTEGRATION_TRACE_HANDLES=1 pnpm test:int`, because `gh run rerun` does not accept environment-variable overrides.
- After collecting diagnostics, remove the variable to avoid excessive logs and unnecessary CI cost.
- Detailed procedures live in `docs/testing/integration-runtime-helpers.md`.

### Evolution policy

- Newly identified flaky suites should be stabilized first.
- If immediate stabilization is not practical, move them to label-gated or scheduled execution until the root cause is fixed.
- Required PR checks should continue to reflect the stable baseline, not the temporary location of unstable suites.

## 日本語

このプロファイルは、pull request 検証の baseline signal として使う、決定的かつ比較的高速なテスト subset を定義します。重い suite や flaky な suite は、required PR checks の安定性を保つため、ラベルや scheduled workflow の後段へ退避します。

### 目的

- PR を block する feedback を高速かつ再現可能に保つ
- required baseline signal と、opt-in / scheduled の重い検証を分離する
- operator がまず green baseline を回復し、その後に重い suite へ escalation できる共通 fallback を提供する

### コマンド

- Full CI 構成: `pnpm run test:ci`
- 安定 Vitest subset: `pnpm run test:ci:stable`
- Verify Lite 相当（`types:check` / lint / build / conformance）: `pnpm run test:ci:lite`
- Extended pipeline（integration / property / MBT / pact / mutation quick）: `pnpm run test:ci:extended`

`test:ci:stable` は現在、以下を除外します。
- `**/system-integration.test.ts`

### Workflow 対応

- Verify Lite（`.github/workflows/verify-lite.yml`）は required baseline を高速に保つため `test:ci:lite` を使用します。
- 重い suite は `.github/workflows/ci-extended.yml` から実行し、通常は `run-ci-extended`、`run-integration`、`run-property`、`run-mbt`、`run-mutation` などの label、または scheduled run で有効化します。
- full heavy lane を開かずに confidence を上げたい場合は、`test:unit`、`test:int`、`test:a11y`、`test:coverage` などの targeted suite を選択します。
- Playwright / E2E coverage は、default の PR baseline を不安定化させないため、`run-e2e` label または scheduled 実行に留めます。

### Flake 診断

- integration 系の再実行でハンドルリーク等を調べる場合は、`AE_INTEGRATION_TRACE_HANDLES=1` を付けて `why-is-node-running` 診断を収集します。
- GitHub Actions では、同じ CI 文脈で再現性を確認するため、失敗 job だけを `gh run rerun <runId> --failed` で再実行します。
- ハンドルレベルの診断が必要な場合は、`gh run rerun` では環境変数 override ができないため、ローカルで `AE_INTEGRATION_TRACE_HANDLES=1 pnpm test:int` を実行します。
- 診断後はログ肥大と CI コスト増を避けるため、必ず環境変数を外します。
- 詳細手順は `docs/testing/integration-runtime-helpers.md` を参照します。

### Evolution 方針

- 新たに flaky と判明した suite は、まず安定化を優先します。
- 直ちに安定化できない場合のみ、根本原因が解消するまで label-gated または scheduled 実行へ移します。
- required PR checks は、一時的な退避先ではなく、常に stable baseline を表すよう維持します。
