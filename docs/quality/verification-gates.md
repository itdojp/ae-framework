---
docRole: derived
canonicalSource:
- policy/risk-policy.yml
- policy/quality.json
lastVerified: '2026-03-23'
---
# Verification Gates Guide

> 🌍 Language / 言語: English | 日本語

---

## English

Verification gates standardize **verify-then-merge**. This document summarizes the current gate taxonomy, how heavier checks are enabled, how the word `contract` should be interpreted in gate names, and where operators should look for evidence.

### Gate categories

- Baseline gates: `types:check` / lint / build / conformance
- Additional gates: property / pact-contract (API) / mutation / MBT / perf / a11y / lighthouse / heavy (CI Extended)
- Formal gates: TLA+ / Alloy (report-only by default, opt-in for stricter execution)

### Enablement guidance (current operations)

- Daily PRs default to the lighter baseline in Verify Lite.
- Heavier gates are usually enabled through opt-in labels.
- Adapter-threshold checks such as perf / lighthouse / a11y are usually enabled through `run-adapters`; `enforce-*` labels only switch those checks from report-only to blocking.

Related documents:
- `docs/ci/label-gating.md`
- `docs/ci/stable-profile.md`
- `docs/quality/adapter-thresholds.md`
- `docs/quality/comparator.md`

### Contract taxonomy in this guide

- See `docs/quality/contract-taxonomy.md` for the canonical meaning split.
- `pact-contract (API)` in this guide refers to **API/Integration contract verification** such as Pact.
- DbC (Design contract: preconditions / postconditions / invariants) is covered through property tests, runtime conformance, and integration assertions rather than a single gate name.
- Artifacts contract means required/optional artifact obligations and is separate from API contract verification.

### Representative gates and entry points

| Gate | How to enable | Primary output | Notes |
| --- | --- | --- | --- |
| property | label `run-property` | `artifacts/properties/` | Executed from CI Extended lanes |
| pact-contract (API) | label `run-integration` or `run-ci-extended` | pact test logs/artifacts (project-defined) | Consumer-driven API contract verification in CI; `pnpm run pipelines:pact` remains the local/manual entrypoint |
| mutation | label `run-mutation` | `reports/mutation/` | quick mode with `ignoreStatic` |
| MBT | label `run-mbt` | `artifacts/mbt/` | Executed from CI Extended lanes |
| perf / a11y / lh | label `run-adapters` (optionally `enforce-perf` / `enforce-a11y` / `enforce-lh` to make blocking) | `reports/perf-results.json`, `reports/a11y-results.json`, `reports/lighthouse-results.json` (or `reports/lh-results.json`) | Adapter-threshold jobs run when `run-adapters` is present; `enforce-*` switches them from report-only to blocking |
| heavy tests | label `run-ci-extended` | `reports/heavy-test-trends.json` | Aggregate for integration / property / MBT / mutation |

#### What `contract` means in gate names

- `contract` in this guide means **API/Integration contract tests** such as Pact.
- DbC concerns are enforced through multiple mechanisms rather than a standalone `contract` gate.

#### Minimal DbC -> verification mapping

| DbC condition | Representative verification method | Representative evidence |
| --- | --- | --- |
| Preconditions | request validation / negative tests / type guards | `artifacts/verify-lite/verify-lite-run-summary.json` (see `docs/quality/ARTIFACTS-CONTRACT.md`) |
| Postconditions | state assertions / event assertions / integration tests | `reports/quality-gates/quality-report-*.json`, `artifacts/hermetic-reports/conformance/summary.json` |
| Invariants | property tests / runtime conformance monitors / DB constraints | `artifacts/properties/summary.json`, `artifacts/hermetic-reports/conformance/summary.json` |

### PR reporting

- Existing template: `docs/quality/pr-summary-template.md`
- Implementation detail: `docs/quality/pr-summary-tool.md`
- Operational goal: summarize verification results in a form that a human reviewer can judge without reopening every raw artifact.

### Report metadata

Quality gate reports (`reports/quality-gates/quality-report-*.json`) include a `meta` object for run-level metadata. That object may contain `runId`, `commitSha`, `branch`, `createdAt`, `agent`, `model`, and `traceId`. Values are taken from CI/local environment variables when available; only `runId` and `createdAt` are always populated.

### Operational caution

- When AI produces code and tests together, blind spots can overlap.
- Spec Kit / Blueprint documents should record adversarial test intent explicitly.
- The baseline remains **CI green plus human approval**, not machine-only approval.

---

## 日本語（概要）

検証ゲートは **verify-then-merge** を実現するための基準です。本ドキュメントではゲート種別・有効化方法・レポート出力先を整理します。

## ゲート種別

- 基本ゲート: `types:check` / lint / build / conformance
- 追加ゲート: property / pact-contract(API) / mutation / MBT / perf / a11y / lighthouse / heavy (CI Extended)
- Formal: TLA+ / Alloy（report-only → opt-in）

## 有効化の指針（既存運用のまとめ）

- PRデフォルトは軽量ゲート（Verify Lite）
- 重いゲートは **ラベルで opt-in** する
- adapter-threshold 系（perf/lh/a11y）は通常 `run-adapters` で有効化し、`enforce-*` ラベルで report-only から blocking に切り替える

関連ドキュメント:
- `docs/ci/label-gating.md`
- `docs/ci/stable-profile.md`
- `docs/quality/adapter-thresholds.md`
- `docs/quality/comparator.md`

## Contract taxonomy（意味の分離）

- 用語の基準は `docs/quality/contract-taxonomy.md` を参照
- 本ガイドの `pact-contract(API)` は **API/Integration contract（Pact）** を指す
- DbC（Design contract: pre/post/invariant）は、主に property / runtime conformance / integration assertion で担保する
- Artifacts contract は成果物の必須/任意ルールであり、API契約検証とは別概念

## 代表的なゲートと入口

| Gate | How to enable | Primary output | Notes |
| --- | --- | --- | --- |
| property | label `run-property` | `artifacts/properties/` | CI Extended 側で実行 |
| pact-contract(API) | label `run-integration` または `run-ci-extended` | pact test logs/artifacts (project-defined) | CI上の API 契約検証（Pact）。`pnpm run pipelines:pact` はローカル/手動入口 |
| mutation | label `run-mutation` | `reports/mutation/` | quick mode + ignoreStatic |
| MBT | label `run-mbt` | `artifacts/mbt/` | CI Extended 側 |
| perf/a11y/lh | label `run-adapters`（必要に応じて `enforce-perf` / `enforce-a11y` / `enforce-lh` で blocking 化） | `reports/perf-results.json`, `reports/a11y-results.json`, `reports/lighthouse-results.json`（または `reports/lh-results.json`） | adapter-threshold jobs は `run-adapters` で起動し、`enforce-*` は report-only から blocking への切替 |
| heavy tests | label `run-ci-extended` | `reports/heavy-test-trends.json` | integration/property/MBT/mutation の集約 |

### contract gate の意味（読み替え）

- 本ガイドの `contract` gate は **Pact等の API/Integration contract test** を指します。
- DbC（pre/post/invariant）は単独ゲート名ではなく、下記の複数手段で担保します。

### DbC -> 検証マッピング（最小）

| DbC条件 | 代表的な検証手段 | 代表的な証跡 |
| --- | --- | --- |
| Preconditions | request validation / negative tests / type guards | `artifacts/verify-lite/verify-lite-run-summary.json`（詳細は `docs/quality/ARTIFACTS-CONTRACT.md`） |
| Postconditions | state assertions / event assertions / integration tests | `reports/quality-gates/quality-report-*.json`, `artifacts/hermetic-reports/conformance/summary.json` |
| Invariants | property tests / runtime conformance monitors / DB constraints | `artifacts/properties/summary.json`, `artifacts/hermetic-reports/conformance/summary.json` |

## PRレポート

- 既存テンプレ: `docs/quality/pr-summary-template.md`
- 仕様: `docs/quality/pr-summary-tool.md`
- 目的: 検証結果を PR に要約して**人間が判断**できる形にする

## レポートメタ情報

- quality-gates レポート（`reports/quality-gates/quality-report-*.json`）には run-level metadata を表す `meta` object を付与
- 代表項目: `runId` / `commitSha` / `branch` / `createdAt` / `agent` / `model` / `traceId`
- 値はCI/ローカルの環境変数から取得し、存在するもののみ付与（`runId` と `createdAt` は常に付与）

## 注意（machine verifying machine）

- AIがコードとテストを同時に生成すると盲点が共有される
- Spec Kit / Blueprint に **対抗的なテスト設計** を明記し、人間が責任を持つ
- verify-then-merge は「**CI合格 + 人間承認**」が基本
