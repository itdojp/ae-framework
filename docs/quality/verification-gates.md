---
docRole: derived
canonicalSource:
- policy/risk-policy.yml
- policy/quality.json
lastVerified: '2026-03-10'
---
# Verification Gates Guide

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

Verification gates standardize **verify-then-merge**. This guide lists the available gate types, how to enable them, and where results are reported.

### Report metadata

Quality gate reports (`reports/quality-gates/quality-report-*.json`) include a `meta` object with run context (`runId`, `commitSha`, `branch`, `createdAt`, `agent`, `model`, `traceId`). Values are derived from CI/local environment variables when available and are optional beyond `runId`/`createdAt`.

---

## 日本語（概要）

検証ゲートは **verify-then-merge** を実現するための基準です。本ドキュメントではゲート種別・有効化方法・レポート出力先を整理します。

## ゲート種別

- 基本ゲート: lint / types / coverage
- 追加ゲート: property / pact-contract(API) / mutation / MBT / perf / a11y / lighthouse / heavy (CI Extended)
- Formal: TLA+ / Alloy / conformance (report-only → opt-in)

## 有効化の指針（既存運用のまとめ）

- PRデフォルトは軽量ゲート（Verify Lite）
- 重いゲートは **ラベルで opt-in** する
- しきい値系（perf/lh/a11y）は `enforce-*` ラベルでブロッキング化

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
| pact-contract(API) | `pnpm run pipelines:pact` | pact test logs/artifacts (project-defined) | API契約の検証（Pact） |
| mutation | label `run-mutation` | `reports/mutation/` | quick mode + ignoreStatic |
| MBT | label `run-mbt` | `artifacts/mbt/` | CI Extended 側 |
| perf/a11y/lh | label `enforce-perf` / `enforce-a11y` / `enforce-lh` | `reports/*.json` | しきい値でブロッキング |
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

- quality-gates レポート（`reports/quality-gates/quality-report-*.json`）には `meta` を付与
- 代表項目: `runId` / `commitSha` / `branch` / `createdAt` / `agent` / `model` / `traceId`
- 値はCI/ローカルの環境変数から取得し、存在するもののみ付与（`runId` と `createdAt` は常に付与）

## 注意（machine verifying machine）

- AIがコードとテストを同時に生成すると盲点が共有される
- Spec Kit / Blueprint に **対抗的なテスト設計** を明記し、人間が責任を持つ
- verify-then-merge は「**CI合格 + 人間承認**」が基本
