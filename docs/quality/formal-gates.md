---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- policy/risk-policy.yml
lastVerified: '2026-04-14'
---
# Formal Quality Gates (v0.2 DoD)

> 🌍 Language / 言語: English | 日本語

---

## English

This document defines the formal verification gates used in CI for the current v0.2 baseline.

### Objectives

- Confirm conformance between runtime traces and formal specifications.
- Run lightweight temporal verification with Alloy 6.
- Run TLA+ verification through TLC or Apalache when the corresponding engine is available.
- Run redundant SMT checks with `z3` or `cvc5`.
- Preserve the counterexample -> failing test -> minimal fix workflow.

### Current CI entry points

- `verify:conformance (stub)`
- `verify:alloy (stub)`
- `verify:tla (stub)`
- `verify:smt (stub)`
- `verify:apalache (stub)`
- `verify:kani (presence)`
- `verify:spin (Promela)`
- `verify:csp`
- `verify:lean (Lean4)`
- `Formal Reports Aggregate`

These jobs are wired through `.github/workflows/formal-verify.yml` and, for non-fork PRs, start only when the PR has the `run-formal` label. For fork PRs, a maintainer must use `workflow_dispatch` with the matching `target`.

### Blocking vs report-only behavior

- The formal lane is opt-in and report-only by default.
- Adding `enforce-formal` makes the strict path enforce the Apalache `ran/ok` result and the formal summary validation in the aggregate step.
- `verify-lite` can also collect formal outputs when `run-formal` is present, but the default required baseline remains `verify-lite`, `policy-gate`, and `gate`.

### Workflow

1. Add `run-formal` to the PR, or dispatch `Formal Verify` manually.
2. Confirm the per-tool summaries under `artifacts/hermetic-reports/formal/`.
3. If a property fails, capture the counterexample and convert it into a failing test.
4. Apply the smallest fix that returns the formal lane to green.

### Artifacts to review

- `artifacts/hermetic-reports/formal/summary.json`
- `artifacts/formal/formal-summary-v1.json`
- `artifacts/formal/formal-summary-v2.json`
- per-tool summaries such as:
  - `artifacts/hermetic-reports/formal/apalache-summary.json`
  - `artifacts/hermetic-reports/formal/tla-summary.json`
  - `artifacts/hermetic-reports/formal/smt-summary.json`
  - `artifacts/hermetic-reports/formal/alloy-summary.json`

### Current status

- v0.2 keeps the formal lane available but opt-in on PRs.
- Several jobs still operate as stubs or presence checks while the repository incrementally wires real engines and stricter evidence handling.
- The canonical operational detail lives in `docs/quality/formal-runbook.md`; use this document as the policy-level overview.

## 日本語

この文書は、現行 v0.2 ベースラインで CI に導入している形式検証ゲートの定義をまとめたものです。

### 目的

- 実行トレースと形式仕様の適合性を確認する。
- Alloy 6 による軽量時相検証を行う。
- 利用可能な場合は TLC / Apalache を通じて TLA+ 検証を行う。
- `z3` / `cvc5` による冗長 SMT チェックを行う。
- 失敗 -> 反例 -> 失敗テスト -> 最小修正、という運用フローを維持する。

### 現在の CI 起点

- `verify:conformance (stub)`
- `verify:alloy (stub)`
- `verify:tla (stub)`
- `verify:smt (stub)`
- `verify:apalache (stub)`
- `verify:kani (presence)`
- `verify:spin (Promela)`
- `verify:csp`
- `verify:lean (Lean4)`
- `Formal Reports Aggregate`

これらのジョブは `.github/workflows/formal-verify.yml` に実装されており、fork されていない PR では `run-formal` ラベルが付いた場合にのみ起動します。fork PR ではメンテナーが `workflow_dispatch` を使い、`target` で対象を選択する必要があります。

### ブロッキングと報告専用（report-only）の扱い

- 形式検証レーンはオプトインで、既定では報告専用（report-only）です。
- `enforce-formal` を付けると、厳格パス（strict path）で Apalache の `ran/ok` と集約ステップ（aggregate step）の formal summary 検証を強制します。
- `run-formal` がある場合は `verify-lite` でも formal 出力を収集できますが、既定の必須ベースラインは引き続き `verify-lite` / `policy-gate` / `gate` です。

### 運用フロー

1. PR に `run-formal` を付与するか、`Formal Verify` を手動起動する。
2. `artifacts/hermetic-reports/formal/` 配下の各ツールのサマリーを確認する。
3. 性質が失敗した場合は反例を採取し、失敗テストに落とし込む。
4. 形式検証レーンを green に戻す最小修正を適用する。

### 確認する成果物

- `artifacts/hermetic-reports/formal/summary.json`
- `artifacts/formal/formal-summary-v1.json`
- `artifacts/formal/formal-summary-v2.json`
- 各ツールのサマリ例:
  - `artifacts/hermetic-reports/formal/apalache-summary.json`
  - `artifacts/hermetic-reports/formal/tla-summary.json`
  - `artifacts/hermetic-reports/formal/smt-summary.json`
  - `artifacts/hermetic-reports/formal/alloy-summary.json`

### 現状

- v0.2 では形式検証レーンを PR 上でオプトインのまま維持しています。
- リポジトリでは実エンジンと、より厳格な証跡処理を段階的に接続しており、スタブ / presence check のジョブもまだ含まれます。
- 正式な運用詳細は `docs/quality/formal-runbook.md` にあるため、この文書はポリシーレベルの概要として扱ってください。
