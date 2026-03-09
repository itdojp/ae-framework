---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- policy/risk-policy.yml
lastVerified: '2026-03-10'
---
# Formal Quality Gates (v0.2 DoD)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

v0.2 で CI に導入するフォーマル検証ゲートの定義です。
- 適合性チェック（トレース vs 仕様）
- Alloy 6 による軽量時相検証、TLA+（TLC/Apalache）による検証
- SMT ソルバの冗長化（Z3/cvc5）
- 失敗→反例→テスト化→最小修正→緑化、というワークフロー

詳細は英語セクションの対象/ワークフロー/アーティファクト項を参照してください。

## English

This document defines v0.2 formal verification gates in CI.

Objectives
- Conformance between runtime traces and formal specs
- Lightweight temporal verification via Alloy 6 (LTL + past)
- TLA+ via TLC/Apalache (SMT/BMC + inductive invariants)
- Redundant SMT solving (Z3/cvc5)

CI Targets (green = pass)
- verify:conformance — trace vs spec
- verify:alloy — temporal properties
- verify:tla --engine=apalache|tlc — model checking
- verify:smt --solver=z3|cvc5 — redundancy

Workflow
1) Failing property → counterexample
2) Counterexample → failing test under `tests/`
3) Minimal fix until all gates green

Artifacts
- Trace schema: `observability/trace-schema.yaml`
- Reports: `artifacts/hermetic-reports/conformance/`

Status
- v0.2: establish stubs in CI and wire engines incrementally

This document defines the formal verification gates that must pass in CI for v0.2.

Objectives
- Conformance checking between runtime traces and formal specs
- Lightweight temporal verification via Alloy 6 (LTL + past operators)
- TLA+ verification via TLC and Apalache (SMT/BMC + inductive invariants)
- Redundant SMT solving with Z3 and cvc5

CI Targets (green = pass)
- verify:conformance — trace vs spec conformance
- verify:alloy — Alloy 6 temporal properties
- verify:tla --engine=apalache|tlc — TLA+ model checking
- verify:smt --solver=z3|cvc5 — solver redundancy

Workflow
1) Failing property yields a counterexample
2) Counterexample becomes a failing test under tests/
3) Apply minimal fix until all gates return green

Artifacts
- Trace schema: observability/trace-schema.yaml
- Reports: artifacts/hermetic-reports/conformance/

Status
- v0.2: Establish gates as stubs in CI; incrementally wire real engines
