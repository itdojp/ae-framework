---
docRole: derived
canonicalSource:
- docs/quality/ASSURANCE-MODEL.md
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
lastVerified: '2026-03-22'
---
# Assurance Control Plane

> Language / 言語: English | 日本語

---

## English

## 1. Definition
This document defines ae-framework as an assurance control plane that sits on top of BYO agents and verification tools.

Here, “control plane” means the layer that keeps the following under a consistent contract:
- specification
- verification
- evidence artifacts
- policy / PR gate / merge automation
- release / post-deploy judgment

## 2. Where the value actually comes from
The center of value is not an isolated code-generation feature. In the current implementation, the practical value comes from:

1. fixing specifications and contracts through Context Pack and schemas
2. aggregating `verify-lite`, formal runners, and conformance outputs into summaries
3. detecting breakage through artifact validation and the Contract Catalog
4. operating `policy-gate`, `gate`, auto-fix, and auto-merge with explicit control
5. retaining PR / release evidence in JSON and Markdown

## 3. What ae-framework is / is not

### 3.1 What it is
- an agentic SDLC orchestrator
- a control plane for specification / verification / evidence / policy gates
- an operating model that can strengthen assurance only for selected high-risk changes

### 3.2 What it is not
- a single-model-dependent code generator
- an agent runtime or IDE plugin
- a mandatory framework that requires formal proof on every change

## 4. Producer vs. control-plane responsibilities

| Category | Examples | Primary responsibility |
| --- | --- | --- |
| Producer | coding agents, test runners, TLA/Alloy/SMT/CSP/Lean tools | generate code, specifications, and raw verification results |
| Assurance control plane | Context Pack, verify-lite, formal aggregate, policy gate, change package | collect outputs, validate contracts, and convert results into judgment artifacts |

Because of this separation, teams can replace the underlying agents or solvers while keeping the judgment-side contracts stable.

### 4.1 Two-layer model

```text
Harness layer
- lint / test / hooks
- E2E / adapters / runners

Assurance control plane
- Context Pack / evidence aggregation
- policy / PR gate / release judgment
```

- The Harness layer executes checks and produces raw outputs.
- The Assurance control plane converts those outputs into contract-bound artifacts that can be reviewed and judged.
- The differentiator of ae-framework is not the individual harness feature, but the ability to keep the judgment-side contract stable.

## 5. Rollout profiles

### Baseline
- `verify-lite`
- schema / AJV validation
- `policy-gate` and `gate`
- report-only aggregation through `quality-scorecard`
- role: stabilize the minimum Harness layer

### Structured assurance
- Context Pack
- property / MBT / conformance
- `assurance-summary`
- `hook-feedback` / `ae-handoff`
- organized change evidence
- role: connect specifications and verification evidence into the control plane

### High-assurance critical core
- formal / model / proof lanes
- stricter policy-gate operation
- proof-carrying change package
- role: strengthen the control plane only for selected high-risk changes

## 6. Mapping to the current implementation

Control-plane elements that already exist today:
- `docs/spec/context-pack.md`
- `spec/context-pack/boundary-map.json`
- `schema/*.schema.json`
- `scripts/context-pack/verify-boundary-map.mjs`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/assurance/assurance-summary.json`
- `artifacts/quality/quality-scorecard.json`
- `artifacts/agents/hook-feedback.json`
- `artifacts/handoff/ae-handoff.json`
- `artifacts/formal/formal-summary-v1.json`
- `artifacts/hermetic-reports/formal/summary.json`
- `artifacts/ci/policy-gate-summary.json`
- `artifacts/ci/policy-decision-js-v1.json`, `artifacts/ci/policy-decision-opa-v1.json`
- `artifacts/ci/automation-report.json`
- `docs/ci/pr-automation.md`

Conditional or preview elements:
- strict assurance enforcement (only when the `enforce-assurance` label is set)
- proof-carrying change package v2
- opt-in heavy lanes such as formal / trace / security

## 7. What matters on the judgment side
- being able to explain what is guaranteed and what remains unverified is more important than a raw green build alone
- review and release decisions should center on summary artifacts, not raw logs
- heavy verification should be required only for high-risk changes, while normal lanes stay fast

---

## 日本語

## 1. 定義

本資料では、ae-framework を **BYO-agent の上に載る assurance control plane** と定義します。

ここでいう control plane とは、次を一貫した契約で束ねる層です。

- specification
- verification
- evidence artifacts
- policy / PR gate / merge automation
- release / post-deploy judgment

## 2. 何が価値の中心か

価値の中心は、個別の codegen 機能ではありません。現在の実装で価値が出ているのは次です。

1. Context Pack や schema による spec/contracts の固定
2. `pnpm run verify:lite`、formal runners、conformance の summary 化
3. artifact validation と Contract Catalog による破壊検知
4. `policy-gate` / `gate` / auto-fix / auto-merge の運用制御
5. PR / release に必要な証跡を JSON/Markdown で残すこと

## 3. What ae-framework is / is not

### 3.1 What it is
- agentic SDLC orchestrator
- spec / verification / evidence / policy gate の control plane
- high-risk 変更だけ assurance を強化できる運用基盤

### 3.2 What it is not
- 単一モデル依存のコード生成器
- agent runtime や IDE plugin
- すべての変更に formal proof を要求する強制フレームワーク

## 4. producer と control plane の役割分担

| 区分 | 例 | 主責務 |
| --- | --- | --- |
| Producer | coding agent, test runner, TLA/Alloy/SMT/CSP/Lean ツール | コード、仕様、検証結果を生成する |
| Assurance control plane | Context Pack, verify-lite, formal aggregate, policy gate, change package | 結果を収集し、契約検証し、判断用 artifact に変換する |

この分離により、基礎となる agent や solver が変わっても、判断面の契約を継続利用できます。

### 4.1 二層モデル

```mermaid
flowchart TB
  subgraph H[Harness layer]
    H1[lint / test / hooks]
    H2[E2E / adapters / runners]
  end
  subgraph C[Assurance control plane]
    C1[Context Pack / evidence aggregation]
    C2[policy / PR gate / release judgment]
  end
  H --> C
```

- Harness layer は「実行して結果を出す層」です。
- Assurance control plane は「結果を契約化し、判断可能な artifact に変換する層」です。
- ae-framework の差別化は前者の個別機能ではなく、後者の判断面契約を固定できる点にあります。

## 5. 導入プロファイル

### Baseline
- `verify-lite`
- schema/AJV validation
- `policy-gate` と `gate`
- `quality-scorecard` の report-only 集約
- 役割: harness layer の最小安定化

### Structured assurance
- Context Pack
- property / MBT / conformance
- `assurance-summary`
- `hook-feedback` / `ae-handoff`
- change evidence の整理
- 役割: control plane に仕様と検証の対応を供給

### High-assurance critical core
- formal/model/proof lane
- strict policy gate
- proof-carrying change package
- 役割: selected high-risk change に限定して control plane を強化

## 6. 現行実装との対応

現時点で既に存在する control plane 要素:
- `docs/spec/context-pack.md`
- `spec/context-pack/boundary-map.json`
- `schema/*.schema.json`
- `scripts/context-pack/verify-boundary-map.mjs`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/assurance/assurance-summary.json`
- `artifacts/quality/quality-scorecard.json`
- `artifacts/agents/hook-feedback.json`
- `artifacts/handoff/ae-handoff.json`
- `artifacts/formal/formal-summary-v1.json`
- `artifacts/hermetic-reports/formal/summary.json`（formal aggregate）
- `artifacts/ci/policy-gate-summary.json`
- `artifacts/ci/policy-decision-js-v1.json`, `artifacts/ci/policy-decision-opa-v1.json`
- `artifacts/ci/automation-report.json`
- `docs/ci/pr-automation.md`

条件付きまたは preview 扱いの要素:
- strict assurance enforcement（`enforce-assurance` ラベル時のみ）
- proof-carrying change package v2
- formal / trace / security などの opt-in heavy lane

## 7. 判断面で重視すること

- green build であることより、何が保証され何が未保証かを説明できること
- raw log ではなく summary artifact を review/release 判断の中心に置くこと
- high-risk change にだけ重い検証を要求し、通常 lane の速度を維持すること
