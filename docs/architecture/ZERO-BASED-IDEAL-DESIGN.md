---
docRole: derived
canonicalSource:
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
lastVerified: '2026-03-23'
---
# Zero-Based Ideal Design Blueprint (2026-03)

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document defines the ideal future shape of `ae-framework` if it were redesigned from zero while keeping the current business constraints explicit.

In scope:
- architecture: responsibility separation, state transitions, and contracts
- environment, language, and technology-stack re-selection
- operating models for solo, team, and enterprise usage

Out of scope:
- immediate full replacement of the current implementation
- patch-by-patch migration detail for every existing module

Assumptions as of 2026-03:
- the GitHub PR-driven delivery flow remains in place
- AI review, auto-fix, and gate decisions must stay auditable
- artifacts remain contractual evidence
- code generators are replaceable producers, while the assurance control plane stays centered on spec, verification, evidence, and policy gates

### 2. Zero-based design principles

1. Contract-first
   - Define every input and output with JSON Schema before implementation.
2. Deterministic by default
   - The same input should lead to the same judgement; avoid time, ordering, and randomness dependencies where possible.
3. Policy as code
   - Approval requirements, risk classification, and required-check selection stay declarative and machine-evaluable.
4. Observability as product
   - Failure taxonomy, recovery flow, and SLO/MTTR reporting are specified from the start.
5. Human override with trace
   - Human exceptions remain possible, but must always preserve a reason, deadline, and evidence link.
6. Assurance is claim-based
   - The system should explain what was assured through claims, levels, lanes, and evidence.

### 3. Ideal architecture (logical structure)

#### 3.1 Overall shape

The ideal design separates `ae-framework` into five planes:

- Control Plane
  - PR state machine, execution planning, retry, and convergence control
- Policy Plane
  - risk classification, required-check selection, and approval topology evaluation
- Execution Plane
  - AI review handling, code-change execution, and verification runner orchestration
- Evidence Plane
  - artifact generation, validation, storage, and traceability aggregation
- Observability Plane
  - audit logs, metrics, alerts, and operational reports

Even in the ideal shape, code generators and review AIs remain replaceable producers in the Execution Plane. The differentiated value stays in the Control, Policy, and Evidence planes, where PR and release assurance becomes standardized.

#### 3.2 Ideal component split

| Component | Primary responsibility | Contract |
| --- | --- | --- |
| `orchestrator` | Control PR-scoped state transitions | `pr-state.v1`, `execution-plan.v1` |
| `policy-engine` | Evaluate risk, approval, and required-check rules | `policy-input.v1`, `policy-decision.v1` |
| `action-engine` | Execute actionable findings and fix workflows | `review-task.v1`, `action-result.v1` |
| `evidence-broker` | Collect and validate evidence | `evidence-manifest.v1` |
| `gate-evaluator` | Produce final go/no-go judgements | `gate-evaluation.v1` |
| `ops-reporter` | Emit summaries, notifications, and recovery guidance | `ops-report.v1` |

#### 3.3 Ideal PR state machine

States:
- `draft`
- `ready_for_review`
- `review_feedback_pending`
- `action_execution`
- `gate_recheck`
- `merge_eligible`
- `blocked`
- `merged`

Key transitions:
- `ready_for_review -> review_feedback_pending` when AI review arrives
- `review_feedback_pending -> action_execution` when unresolved findings exist
- `action_execution -> gate_recheck` after a fix is applied
- `gate_recheck -> merge_eligible` when required gates are green
- any state -> `blocked` when a fail-closed condition is met

Every `blocked` state must emit:
- `blocked_reason`
- `unblock_actions[]`
- `owner_hint`

### 4. Ideal CI / automation topology

#### 4.1 Consolidate workflows into four lanes

1. `pr-core.yml` (Required)
   - policy gate, review gate, verify-lite, artifact validation
2. `pr-extended.yml` (Label opt-in)
   - heavy tests, full formal verification, deep security scans
3. `maintenance.yml` (Scheduled + dispatch)
   - reruns, branch sync, stale cleanup, trend analysis
4. `release-assurance.yml` (Dispatch)
   - release verify, rollback verify, post-deploy checks

#### 4.2 Fixed evaluation order

1. contract integrity (schema and artifact validation)
2. risk and approval policy
3. unresolved review state
4. auto-fix feasibility
5. required-check convergence
6. auto-merge eligibility

The ideal design fixes this order so workflow-by-workflow drift disappears.

### 5. Ideal contract model

#### 5.1 Contract layers

- input contracts
  - review comments, changed files, labels, workflow context
- decision contracts
  - risk decision, approval decision, gate decision
- evidence contracts
  - run summary, trace summary, formal summary, change package
- operation contracts
  - retry policy, backoff policy, escalation policy

#### 5.2 Compatibility policy

- every contract has `schema_version`
- backward compatibility is guaranteed only within the same major version
- major upgrades require a `dual-write` and `dual-validate` period

### 6. Technology-stack reconsideration

#### 6.1 Preferred stack (Ideal option A: Hybrid)

| Layer | Preferred choice | Reason |
| --- | --- | --- |
| Orchestrator / Policy runtime | Go 1.24 | single-binary distribution, concurrency, CI stability |
| CLI / adapter / schema tooling | TypeScript on Node.js 22 LTS with pnpm 10 | strong fit for GitHub API and JSON-heavy workflows |
| Heavy execution workers | Rust stable | CPU efficiency, memory safety, portable distribution |
| Policy DSL | Rego (OPA) | declarative policy evaluation and testability |
| Contract validation | JSON Schema 2020-12 + AJV | compatibility with the current repository assets |
| Event bus | NATS JetStream | low operational overhead with retry and ordering support |
| Metadata DB | PostgreSQL 16 | strong audit-query and relational consistency story |
| Artifact store | S3-compatible storage | long-term evidence retention and re-analysis |
| Cache | Redis 7 | idempotency keys and short-lived coordination state |
| Observability | OpenTelemetry + Prometheus + Loki + Tempo + Grafana | integrated logs, metrics, and traces |
| Packaging | OCI + distroless | reproducibility and smaller security surface |

#### 6.2 Execution-environment profiles

##### Solo
- GitHub Actions centric
- SQLite plus artifact files is acceptable instead of an external database
- OPA bundle can remain local

##### Team
- GitHub Actions plus a lightweight Go control plane
- PostgreSQL + S3 + Redis
- NATS for async job separation

##### Enterprise
- Kubernetes with HPA
- PostgreSQL HA and multi-AZ object storage
- multi-tenant policy bundles

#### 6.3 Alternative stack options

- Option B: TypeScript-only
  - easier to start, but likely higher long-term operational cost
- Option C: Rust-first
  - strongest performance and safety, but slower iteration and higher hiring cost

Preferred direction: option A (Hybrid).

### 7. Ideal repository structure

```text
/
  cmd/
    orchestrator/
    policy-engine/
    ops-reporter/
  packages/
    contracts/
    adapters-github/
    cli/
  workers/
    actionable-executor/
    formal-runner/
  policy/
    risk/
    approval/
    gate/
  schemas/
    input/
    decision/
    evidence/
    operation/
  docs/
    architecture/
    operations/
    contracts/
  deploy/
    github-actions/
    k8s/
```

The intent is to keep responsibility boundaries explicit so CLI UX, contracts, policy logic, and workers can evolve independently.

### 8. Ideal security design

- execution identity should be separated by lane
- secrets should be scoped per workflow and environment
- human override must leave an auditable record
- artifact integrity should be verifiable through manifests and checksums
- dispatch-only operations should validate intent, target, and actor permissions up front

### 9. Ideal quality-gate design

- required gates should be minimal, deterministic, and reproducible locally
- extended gates should be opt-in but evidence-preserving
- the final go/no-go decision should read normalized contracts, not raw workflow logs
- each blocked decision should provide machine-readable recovery steps

### 10. Ideal operating model

- solo mode optimizes for low ceremony and high determinism
- team mode adds approval topology and evidence reuse
- enterprise mode adds stronger separation of duties, multi-tenant policy bundles, and durable audit retention

Across all modes, the operator should be able to answer:
- what failed
- why it failed
- what the minimum restart action is
- which artifact proves the final decision

### 11. Phased migration (`current -> ideal`)

1. isolate current contracts and evidence surfaces
2. separate policy evaluation from workflow-specific shell logic
3. introduce normalized state/decision contracts
4. move heavier execution to dedicated workers
5. adopt the ideal topology incrementally with dual-write / dual-validate periods

### 12. Adoption criteria for the ideal design

Adopt the ideal design only when it improves:
- determinism of gate decisions
- traceability of release and merge judgements
- portability across AI producers
- operator recovery speed
- long-term maintainability of policy and artifact contracts

---

## 日本語

## 1. 目的

この文書は、現行実装の制約を一旦外し、`ae-framework` をゼロベースで再設計する場合の理想像を定義する。

対象:
- アーキテクチャ（責務分離・状態遷移・契約）
- 環境/言語/技術スタック（再選定）
- 運用モデル（solo/team/enterprise）

非対象:
- 現時点での即時全面置換
- 既存実装との差分パッチ詳細

前提（2026-03時点の運用要件）:
- GitHub PR駆動の開発フローを継続
- AIレビュー + 自動修正 + ゲート判定の監査可能性を維持
- 証跡（artifacts）を契約として扱う
- codegen は交換可能な producer とみなし、spec / verification / evidence / policy gate を束ねる assurance control plane を中核に置く

## 2. 設計原則（ゼロベース）

1. Contract-First
   - すべての入出力をJSON Schemaで定義し、実装より先に契約を固定する。
2. Deterministic-by-Default
   - 同一入力なら同一判定になることを最優先する（時刻・順序・乱数依存を排除）。
3. Policy as Code
   - 承認要件・リスク判定・必須チェック判定を宣言的ポリシーとして管理する。
4. Observability as Product
   - 失敗原因の分類・復旧導線・SLO/MTTRを最初から仕様化する。
5. Human Override with Trace
   - 人手例外は許可するが、必ず理由・期限・証跡リンクを残す。
6. Assurance is Claim-Based
   - 「何が保証されたか」を claim / level / lane / evidence 単位で説明できるようにする。

## 3. 理想アーキテクチャ（論理構成）

### 3.1 全体像

`ae-framework` を以下5プレーンで分離する。

- Control Plane
  - PR状態機械、実行計画、再試行/収束制御
- Policy Plane
  - リスク分類、必須チェック判定、承認トポロジ判定
- Execution Plane
  - AIレビュー対応、コード修正、各種検証ランナー実行
- Evidence Plane
  - artifacts生成/検証/保存、traceability集約
- Observability Plane
  - 監査ログ、メトリクス、アラート、運用レポート

この理想像でも、コード生成器やレビューAIは Execution Plane の producer として入れ替え可能である。差別化要因は、それらを横断して PR / release の assurance 判断を標準化する Control/Policy/Evidence Plane 側に置く。

### 3.2 コンポーネント（理想責務）

| コンポーネント | 主責務 | I/O契約 |
| --- | --- | --- |
| `orchestrator` | PR単位の状態遷移制御 | `pr-state.v1`, `execution-plan.v1` |
| `policy-engine` | ルール評価（risk/approval/checks） | `policy-input.v1`, `policy-decision.v1` |
| `action-engine` | suggestion/actionable対応実行 | `review-task.v1`, `action-result.v1` |
| `evidence-broker` | 成果物収集と整合性検証 | `evidence-manifest.v1` |
| `gate-evaluator` | 最終Go/No-Go判定 | `gate-evaluation.v1` |
| `ops-reporter` | summary/通知/復旧提案 | `ops-report.v1` |

### 3.3 PR状態機械（理想）

状態:
- `draft`
- `ready_for_review`
- `review_feedback_pending`
- `action_execution`
- `gate_recheck`
- `merge_eligible`
- `blocked`
- `merged`

主要遷移:
- `ready_for_review` -> `review_feedback_pending`（AIレビュー到着）
- `review_feedback_pending` -> `action_execution`（未解決指摘あり）
- `action_execution` -> `gate_recheck`（修正完了）
- `gate_recheck` -> `merge_eligible`（必須ゲートgreen）
- 任意状態 -> `blocked`（fail-closed条件）

`blocked` では必ず以下を出力する:
- `blocked_reason`（機械可読コード）
- `unblock_actions[]`（最小復旧手順）
- `owner_hint`（人/AIどちらが対応すべきか）

## 4. 理想のCI/自動化トポロジ

### 4.1 ワークフロー分類を4系統へ集約

1. `pr-core.yml`（Required）
   - policy gate / review gate / verify-lite / artifact validation
2. `pr-extended.yml`（Label opt-in）
   - heavy tests / formal full / security deep scan
3. `maintenance.yml`（Scheduled + dispatch）
   - rerun / branch sync / stale cleanup / trend analysis
4. `release-assurance.yml`（Dispatch）
   - release verify / rollback verify / post-deploy checks

### 4.2 判定順序（固定）

1. 契約整合（schema・artifact）
2. リスク/承認ポリシー
3. レビュー未解決有無
4. 自動修正可能性評価
5. 必須チェック収束確認
6. auto-merge可否判定

この順序を固定し、workflowごとの差異をなくす。

## 5. 理想の契約モデル

### 5.1 契約レイヤ

- `input contracts`
  - review comments, changed files, labels, workflow context
- `decision contracts`
  - risk decision, approval decision, gate decision
- `evidence contracts`
  - run summary, trace summary, formal summary, change package
- `operation contracts`
  - retry policy, backoff policy, escalation policy

### 5.2 互換方針

- すべて `schema_version` を持つ
- 後方互換は同一major内のみ保証
- major更新時は `dual-write` + `dual-validate` 期間を設ける

## 6. 環境/言語/技術の再選定（フリーハンド）

### 6.1 推奨スタック（理想案A: Hybrid）

| レイヤ | 推奨 | 理由 |
| --- | --- | --- |
| Orchestrator / Policy Runtime | Go 1.24系 | 単一バイナリ、並列処理、CI実行の安定性 |
| CLI/Adapter/Schema Tooling | TypeScript (Node.js 22 LTS, pnpm 10) | GitHub API/JSON処理エコシステムとの親和性 |
| 高負荷実行Worker | Rust stable | CPU集約処理・安全性・配布容易性 |
| Policy DSL | Rego (OPA) | 判定ロジックを宣言化しテストしやすい |
| Contract Validation | JSON Schema 2020-12 + AJV | 現行資産との互換性と運用実績 |
| Event Bus | NATS JetStream | 低運用コストで再試行/順序制御が容易 |
| Metadata DB | PostgreSQL 16 | 監査クエリと参照整合性 |
| Artifact Store | S3互換ストレージ | 証跡の長期保存と再解析 |
| Cache | Redis 7 | idempotency key / short-lived state |
| Observability | OpenTelemetry + Prometheus + Loki + Tempo + Grafana | トレース/ログ/メトリクス統合 |
| Packaging | OCI + distroless | セキュリティ更新と再現性 |

### 6.2 実行環境プロファイル

#### Solo（開発者1名 + AIエージェント）
- GitHub Actions中心
- 外部DBなし（SQLite + artifact files でも可）
- OPAはローカルbundle

#### Team（2〜20名）
- GitHub Actions + 軽量Control Plane（Go service）
- PostgreSQL + S3 + Redis
- NATSで非同期ジョブ分離

#### Enterprise（高トラフィック）
- Kubernetes（HPA）
- PostgreSQL HA / object storage multi-AZ
- multi-tenant policy bundles

### 6.3 代替スタック案

- 理想案B（TypeScript-only）
  - 速度優先で導入しやすいが、長期的には運用負荷が増えやすい。
- 理想案C（Rust-first）
  - 性能と安全性は高いが、開発速度と採用難易度が課題。

推奨は理想案A（Hybrid）。

## 7. リポジトリ構成（理想）

```text
/
  cmd/
    orchestrator/
    policy-engine/
    ops-reporter/
  packages/
    contracts/
    adapters-github/
    cli/
  workers/
    actionable-executor/
    formal-runner/
  policy/
    risk/
    approval/
    gate/
  schemas/
    input/
    decision/
    evidence/
  workflows/
    pr-core/
    pr-extended/
    maintenance/
    release-assurance/
  docs/
    architecture/
    operations/
    contracts/
```

## 8. セキュリティ設計（理想）

- Token分離
  - read-only token と write token をジョブ単位で分離
- Provenance
  - 主要artifactへ署名（Sigstore/cosign）
- Least Privilege
  - workflowごとに最小権限を明示
- Secret Zero
  - 可能な限りOIDC federationで短命資格情報を使用

## 9. 品質ゲート設計（理想）

必須ゲート（常時）:
- contract validation
- policy decision
- review resolution
- verify-lite
- artifact required set

条件付きゲート（policy-driven）:
- high-risk approvals
- trace conformance
- security deep scan
- formal full run

fail-open は原則禁止。例外時は `temporary_override` 契約と期限を必須化。

## 10. 運用設計（理想）

SLO例:
- Required checks success rate: `>= 99.5%`
- `blocked` から `merge_eligible` へのMTTR（P50）: `<= 30分`
- false-block rate: `<= 1%`

運用Runbookの最低要件:
- 失敗分類コード（固定辞書）
- 復旧コマンド（1コマンド単位）
- 再発防止テンプレート

## 11. 段階移行（現行 -> 理想）

1. Contract先行
   - 現行scriptsの入出力を契約化
2. Policy Engine分離
   - 判定ロジックをworkflowから独立
3. Orchestrator導入
   - 複数workflowの状態遷移を一本化
4. Worker分離
   - 重い処理を非同期化
5. Legacy workflow廃止
   - 互換期間後に削除

## 12. この理想設計の採用判断基準

採用すべき条件:
- 現行運用で `workflow肥大化` / `判定重複` / `レビュー反映遅延` が継続している
- 複数プロダクトで共通の自動化基盤として再利用したい

見送る条件:
- 単一リポジトリ・小規模運用で、現行構成の保守コストが十分低い

---

更新日: 2026-03-03
