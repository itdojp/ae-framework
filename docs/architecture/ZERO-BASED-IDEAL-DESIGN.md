# Zero-Based Ideal Design Blueprint (2026-03)

> Language / 言語: English | 日本語

---

## English (Summary)

This document describes an ideal, from-scratch redesign of ae-framework.
It includes: (1) a target architecture, (2) a free-hand technology stack reconsideration,
and (3) migration principles to move from the current implementation to the target shape.

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
