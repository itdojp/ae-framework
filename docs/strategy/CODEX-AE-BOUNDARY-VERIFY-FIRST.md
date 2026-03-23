---
docRole: ssot
lastVerified: '2026-03-23'
owner: product-strategy
verificationCommand: pnpm -s run check:doc-consistency
---

# Codex と ae-framework の責務境界（Verify-first 戦略）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document defines the operational boundary between Codex capabilities (plans, skills, automations) and `ae-framework` capabilities in overlapping areas. The goal is to keep the value center of `ae-framework` fixed on **Verify-first**: verification criteria, gate decisions, and evidence remain first-class outputs.

### 2. Positioning

- **Codex**: the execution cockpit that optimizes conversation, thread handling, delegated work, and operational automation
- **ae-framework**: the governance rail that makes outputs harder to break through SSOT, quality gates, evidence, and auditability

Principles:
- **Conversation is not SSOT**: plans in the thread are input assets. The canonical state must be fixed in repository artifacts.
- **Verify-first**: verification conditions and pass/fail judgement are more important than ad hoc execution sequences.
- **Policy-as-code**: quality, security, and compliance requirements must remain machine-evaluable.
- **Vendor-neutral**: prefer artifact contracts that do not depend on a single agent vendor.

### 3. Overlap matrix and operating decision

| Area | Codex responsibility | ae-framework responsibility | SSOT | Policy |
| --- | --- | --- | --- | --- |
| Plan (requirement shaping / task decomposition) | Dialogue, decomposition, alignment | Normalization rules into specs | repo | **integrate** |
| Execution experience (threads / parallel work / task isolation) | Primary owner | No competing implementation; consume only | n/a | **reduce** |
| Skills (repeatable procedures) | Execution channel | Distribute procedures that assume gate and evidence discipline | repo | **integrate** |
| Automation triggers (dispatch / comment / labels) | Execution entrypoint | Define decision criteria and safety boundaries | repo + CI | **integrate** |
| Verification / quality gates | Execution helper only | Own gate definitions, judgements, and evidence contracts | repo + CI | **keep** |
| Auditability / reproducibility | Supplemental signals | Own evidence contracts, collection, and traceability | repo + artifacts | **keep** |

Decision rules:
- **keep**: differentiated core of SSOT, verification, and evidence
- **reduce**: experience layer that should be delegated to the platform
- **integrate**: areas that should be connected as inputs or distribution channels

### 4. Non-goals

- Rebuilding a full UI / thread / parallel-execution experience that competes directly with Codex
- Treating `ae-framework` as a generic agent runtime
- Overcommitting to vendor-specific APIs when contract-neutral artifacts suffice

### 5. Standard flow (`Thread -> Repo -> CI`)

#### Step 0: Thread (conversation assets)
- Use Codex to organize requirements, tasks, and risks.
- At this point, the plan is only a working memo, not SSOT.

#### Step 1: Repo (normalize into SSOT)
- Use `docs/templates/plan-to-spec-normalization-template.md` to fix the plan into repository artifacts.
- Update, at minimum:
  - purpose / scope
  - acceptance criteria
  - non-functional requirements and constraints
  - verification conditions (which gate judges what)

#### Step 2: CI (machine judgement)
- Run the minimum required gate set, for example `verify-lite`, `policy-gate`, and `gate`.
- Add heavier opt-in verification only when the change warrants it.
- When a gate fails, preserve diagnosis and reproduction steps as evidence.

#### Step 3: Evidence (make the judgement auditable)
- Preserve PR/CI results, summaries, and related artifact links.
- Keep the reason for the change and the basis for the judgement traceable.

### 6. Minimum Verify-first artifact set

Required minimum:
- **Spec**: requirement, acceptance criteria, non-functional constraints, and explicit limits
- **Gate definition**: which CI checks are required
- **Evidence**: result logs, major artifacts, and reproduction commands

Optional extensions:
- formal-method reports (TLA+, Alloy, CSP, Lean, and similar)
- additional performance, security, or dependency-audit evidence

### 7. Operational rules

- At PR creation, state which repository artifacts absorb the thread plan.
- Do not merge changes with unmet required gates unless a fail-open exception is explicitly approved.
- Manage automation settings as repository variables and policy, not as undocumented operator conventions.

### 8. References

- `docs/product/POSITIONING.md`
- `docs/product/OVERVIEW.md`
- `docs/ci/pr-automation.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/templates/plan-to-spec-normalization-template.md`

---

## 日本語

## 1. 目的

本ドキュメントは、Codex の Plan/Skills/Automations と ae-framework の機能が重複する領域を整理し、
**ae-framework の価値中心を Verify-first（検証主語）に固定**するための運用基準を定義します。

## 2. ポジショニング

- **Codex**: 実行体験を最適化する操縦席（会話、スレッド、並列実行、運用自動化）
- **ae-framework**: 生成物を壊れにくくするレール（SSOT、品質ゲート、証跡、監査性）

原則:
- **Conversation is not SSOT**: 会話上の計画は入力。正は repo に固定する。
- **Verify-first**: 実行手順より、検証条件と合否判定を第一級成果物として扱う。
- **Policy-as-code**: 品質/セキュリティ/コンプラ要件を機械判定可能に保つ。
- **Vendor-neutral**: 特定エージェントに依存しない成果物規約を優先する。

## 3. 競合領域マトリクス（運用判断）

| 領域 | Codex 側の役割 | ae-framework 側の役割 | SSOT | 方針 |
| --- | --- | --- | --- | --- |
| Plan（要件整理/タスク分解） | 対話・分解・合意形成 | Spec への正規化ルール | repo | **integrate** |
| 実行体験（スレッド/並列/作業分離） | 主担当 | 競合しない（利用のみ） | n/a | **reduce** |
| Skills（定型手順） | 実行チャネル | 品質ゲート前提の手順を配布 | repo | **integrate** |
| 自動化トリガ（dispatch/comment） | 実行起点 | 判定条件と安全境界を規定 | repo + CI | **integrate** |
| 検証/品質ゲート | 実行補助 | ゲート定義・判定・証跡契約の本体 | repo + CI | **keep** |
| 監査性/再現性 | 補助情報 | Evidence 契約・収集・追跡の本体 | repo + artifacts | **keep** |

判断基準:
- **keep**: 差別化コア（SSOT/検証/証跡）
- **reduce**: プラットフォームに委譲すべき体験層
- **integrate**: 入力吸収または配布チャネルとして連携すべき領域

## 4. Non-goals（明示的に実施しない）

- Codex と同等の UI/スレッド/並列実行体験の再実装
- 汎用エージェント実行ランタイムでの正面競争
- 特定ベンダー専用 API への過度なロックイン

## 5. 標準フロー（Thread -> Repo -> CI）

### Step 0: Thread（会話資産）
- Codex で要件・タスク・リスクを整理
- この時点の Plan は作業メモであり、SSOT ではない

### Step 1: Repo（SSOT 正規化）
- `docs/templates/plan-to-spec-normalization-template.md` を使い、Plan を repo 資産へ固定
- 最低限、以下を更新:
  - 目的/スコープ
  - Acceptance Criteria
  - NFR/制約
  - 検証条件（どのゲートで何を判定するか）

### Step 2: CI（機械判定）
- 最小セットの品質ゲートを実行（例: `verify-lite`, `policy-gate`, `gate`）
- 必要に応じて opt-in で重い検証を追加
- 失敗時は診断と再現手順を Evidence として残す

### Step 3: Evidence（監査可能化）
- PR/CI の判定結果、要約、関連成果物リンクを保存
- 変更理由と判定根拠を追跡可能にする

## 6. Verify-first の最小成果物セット

必須（Minimum）:
- **Spec**: 要件、受入基準、非機能、制約
- **Gate definition**: どの CI チェックを required とするか
- **Evidence**: 合否ログ、主要成果物、再現手順

任意（Extension）:
- 形式手法レポート（TLA+/Alloy/CSP/Lean など）
- 性能・セキュリティ・依存性監査の追加証跡

## 7. 運用ルール（実務）

- PR 作成時に「Plan の内容はどの repo 資産に反映したか」を明記する
- ゲート未通過の変更は merge しない（明示的な fail-open 例外を除く）
- 自動化設定は repo 変数・ポリシーとして管理し、手順書と乖離させない

## 8. 参照

- `docs/product/POSITIONING.md`
- `docs/product/OVERVIEW.md`
- `docs/ci/pr-automation.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/templates/plan-to-spec-normalization-template.md`
