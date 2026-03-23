---
docRole: derived
canonicalSource:
- docs/ci/pr-automation.md
- docs/project/GOVERNANCE.md
lastVerified: '2026-03-23'
---
# Thread -> Repo -> CI Flow Guide (Plan -> Spec Normalization)

> Language / 言語: English | 日本語

---

## English

This guide standardizes how conversation plans are normalized into repository SSOT, then validated in CI with traceable evidence. Treat the conversation thread as planning input, not as implementation SSOT. The repository specification and the recorded CI evidence remain the authoritative artifacts.

### 1. Purpose
Use this workflow when a plan originates in a thread or issue and must be converted into a repository artifact before implementation and review. The goal is to keep the plan, repository specification, CI judgement, and PR evidence aligned.

### 2. Inputs, outputs, and update timing

| Phase | Inputs | Outputs | Update timing |
| --- | --- | --- | --- |
| Thread triage | Conversation plan, issue, constraints, risks | Plan summary or operator memo | At the start of the work |
| Repository normalization | Plan summary | Draft spec filled from `docs/templates/plan-to-spec-normalization-template.md` | Before the PR is opened |
| CI validation | Draft spec, gate definitions | Gate status and evidence (`summary`, logs, reports) | On each PR update |
| Evidence fixation | CI results, reproduction commands | PR description/comments with traceability links | Before review and before merge |

### 3. Standard procedure

#### Step 0: Organize the plan in the thread
- Extract requirements, scope, acceptance criteria, non-functional constraints, and explicit exclusions.
- Treat the result as a working memo only. It is not SSOT.

#### Step 1: Normalize into the repository
- Copy `docs/templates/plan-to-spec-normalization-template.md` into the working spec or runbook.
- Fill, at minimum:
  - Goal / Scope
  - Acceptance criteria (`Given/When/Then`)
  - Non-functional requirements
  - Verification plan (required and optional gates)
  - Traceability map

#### Step 2: Let CI judge the normalized artifact
- Run the current main required gates: `verify-lite`, `policy-gate`, and `gate`.
- Opt in to formal, security, adapters, or QA lanes when the change warrants them.

#### Step 3: Fix evidence in the PR
- Record the CI run URL, the result summary, and the reproduction commands in the PR.
- Make the mapping from plan item -> spec artifact -> gate -> evidence explicit and reviewable.

### 4. Example traceability entry for a PR

| Source plan/thread | Spec path | Gate | Evidence |
| --- | --- | --- | --- |
| Issue or thread URL | `docs/templates/plan-to-spec-normalization-sample.md` | `verify-lite` | CI URL + `artifacts/verify-lite/verify-lite-run-summary.json` |

### 5. Rerun procedure when validation fails
1. Identify the failed required gate (`gate`, `policy-gate`, or `verify-lite`).
2. Inspect the related spec, acceptance criteria, and NFR deltas.
3. If needed, re-extract the requirement from the original thread and update the normalized template.
4. Reproduce locally where feasible, then push the correction.
5. After the CI rerun, update the PR evidence section.

### 6. Minimum review checklist
- Is the plan fixed into a repository artifact rather than left only in the thread?
- Is the mapping between acceptance criteria/NFRs and the implementation change explicit?
- Are the required gates green or accompanied by a defensible reproduction path?
- Are out-of-scope items stated explicitly?

### 7. Related documents
- `docs/templates/plan-to-spec-normalization-template.md`
- `docs/templates/plan-to-spec-normalization-sample.md`
- `docs/strategy/CODEX-AE-BOUNDARY-VERIFY-FIRST.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`

---

## 日本語

## 1. 目的

Plan（会話資産）を直接実装の正にせず、repo 上の Spec を SSOT として固定するための運用手順です。  
本ガイドは特定のIssueに依存しない一般的な運用標準です。

## 2. 入力/出力/更新タイミング

| フェーズ | 入力 | 出力 | 更新タイミング |
| --- | --- | --- | --- |
| Thread 整理 | 会話Plan、Issue、制約、リスク | Plan要約（作業メモ） | 作業開始時 |
| Repo 正規化 | Plan要約 | `docs/templates/plan-to-spec-normalization-template.md` を埋めたSpec草案 | PR作成前 |
| CI 検証 | Spec草案、ゲート定義 | ゲート合否、Evidence（summary/log） | PR更新ごと |
| Evidence 固定 | CI結果、再現手順 | PR本文/コメントのトレーサビリティ記録 | Review前/マージ前 |

## 3. 標準手順

### Step 0: Thread でPlanを整理
- 要件、スコープ、受入条件、非機能、制約を抽出する。
- ここでの成果物は作業メモ。SSOTではない。

### Step 1: Repo に正規化
- `docs/templates/plan-to-spec-normalization-template.md` をコピーして作業対象のSpecへ反映。
- 最低限、以下を埋める:
  - Goal/Scope
  - AC（Given/When/Then）
  - NFR
  - Verification Plan（Required/Optional gates）
  - Traceability Map

### Step 2: CI で機械判定
- Required gates（current main baseline: `verify-lite` / `policy-gate` / `gate`）を実行。
- 必要に応じて formal/security/adapters/qa を opt-in 実行。

### Step 3: Evidence を固定
- CI run URL、結果要約、再現コマンドをPRに記録。
- Plan item -> Spec artifact -> Gate -> Evidence の対応をPRで参照可能にする。

## 4. トレーサビリティ記載例（PR向け）

| Source plan/thread | Spec path | Gate | Evidence |
| --- | --- | --- | --- |
| Issue/Thread URL | `docs/templates/plan-to-spec-normalization-sample.md` | verify-lite | CI URL + `artifacts/verify-lite/verify-lite-run-summary.json` |

## 5. 失敗時の再実行手順

1. 失敗ゲートを特定（例: `gate` / `policy-gate` / `verify-lite`）。
2. 関連する Spec/AC/NFR の差分を確認。  
3. 必要なら Plan から再抽出し、正規化テンプレートの該当欄を更新。  
4. ローカル再現（可能な範囲）後に push。  
5. CI rerun 実施後、PRのEvidence欄を更新。

## 6. レビュー観点（最小）

- Planの要求が Spec に固定されているか
- AC/NFR と実装変更の対応が明確か
- Required gate の合否と再現導線があるか
- Out-of-scope が明示されているか

## 7. 関連ドキュメント

- `docs/templates/plan-to-spec-normalization-template.md`
- `docs/templates/plan-to-spec-normalization-sample.md`
- `docs/strategy/CODEX-AE-BOUNDARY-VERIFY-FIRST.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
