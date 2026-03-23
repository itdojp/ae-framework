---
docRole: derived
canonicalSource:
  - README.md
  - docs/agents/hook-feedback.md
lastVerified: '2026-03-23'
---

# Codex連携の責務境界と Vendor-neutral 最小コア

> 🌍 Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document defines the operational boundary for Codex integration so `ae-framework` keeps its differentiated core in SSOT, verification, and evidence while avoiding redundant functionality.

Scope: `#1973` (parent: `#1969`)

### 2. Responsibility boundary by operation (`keep` / `reduce` / `integrate`)

| Operation | Codex side | ae-framework side | Decision |
| --- | --- | --- | --- |
| Plan creation / decomposition | Organize and align through conversation | Consume as an input asset | integrate |
| Spec updates | Assist with proposal and drafting | Fix as SSOT and make reviewable | keep |
| Gate execution | Trigger and orchestrate | Own judgement rules, evidence contracts, and result evaluation | keep |
| Evidence collection | Help collect and package | Own evidence contracts, storage, and traceability | keep |
| Thread / parallel execution experience | Primary owner | Do not rebuild it | reduce |
| Vendor-specific APIs | Use as execution channels | Abstract behind the minimum interface | integrate |

### 3. Vendor-neutral minimum interface

The minimum requirement is that the same workflow remains reproducible even without Codex.

- CLI execution:
  - `pnpm run types:check`
  - `pnpm run lint`
  - `pnpm run build`
  - `pnpm run test:ci:lite`
- CI execution:
  - `verify-lite` (required)
  - `policy-gate` (required)
  - `gate` (required, Copilot Review Gate)
  - `docs-doctest` (required for docs-touching PRs)
  - opt-in jobs for formal, security, adapters, and QA
- Artifact contract:
  - `docs/quality/ARTIFACTS-CONTRACT.md`
  - PRs must remain traceable to the evidence stored under `artifacts/**`

### 4. Fail-open / fail-closed boundary

| Case | Default | Condition | Required action |
| --- | --- | --- | --- |
| Required gate failure | fail-closed | Always | Fix and rerun; record the reason if an exception is approved |
| Opt-in gate failure | fail-open allowed | Only when the gate is non-required | Record the failure reason and open a follow-up issue |
| Unresolved `gate` findings | fail-closed | Always | Resolve the thread or reply with evidence |
| External dependency failure (SaaS / API) | fail-open allowed | Only when equivalent alternative verification exists | Preserve the alternative run log and document the limitation |

### 5. Operator decision guide

1. Treat plans as conversation assets; only repository-normalized content is canonical.
2. Pass the required gates first and add opt-in gates only when change risk justifies them.
3. When using fail-open, make the exception reason and a time-bounded follow-up issue mandatory.
4. Even when Codex-specific features are used, keep the workflow reproducible with CLI and CI only.

### 6. References

- `docs/integrations/CODEX-INTEGRATION.md`
- `docs/ci/pr-automation.md`
- `docs/ci/automation-failure-policies.md`
- `docs/ci-policy.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`

---

## 日本語

### 1. 目的

Codex連携時に機能重複を避けつつ、ae-framework の差別化コア（SSOT / 検証 / 証跡）を維持するための運用基準を定義します。

対象: #1973（親: #1969）

### 2. 操作単位の責務境界（keep / reduce / integrate）

| 操作 | Codex 側 | ae-framework 側 | 方針 |
| --- | --- | --- | --- |
| Plan 作成・分解 | 会話での整理/合意 | 入力として受け取る | integrate |
| Spec 更新 | 補助（提案・下書き） | SSOTとして固定・レビュー可能化 | keep |
| Gate 実行 | トリガー/オーケストレーション | 判定条件・証跡契約・結果評価 | keep |
| 証跡収集 | 補助（収集起点） | Evidence 契約、保管、追跡 | keep |
| スレッド/並列実行体験 | 主担当 | 再実装しない | reduce |
| 依存ベンダーAPI | 実行チャネルとして利用 | 最小I/Fで抽象化 | integrate |

### 3. Vendor-neutral 最小I/F

Codex がなくても再現可能であることを最小要件とする。

- CLI 実行:
  - `pnpm run types:check`
  - `pnpm run lint`
  - `pnpm run build`
  - `pnpm run test:ci:lite`
- CI 実行:
  - `verify-lite`（required）
  - `policy-gate`（required）
  - `gate`（required, Copilot Review Gate）
  - `docs-doctest`（docs 変更 PR では required）
  - opt-in jobs（formal/security/adapters/qa）
- 成果物契約:
  - `docs/quality/ARTIFACTS-CONTRACT.md`
  - `artifacts/**` の証跡を PR から追跡できること

### 4. fail-open / fail-closed 境界

| ケース | 既定 | 条件 | 必須アクション |
| --- | --- | --- | --- |
| Required gate 失敗 | fail-closed | 常時 | 修正して再実行、例外時は理由記録 |
| Opt-in gate 失敗 | fail-open 可能 | 非必須運用時のみ | 失敗理由とフォローアップIssue起票 |
| `gate` 未解決 | fail-closed | 常時 | コメント解消または根拠付き応答 |
| 外部依存不調（SaaS/API） | fail-open 可能 | 代替検証が可能な場合 | 代替実行ログと制限事項を記録 |

### 5. 利用者向け判断ガイド

1. Plan は会話資産として扱い、repo に正規化した内容のみを正とする。  
2. まず Required gate を通し、必要な場合にのみ Opt-in gate を追加する。  
3. fail-open を使う場合は、例外理由と期限付きフォローアップIssueを必須にする。  
4. Codex専用機能を使っても、CLI/CI 単独で再実行できる状態を維持する。

### 6. 参照

- `docs/integrations/CODEX-INTEGRATION.md`
- `docs/ci/pr-automation.md`
- `docs/ci/automation-failure-policies.md`
- `docs/ci-policy.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
