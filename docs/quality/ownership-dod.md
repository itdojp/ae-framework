---
docRole: derived
canonicalSource:
- policy/risk-policy.yml
- policy/quality.json
lastVerified: '2026-03-29'
---
# Ownership DoD (Definition of Done)

> Language / 言語: English | 日本語

---

## English

Purpose: define ownership requirements for AI-assisted changes so teams can explain, support, and roll back safely.

Scope:
- Applies to behavior changes, new integrations, and policy changes.
- Use together with Spec / Blueprint artifacts and PR summary evidence.

### Required ownership artifacts

- Owner: the responsible person or team
- Runbook: operational steps for on-call, mitigation, and recovery
- Failure modes: known risks and expected mitigations
- Rollback plan: how to revert the change safely
- Evidence: PR summary, verification gates, and relevant artifacts

### DoD checklist

- An owner is named and reachable
- The runbook exists or is updated
- Failure modes are listed and reviewed
- Rollback is documented and tested when practical
- PR evidence is complete, including summary and artifacts

### Suggested references

- `docs/quality/llm-first-review-checklist.md`
- `docs/quality/incident-triage-template.md`
- `docs/quality/pr-summary-template.md`
- `docs/templates/blueprint/blueprint-template.md`

## 日本語

目的: AI 支援で行う変更について、説明・運用・ロールバックの責任所在を明確にし、安全に引き継げる状態を定義する。

対象範囲:
- 振る舞い変更、新規 integration、policy change に適用する。
- Spec / Blueprint artifact と PR summary evidence と併用する。

### 必須の ownership artifact

- Owner: 責任を持つ個人またはチーム
- Runbook: 当番対応、緩和策、復旧手順をまとめた運用手順
- Failure modes: 既知のリスクと想定 mitigation
- Rollback plan: 安全に差し戻すための手順
- Evidence: PR summary、verification gates、関連 artifact

### DoD checklist

- owner が明記され、連絡可能である
- runbook が存在する、または更新済みである
- failure modes が列挙され、レビューされている
- rollback が文書化され、可能ならテストされている
- PR evidence が summary と artifact を含めて揃っている

### 参考文書

- `docs/quality/llm-first-review-checklist.md`
- `docs/quality/incident-triage-template.md`
- `docs/quality/pr-summary-template.md`
- `docs/templates/blueprint/blueprint-template.md`
