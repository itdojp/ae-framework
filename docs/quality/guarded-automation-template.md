---
docRole: derived
canonicalSource:
- docs/ci/pr-automation.md
- policy/risk-policy.yml
lastVerified: '2026-03-27'
---
# Guarded Automation Template

> 🌍 Language / 言語: English | 日本語

---

## English

Purpose: Define what automation may do, and where humans must decide, for AI-assisted changes.

## Scope
- Applies to PRs created by LLM or agent workflows.
- This template is a policy stub; teams can extend it per repository.

## Allowed automation (safe)
- Drafting specs or blueprints
- Generating code and tests
- Running CI in `verify-lite` mode
- Posting summaries such as the PR summary, artifacts, and links

## Required human steps (non-automated)
- Approve merge after reviewing diffs and evidence
- Accept or reject risky changes such as security, data, or infrastructure changes
- Sign off on threshold changes such as coverage, performance, or accessibility

## Evidence required before merge
- A PR summary containing `verify-lite`, `policy-gate`, and `gate` results
- Links to artifacts such as reports, traces, and trends
- A rollback plan when behavior changes

## Gate policy (minimum)
- `verify-lite` must be green
- `policy-gate` must be green
- `gate` (`Copilot Review Gate`) must be green
- Any required label-gates must be satisfied

## Exception handling
- If a required gate cannot run, document the reason and open a follow-up issue
- Emergency fixes still require post-merge review and retroactive evidence

## Decision record (copy into PR comment)

```text
Guarded Automation Decision
- Automation scope: [OK/Needs work]
- Human review: [OK/Needs work]
- Evidence: [OK/Needs work]
- Exceptions: [None/Describe]
- Notes:
```

## References
- `docs/quality/llm-first-review-checklist.md`
- `docs/quality/pr-summary-template.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/label-gating.md`

---

## 日本語

目的: AI 支援で行う変更について、自動化が実施してよい範囲と、人間が判断すべき境界を定義します。

## 対象範囲
- LLM または agent workflow が作成した PR に適用します。
- このテンプレートは policy の雛形であり、各 repository ごとに拡張できます。

## 許可される自動化（安全側）
- spec または blueprint の下書き作成
- コードとテストの生成
- `verify-lite` モードでの CI 実行
- PR summary、artifact、関連リンクなどの要約投稿

## 人間が必ず実施する手順（自動化しない）
- diff と evidence を確認したうえでの merge 承認
- security、data、infrastructure など高リスク変更の受理または却下
- coverage、performance、accessibility など threshold 変更への sign-off

## merge 前に必要な evidence
- `verify-lite` / `policy-gate` / `gate` の結果を含む PR summary
- report、trace、trend など artifact へのリンク
- 振る舞い変更がある場合の rollback plan

## gate policy（最低限）
- `verify-lite` が green であること
- `policy-gate` が green であること
- `gate`（`Copilot Review Gate`）が green であること
- required な label-gate があれば、それを満たしていること

## 例外処理
- required gate が実行できない場合は、理由を文書化し、follow-up issue を起票する
- 緊急修正であっても、merge 後 review と事後 evidence は必須

## 判断記録（PR コメントへ転記）

```text
Guarded Automation Decision
- Automation scope: [OK/Needs work]
- Human review: [OK/Needs work]
- Evidence: [OK/Needs work]
- Exceptions: [None/Describe]
- Notes:
```

## 参照
- `docs/quality/llm-first-review-checklist.md`
- `docs/quality/pr-summary-template.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/label-gating.md`
