# Quality Templates

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

This folder indexes quality templates used for guarded automation and ownership.
Canonical templates live under `docs/quality/` and are linked below for reuse.

### Templates
- Guarded automation policy: `docs/quality/guarded-automation-template.md`
- Incident triage: `docs/quality/incident-triage-template.md`
- Ownership DoD: `docs/quality/ownership-dod.md`
- LLM-first review checklist: `docs/quality/llm-first-review-checklist.md`
- PR summary template: `docs/quality/pr-summary-template.md`

### Guardrails (machine verifying machine)
- Human review is required before merge, even if automated gates pass.
- Evidence must include PR summaries and links to artifacts.
- If a required gate cannot run, document the exception and open a follow-up issue.

---

## 日本語（概要）

このフォルダは、ガード付き自動化とオーナーシップの品質テンプレを整理するための索引です。
テンプレの本体は `docs/quality/` に置き、以下に参照リンクを集約しています。

### テンプレ一覧
- ガード付き自動化ポリシー: `docs/quality/guarded-automation-template.md`
- インシデント・トリアージ: `docs/quality/incident-triage-template.md`
- Ownership DoD: `docs/quality/ownership-dod.md`
- LLM-first レビュー・チェックリスト: `docs/quality/llm-first-review-checklist.md`
- PRサマリーテンプレ: `docs/quality/pr-summary-template.md`

### ガードレール（machine verifying machine）
- 自動ゲートが通っても、人のレビューを必須とする。
- 証跡は PR サマリーと成果物リンクを含める。
- 必須ゲートが動作できない場合は例外理由を記録し、フォローアップ Issue を起票する。
