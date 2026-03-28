---
docRole: narrative
lastVerified: '2026-03-28'
---
# Incident Triage Template

> Language / 言語: English | 日本語

---

## English

Purpose: Provide a minimal, repeatable format for incident triage in AI-assisted development.

When to use:
- CI failures with unclear root cause
- Regression detected after merge
- Production or staging anomaly

### Triage summary (fill in)

- Incident ID / Link:
- Detected by (CI, monitoring, user report):
- First observed time (UTC):
- Affected area (module/service):
- Severity (low/medium/high/critical):
- Current status (open/mitigating/resolved):

### Evidence snapshot

- Failing checks / logs:
- Related PR(s) / commit(s):
- Reproduction steps:
- Artifacts (reports, traces, coverage, trends):

### Diagnosis

- Likely cause (hypothesis):
- What changed recently:
- Why the existing gates did not catch it:

### Mitigation plan

- Immediate containment:
- Rollback plan (if needed):
- Short-term fix:
- Owner:

### Post-incident actions

- Add or adjust verification gates:
- Add regression test(s):
- Update documentation / runbook:
- Follow-up issue(s):

### Notes

- Keep this short. If the incident expands, move details to a dedicated issue or report.

## 日本語

目的: AI 支援開発におけるインシデントトリアージを、最小かつ再利用可能な形式で実施するためのテンプレートです。

利用場面:
- 根本原因が不明な CI 障害
- merge 後に検出されたリグレッション
- 本番またはステージングでの異常

### トリアージ要約（記入用）

- Incident ID / Link:
- 検知元（CI / 監視 / ユーザー報告）:
- 初回観測時刻（UTC）:
- 影響範囲（module / service）:
- 重大度（low / medium / high / critical）:
- 現在の状態（open / mitigating / resolved）:

### 証跡スナップショット

- 失敗した check / log:
- 関連 PR / commit:
- 再現手順:
- Artifacts（report / trace / coverage / trend）:

### 診断

- 想定される原因（仮説）:
- 直近の変更点:
- 既存ゲートで検出できなかった理由:

### 緩和計画

- 直ちに行う封じ込め:
- Rollback plan（必要な場合）:
- 短期修正:
- 担当者:

### インシデント後の対応

- 追加または調整する verification gate:
- 追加する回帰 test:
- 更新する documentation / runbook:
- follow-up issue:

### Notes

- 長文化は避けてください。内容が拡大する場合は、詳細を専用 issue または report に切り出してください。
