---
docRole: narrative
lastVerified: '2026-04-07'
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
- フォローアップ issue(s):

### Notes

- Keep this short. If the incident expands, move details to a dedicated issue or report.

## 日本語

目的: AI 支援開発におけるインシデントトリアージを、最小かつ再利用可能な形式で実施するためのテンプレートです。

利用場面:
- 根本原因が不明な CI 障害
- マージ後に検出されたリグレッション
- 本番またはステージングでの異常

### トリアージ要約（記入用）

- インシデントID / リンク:
- 検知元（CI / 監視 / ユーザー報告）:
- 初回観測時刻（UTC）:
- 影響範囲（モジュール / サービス）:
- 重大度（低 / 中 / 高 / クリティカル）:
- 現在の状態（open / mitigating / resolved）:

### 証跡スナップショット

- 失敗したチェック / ログ:
- 関連 PR / コミット:
- 再現手順:
- 証跡成果物（report / trace / coverage / trend）:

### 診断

- 想定される原因（仮説）:
- 直近の変更点:
- 既存ゲートで検出できなかった理由:

### 緩和計画

- 直ちに行う封じ込め:
- ロールバック計画（必要な場合）:
- 短期修正:
- 担当者:

### インシデント後の対応

- 追加または調整する検証ゲート:
- 追加する回帰テスト:
- 更新する文書 / runbook:
- フォローアップ issue:

### 備考

- 長文化は避けてください。内容が拡大する場合は、詳細を専用 issue または report に切り出してください。
