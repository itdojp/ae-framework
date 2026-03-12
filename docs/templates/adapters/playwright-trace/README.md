---
docRole: ssot
lastVerified: '2026-03-12'
owner: templates-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Playwright Trace Adapter Notes

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

トレースの ZIP は raw としてアップロードし、PR 集約用には正規化 JSON（トレース数や生成ファイル数等の高レベル統計）を使用します。詳細な解析はコア外で行います。

- Use normalized JSON to summarize trace artifacts (e.g., count of traces, files produced).
- Upload raw trace zips separately for manual inspection.
- Keep parsing/inspection outside core; PR summary shows high-level stats only.
