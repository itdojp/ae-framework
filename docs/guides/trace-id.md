# Trace ID Guidelines

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

NL → BDD → Formal → Tests → Code → Artifacts の全段で安定した `traceId` を使用する指針です。PR サマリでのフィルタリング容易化のため、各種サマリに `traceId` を含めます。

- Use a stable `traceId` across NL → BDD → Formal → Tests → Code → Artifacts.
- Include `traceId` in: property summaries, adapter summaries, formal summaries, domain events.
- Surface `traceId` in PR summaries for quick filtering.
