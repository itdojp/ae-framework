# JUnit/XML Interop Notes

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

XML への依存をコアから排除し、正規化 JSON を PR 集約の唯一の入力にします。必要に応じて raw JUnit もアーティファクトとしてアップロードします。

- Keep core dependency-free from XML parsers; normalization happens in adapters or CI.
- Upload raw JUnit artifacts for external tooling, but aggregate PR summary from JSON.
- Suggested paths:
  - `artifacts/<adapter>/summary.json` (normalized, PR aggregation source)
  - `artifacts/<adapter>/junit.xml` (optional raw)
- Include `traceId` in JSON where applicable.
