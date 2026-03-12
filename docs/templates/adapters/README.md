---
docRole: ssot
lastVerified: '2026-03-12'
owner: templates-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Adapter Output Normalization

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

アダプターの出力は正規化し、以下を満たしてください：
- `artifacts/<adapter>/summary.json` に正規化結果を書き出す
- スキーマ: `docs/schemas/artifacts-adapter-summary.schema.json` に準拠
- PR 集約向けの 1 行サマリを提供

JUnit/XML に関する注意
- JUnit XML と並行して正規化 JSON を出力
- XML 解析はコアに持ち込まず、必要ならアダプター/CI で実施
- 例: `junit.xml` と `artifacts/<adapter>/summary.json` を両方アップロード

- Write normalized results to `artifacts/<adapter>/summary.json`.
- Conform to `docs/schemas/artifacts-adapter-summary.schema.json`.
- Provide a one-line summary for PR aggregation.

## JUnit/XML Notes
- Prefer emitting normalized JSON summaries alongside JUnit XML.
- Do not require core to parse XML; keep parsing in adapters/CI if needed.
- Example: upload both `junit.xml` and `artifacts/<adapter>/summary.json`.

## Related templates
- CI.validate-artifacts.snippet.yml — 正規化 JSON/JUnit を AJV で検証する CI 例
- ajv-failures.md — AJV 失敗例とトラブルシューティング
- ajv-validation.md — AJV 検証ガイド
- ci-examples.md — アダプター含む最小CIスニペット
- ltl-suggestions.md — BDD→LTL 候補の warn-only 運用例と CI スニペット
