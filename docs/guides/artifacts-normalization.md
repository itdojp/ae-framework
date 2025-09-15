# Artifacts Normalization Policy

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

機械可読な成果物は JSON/JUnit に統一し、`docs/schemas/` のスキーマに準拠します。アダプター要約（`artifacts/*/summary.json`）、フォーマル要約（`formal/summary.json`）、プロパティ要約（`artifacts/properties/summary.json`）では可能な限り `traceId` を含めます。

- Store machine-readable results as JSON and JUnit only.
- Paths:
  - `artifacts/*/summary.json` for adapters
  - `formal/summary.json` for formal verification
  - `artifacts/properties/summary.json` for property tests
- Conform to schemas in `docs/schemas/`.
- Include `traceId` wherever applicable.
