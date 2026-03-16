---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-03-16'
---
# Artifacts Normalization Policy

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

機械可読な成果物は JSON/JUnit に統一し、`docs/schemas/` のスキーマに準拠します。アダプター要約（`artifacts/*/summary.json`）、フォーマル要約（`artifacts/formal/formal-summary-v1.json`, `artifacts/formal/formal-summary-v2.json`）、プロパティ要約（`artifacts/properties/summary.json`）では可能な限り `traceId` を含めます。

- Store machine-readable results as JSON and JUnit only.
- Paths:
  - `artifacts/*/summary.json` for adapters
  - `artifacts/formal/formal-summary-v1.json` and `artifacts/formal/formal-summary-v2.json` for formal verification
  - `artifacts/properties/summary.json` for property tests
- Conform to schemas in `docs/schemas/`.
- Include `traceId` wherever applicable.

## JSON Schema 2020-12 policy / 運用方針

- `docs/schemas/` と `schema/` の JSON Schema は 2020-12 を前提とし、`$schema` を削除しない。
- Ajv の 2020-12 メタスキーマを手動登録して検証する（NodeNext では `ajv/dist/2020` の直接 import が解決しづらいため）。
- メタスキーマ登録に失敗した場合は、`ajv` の依存解決と `dist/refs/json-schema-2020-12` の存在を確認する。
- Ajv2020 を正式採用する方針は #1508 で検討中。

- JSON Schemas in `docs/schemas/` and `schema/` target 2020-12 and should keep `$schema`.
- Validation uses Ajv with manually registered 2020-12 meta schemas (NodeNext cannot reliably resolve `ajv/dist/2020` imports).
- If meta schema registration fails, verify the `ajv` dependency and the `dist/refs/json-schema-2020-12` files.
- The long-term Ajv2020 adoption plan is tracked in #1508.
