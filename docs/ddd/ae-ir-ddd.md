# AE-IR: Optional DDD Fields (Backward-Compatible)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

AE-IR に後方互換な DDD フィールド（境界づけられたコンテキスト、集約、ドメインイベント、ユビキタス用語）をオプションとして追加する提案です。形式仕様/BDD リント/契約・リプレイと連携します。

Summary
- Extend AE-IR with optional DDD fields to strengthen ubiquitous language and aggregate invariants while keeping the core thin and adapters external.

Fields
- `boundedContext: string`
- `aggregate: { name: string; root: string; invariants: string[] }`
- `domainEvents: { name: string; payload: Record<string, unknown>; occursOn: string }[]`
- `ubiquitousTerms: string[]`

Compatibility
- All fields are optional; existing AE-IR documents remain valid.

JSON Schema (excerpt)
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "type": "object",
  "properties": {
    "boundedContext": { "type": "string" },
    "aggregate": {
      "type": "object",
      "properties": {
        "name": { "type": "string" },
        "root": { "type": "string" },
        "invariants": { "type": "array", "items": { "type": "string" } }
      },
      "additionalProperties": false
    },
    "domainEvents": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "name": { "type": "string" },
          "payload": { "type": "object", "additionalProperties": true },
          "occursOn": { "type": "string" }
        },
        "required": ["name"],
        "additionalProperties": false
      }
    },
    "ubiquitousTerms": { "type": "array", "items": { "type": "string" } }
  }
}
```

Consumption Plan
- Formal presets: expand `aggregate.invariants[]` to TLA+/Alloy constraints (#410).
- BDD lint: restrict `When` to aggregate root commands (#410).
- Contracts & replay: generate Zod contracts and replay fixtures from `domainEvents[]` (#411).

Examples
- See `examples/inventory/` samples and `docs/schemas/domain-events.schema.json`.
