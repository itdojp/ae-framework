---
docRole: derived
canonicalSource:
- schema/counterexample.schema.json
- docs/quality/ASSURANCE-MODEL.md
lastVerified: '2026-04-06'
---
# Counterexample → GWT Format (Spec & Examples)

> 🌍 Language / 言語: English | 日本語

---

## English

### Purpose
- Provide both a short human-readable GWT form and a machine-readable JSON form for counterexamples consumed by `ae fix`.
- Keep the doc aligned with the legacy `formal/summary.json` counterexample shape and the derived `artifacts/formal/gwt.summary.json` output produced by `scripts/formal/format-counterexamples.mjs`.

### Short GWT (example)
```text
Given {"onHand":10}
When {"command":"allocate","qty":12}
Then invariant "allocated <= onHand" fails
```

### 機械可読 JSON
- Source location:
  - embedded in the legacy `formal/summary.json`
- Derived location:
  - `scripts/formal/format-counterexamples.mjs` can derive `artifacts/formal/gwt.summary.json`

```json
{
  "items": [
    {
      "property": "allocated <= onHand",
      "gwt": "Given {\"onHand\":10}\nWhen {\"command\":\"allocate\",\"qty\":12}\nThen invariant \"allocated <= onHand\" fails",
      "json": {
        "given": { "onHand": 10 },
        "when": { "command": "allocate", "qty": 12 },
        "then": { "violated": "allocated <= onHand" }
      }
    }
  ]
}
```

## 日本語

### 目的
- 反例を、人間向けの短い GWT 形式と、`ae fix` が読める機械可読 JSON の両方で扱えるようにします。
- legacy `formal/summary.json` の反例形式と、`scripts/formal/format-counterexamples.mjs` が生成する `artifacts/formal/gwt.summary.json` に整合させます。

### 短い GWT（例）
```text
Given {"onHand":10}
When {"command":"allocate","qty":12}
Then invariant "allocated <= onHand" fails
```

### 機械可読 JSON
- 元の格納先:
  - legacy `formal/summary.json` に埋め込まれます
- 派生出力先:
  - `scripts/formal/format-counterexamples.mjs` により `artifacts/formal/gwt.summary.json` を生成できます

```json
{
  "items": [
    {
      "property": "allocated <= onHand",
      "gwt": "Given {\"onHand\":10}\nWhen {\"command\":\"allocate\",\"qty\":12}\nThen invariant \"allocated <= onHand\" fails",
      "json": {
        "given": { "onHand": 10 },
        "when": { "command": "allocate", "qty": 12 },
        "then": { "violated": "allocated <= onHand" }
      }
    }
  ]
}
```
