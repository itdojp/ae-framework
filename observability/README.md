# Observability

> 🌍 Language / 言語: English | 日本語

- Trace schema: `trace-schema.yaml` defines minimal fields for conformance.
- Emit traces conforming to this schema when integrating runtime checks.

Example event (YAML):

```
traceId: "sess-2025-09-12T10:00:03Z-001"
timestamp: "2025-09-12T10:00:03Z"
actor: "checkout-service"
event: "OrderPlaced"
action: "CreateOrder"
state:
  items: 3
  total: 4200
outcome: success
```

---

## 日本語（概要）

観測可能性（Observability）の最小スキーマを `trace-schema.yaml` に定義しています。実行時の適合性チェックや品質ゲートと統合する際は、このスキーマに準拠したトレース（イベント）を出力してください。

ポイント:
- 必須フィールド: `traceId`, `timestamp`, `actor`, `event`, `action`, `state`, `outcome`
- CI/検証フェーズでは、これらのフィールドを用いた相関・集約を行います

イベント例（YAML）
```
traceId: "sess-2025-09-12T10:00:03Z-001"
timestamp: "2025-09-12T10:00:03Z"
actor: "checkout-service"
event: "OrderPlaced"
action: "CreateOrder"
state:
  items: 3
  total: 4200
outcome: success
```
