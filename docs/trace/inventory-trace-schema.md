# Inventory Trace Schema (Draft)

## 目的
- Multi-domain Trace パイプラインに Inventory ドメインを追加するため、Projection/Validation 出力の最小 NDJSON 形式を定義する。
- `pipelines:trace --domain inventory`（想定）の入力として利用し、Envelope 生成時に `summary.trace.domains[]` へ統合できるようにする。

## NDJSON イベントフォーマット
| フィールド | 型 | 必須 | 説明 |
|------------|----|------|------|
| `traceId` | string | ✓ | 複数イベントをまたいで関連付けるトレース ID。Tempo 参照や Envelope 集約に使用する。 |
| `timestamp` | string (ISO8601) | ✓ | イベント発生時刻。Projector 側で並び替えず入力順を保持する。 |
| `type` | string (`projection` \| `allocation` \| `release` \| `validation`) | ✓ | イベント種別。Projection は集計スナップショット、Allocation/Release は差分、Validation は不変条件のチェック結果。 |
| `key` | string | ✓ | イベントのスコープ。`inventory`（集計）または `order-<id>`（予約単位）など。 |
| `state` | object | projection/validation | 在庫状態のスナップショット。最低限 `onHand`, `allocated`, `available` を含める。 |
| `delta` | object | allocation/release | 差分値。`{ "allocated": +/-N }` や `onHand` の補正量を記録する。 |
| `context` | object | 任意 | SKU・予約 ID・補足メタデータ。Grafana/Tempo の属性ラベルと一致させる。 |
| `result` | string (`pass` \| `fail`) | validation | 検証の合否。`fail` の場合は `checks` に違反内容を記録する。 |
| `checks` | object | validation | 各不変条件の評価結果。`allocated_le_onhand` などの真偽値を格納。 |

## イベント種別ごとの意図
- `projection`: Projector が Inventory 集計をスナップショットとして書き出す。`state` を Envelope の `artifacts.projectionPath` に対応させる。
- `allocation`: 予約処理で `allocated` が増減した記録。`delta` と `context.reservationId` で差分を追跡する。
- `release`: 割当解除。`delta.allocated` は負数となり、`state.available` を即座に更新する。
- `validation`: Projector/Validator が不変条件 (`allocated <= onHand`, `onHand >= min`) を評価した結果を記録し、Envelope の `validationPath` と整合させる。

## サンプル
- `samples/trace/inventory/sample.ndjson`

```ndjson
{"traceId":"inventory-trace-1","timestamp":"2025-10-09T00:00:00.000Z","type":"projection","key":"inventory","state":{"onHand":50,"allocated":10,"available":40}}
{"traceId":"inventory-trace-1","timestamp":"2025-10-09T00:05:00.000Z","type":"allocation","key":"order-1001","delta":{"allocated":5},"state":{"onHand":50,"allocated":15,"available":35},"context":{"sku":"SKU-1","reservationId":"res-1001"}}
{"traceId":"inventory-trace-1","timestamp":"2025-10-09T00:10:00.000Z","type":"release","key":"order-1001","delta":{"allocated":-3},"state":{"onHand":50,"allocated":12,"available":38},"context":{"reason":"order-cancelled"}}
{"traceId":"inventory-trace-1","timestamp":"2025-10-09T00:15:00.000Z","type":"validation","key":"inventory","result":"pass","checks":{"allocated_le_onhand":true,"onhand_min":true},"state":{"onHand":50,"allocated":12,"available":38}}
```

## 次のステップ
- `scripts/trace/projector-inventory.mjs`（仮）で上記形式を出力し、`artifacts/trace/inventory/` に保存するフローを整備する。
- `pipelines:trace` へ Inventory ドメインの CLI オプションを追加し、Multi-domain Envelope へ組み込む。
- Grafana 変数 `inventory` を Tempo 属性 `trace.domain=inventory` と関連付けてダッシュボード切り替えを可能にする。
