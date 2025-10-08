# Multi-domain Trace & Refinement Roadmap

Issue refs: #1011 / #997 / #1003

## 目的
- KvOnce で整備した Trace Projector/Validator を、Inventory / Reservation など他ドメインにも転用する。
- Refinement Mapping を増やし、verify:conformance → Tempo ダッシュボードまで一貫した可視化を提供する。
- CI の重いジョブ（mutation / pact / trace）をラベル opt-in で段階導入できるよう、順序立てて整備する。

## 対象ドメイン候補
| ドメイン | 該当 Issue | Trace 重点ポイント | Refinement Mapping TODO |
|----------|------------|---------------------|-------------------------|
| Inventory (在庫) | #1002 | 在庫不足・オーバーアロケーションの検知。`inventory.trace_schema.yaml` を策定。 | KvOnce 同様に `inventory.impl.json` を追加し、TTL / allocate API をマップする。 |
| Reservation (予約) | #1003 | 予約成功/失敗のリトライ、otel span を介したユーザー行動の追跡。 | 既存 BDD シナリオを Trace schema に対応付け、再試行回数を Envelope summary に記録。 |
| EvidenceValidator | #999 | verify-lite で検証された証跡を Trace に反映し、失敗時の差分を可視化。 | `evidence.trace_schema.yaml` を定義し、Spec で確認した証跡と Trace を照合。 |

## 実行ステップ
1. **Trace Schema 定義**
   - `docs/trace/schema/<domain>-trace-schema.md` を作成し、KvOnce で使った表形式テンプレートを流用する。
   - `observability/trace-schema.yaml` は共通フィールドを定義し、ドメイン固有フィールドは `definitions` で拡張する。
2. **Projector/Validator 実装**
   - `scripts/trace/projector-<domain>.mjs` / `validate-<domain>.mjs` を新設し、KvOnce のユニットテスト (`tests/unit/trace/*`) を写経。 
   - テストデータは `samples/trace/<domain>-sample.ndjson` に追加する。
3. **Envelope 拡張**
   - 各ドメインの Projection/Validation Summary を `pipelines:trace` に登録し、`summary.trace.domains[]` の配列として集約する。
   - Step Summary では `Trace:` の配下にドメイン名を添えて結果を表示する。
4. **Dashboard 連動**
   - Grafana では `kvonce.*` に倣い `inventory.*`, `reservation.*` といった属性を付与する。
   - Tempo Dashboard の JSON を `docs/trace/grafana/<domain>-dashboard.json` にバージョン管理する。

## CI 連携イテレーション
| フェーズ | 追加ジョブ | 条件 | 出力 |
|---------|------------|------|------|
| Phase 1 | `pipelines:trace --skip-replay` (KvOnce) | `run-trace` ラベル | Projection / Validation / Envelope を artifacts 化。 |
| Phase 2 | `pipelines:trace --input samples/trace/inventory-sample.ndjson` | `run-trace-inventory` ラベル | Inventory Schema と Refinement Mapping を検証。 |
| Phase 3 | `pipelines:trace` (Reservation) + `verify:conformance` | nightly | Tempo ダッシュボードに各ドメインの成功率・リトライ回数を集約。

## 次のアクション
- [ ] Inventory ドメインの Trace schema とサンプル NDJSON を追加する。
- [ ] Projector/Validator のユニットテスト雛形を `tests/unit/trace/inventory/*.test.ts` に作成する。
- [ ] `pipelines:trace` をドメイン引数対応に拡張し、`--domain inventory` のように切り替えられるようにする。
- [ ] Tempo ダッシュボード JSON をエクスポートし、`docs/trace/grafana/tempo-dashboard.json` として保存する。
