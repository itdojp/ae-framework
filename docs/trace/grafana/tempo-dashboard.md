# Grafana/Tempo Playbook for KvOnce Traces

Issue refs: #1036 / #1038 / #1011

## データフロー概要
1. `pnpm pipelines:trace --input samples/trace/kvonce-sample.ndjson` を実行すると、Projection / Validation / TLC の成果物に加え、`artifacts/trace/report-envelope.json` が自動生成される（PR #1103）。
2. Envelope には `summary.trace`、`artifacts[]`（projection / validation / state sequence / replay）、`correlation.runId` などのメタデータが格納される。
3. `pnpm verify:conformance --from-envelope artifacts/trace/report-envelope.json` で Envelope からサマリを再掲できるため、CI 外でも同じ情報を参照できる（PR #1102）。
4. Tempo では `kvonce.*` 属性付きの span を収集する。Grafana ダッシュボードで Envelope と Tempo の両方を参照し、Run 単位での健全性を可視化する。

## Grafana データソース構成
- **Tempo**: `docker/otlp-tempo/` のスタックなどで起動している Tempo を TraceQL モードで参照する。
- **JSON / Static data source**: `artifacts/trace/report-envelope.json` を JSON データソースとして登録し、`summary.*` / `artifacts[]` を取得する。S3 などに保管する場合は Presigned URL を利用する。
- **Optional**: Verify Lite の Envelope (`artifacts/report-envelope.json`) も同じダッシュボードに読み込むと、Lint / Mutation の指標を一望できる。

## 属性マッピング
| Envelope Field | Grafana での用途 | Tempo 側属性 | 備考 |
|----------------|------------------|--------------|------|
| `summary.trace.status` | ステータスカード | `kvonce.validation.valid` | Envelope では文字列、Tempo には boolean としてコピーする。 |
| `summary.trace.projection.events` | イベント件数カード | `kvonce.projection.event_count` | イベント数の急増監視に利用。 |
| `summary.trace.validation.issues` | テーブルの警告行 | - | Envelope のみで保持。Tempo のエラー span と突合せ。 |
| `correlation.runId` | Tempo テンプレート変数 | `kvonce.run_id` | Run 単位でトレースを絞り込む。 |
| `correlation.branch` | ブランチ切替用変数 | `kvonce.branch` | main / feature 毎の比較に活用。 |
| `artifacts[].path` | ダウンロードリンク | `kvonce.artifact_path` | Projection / Validation / TLC summary へのリンク。 |

## 推奨パネル
1. **Trace Summary (Stat)** – データソース: JSON。`summary.trace.status` や `summary.trace.validation.issues` を表示し、status が `valid` 以外なら赤でハイライト。
2. **Trace Count by Branch (Time series)** – データソース: Tempo。`{ kvonce_run_id != '' } | stats count() by kvonce_branch`。
3. **Validation Issues Table** – データソース: Tempo。`{ status.code = 'STATUS_CODE_ERROR' } | fields service.name, status_message, kvonce_run_id`。Data Link で Envelope `artifacts[].path` に飛べるよう設定。
4. **Artifact Download List** – データソース: JSON。`artifacts[].path` をテーブル表示し、S3/GitHub artifact へのリンクを付与。

## ダッシュボードの更新手順
1. `pnpm pipelines:trace --input ...` を実行し、Envelope と Tempo の両方に最新のデータを投入する。
2. Envelope を JSON データソースに再読込させ、Run ID / status が反映されているか確認する。
3. Tempo Explore で `kvonce_run_id = $runId` を検索し、span 属性に `kvonce.validation.valid` などが付与されているかをチェックする。
4. 不整合が見つかった場合は Envelope の `summary.trace.validation.issues` と Tempo のエラー span を突合し、Projection/Validation の成果物（`artifacts[].path`）をダウンロードして調査する。

## Export / Import
- Grafana UI から JSON をエクスポートし、`docs/trace/grafana/tempo-dashboard.json` としてリポジトリ管理することを推奨。
- 将来的には `scripts/trace/export-dashboard.mjs`（TODO）で CI からダッシュボードを自動エクスポートし、差分をレビューできるようにする。

## TODO
- [ ] Verify Lite Envelope を同じダッシュボードに統合し、Mutation/Lint 指標も可視化する。
- [ ] `pipelines:trace` 実行時に Grafana Link パネル向け URL を Envelope の `notes` に追記する。
- [ ] ダッシュボードの export/import スクリプトを `scripts/trace/` 配下に追加し、自動化する。
