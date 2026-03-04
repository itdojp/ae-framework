# Local Stack Foundation 比較記録テンプレート（最小）

このテンプレートは `#2409` のローカルスタック基盤確認向けに限定し、詳細分析（長時間負荷・統計比較・回帰判定）は `#2414` 側のPoC docsに委譲する。

## メタ情報

| 項目 | 値 |
| --- | --- |
| 計測ID | `YYYYMMDD-<owner>-local-stack` |
| 計測日 | |
| 実施者 | |
| ブランチ / コミット | |
| OS / CPU / メモリ | |
| Docker / Compose バージョン | |

## 実施条件

| 項目 | 値 |
| --- | --- |
| `.env` 差分 | なし / あり（内容を記載） |
| 事前状態 | `docker compose down --volumes` 実施有無 |
| 同時稼働コンテナ | |
| 計測回数 | 1回以上（推奨3回） |

## 計測結果（最小）

| 指標 | Run1 | Run2 | Run3 | 備考 |
| --- | --- | --- | --- | --- |
| `docker compose up -d` 完了時間 (秒) | | | | |
| NATS `/healthz` 応答 (ms) | | | | |
| PostgreSQL `select now()` 成功可否 | | | | |
| MinIO `/minio/health/live` 応答 (ms) | | | | |
| `docker compose down` 完了時間 (秒) | | | | |

## ログ参照

- `docker compose ps`
- `docker compose logs --no-color nats postgres minio minio-init`
- 追加ログ:

## 所見

- 成功/失敗:
- 既知制約:
- 次アクション:
