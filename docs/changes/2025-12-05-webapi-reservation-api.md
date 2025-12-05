# Web API 予約リポジトリ実装とプロパティテスト整備 (2025-12-05)

## 目的
- Web API の予約エンドポイントをリポジトリ実装に差し替え、在庫・冪等性の挙動を担保する。
- 予約リクエストのバリデーションとエラーレスポンスを整備し、将来の永続化層差し替えに備える。
- プロパティ/統合テストで idempotency と在庫一貫性を自動検証できるようにする。

## 主要変更
- `src/web-api/repository.ts` に ReservationRepository を定義し、拒否ケースもキャッシュする InMemory 実装を追加。返却を判別可能 Union 化。
- `src/web-api/app.ts` をリポジトリ DI に対応し、requestId/sku/quantity のバリデーションと構造化エラー(400/409)を返却。ESM 拡張子・type-only import に対応。
- テスト:
  - `tests/integration/web-api/reservations.test.ts` で成功・冪等・在庫不足・バリデーションをカバー。
  - `tests/property/web-api/reservation.spec.ts` で fc.uuid を用いた requestId 生成、毎ケース新インスタンス生成で汚染防止。
  - `tests/property/web-api/fast-check.config.ts` で FC_WEBAPI_RUNS 等の環境変数で実行回数を調整可能に。

## 影響/注意点
- 既知警告: テスト実行時に MaxListenersExceededWarning が発生（機能影響なし）。抑止はバックログ化。
- CI: 現状 gate/verify-lite 等は緑。Security Analysis の gitleaks ライセンス未設定などはリポジトリ共通課題として別途対応予定。

## 次ステップ
- MaxListeners 警告の抑止策検討（テストセットアップでの setMaxListeners など）。
- Security Analysis のライセンス/スキャン設定を是正し、ノイズのない CI にする。
