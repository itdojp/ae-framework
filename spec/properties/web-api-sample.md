# Property テスト サンプル（ドキュメント用）

> リファレンス用の記述例。テスト実装時の出発点として利用。

## 候補プロパティ
- **Idempotency**: 同一 `requestId` で再送しても状態が重複しない
- **Stock never negative**: 在庫が 0 未満にならない
- **Reservation count monotonic**: 同一ユーザーの予約数はキャンセル以外で減少しない
- **Audit emits on failure**: 409/400 などエラー時には必ず監査ログイベントを出す

## ジェネレータのヒント
- requestId: uuid v4
- quantity: 0..5 の整数
- concurrent users: ['u1', 'u2', 'u3']
- inventory seeds: small arrays of {sku, stock}
