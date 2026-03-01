import { Given, When, Then } from '@cucumber/cucumber';

// NOTE: テンプレート。実装時に適宜置き換えてください。

Given('サービスが起動している', async function () {
  // NEXT: app 起動 or ヘルスチェック
});

Given('商品 {string} の在庫が {int} である', async function (sku: string, stock: number) {
  // NEXT: テスト用の在庫初期化
});

When('ユーザー {string} が {string} を {int} 個予約する', async function (userId: string, sku: string, qty: number) {
  // NEXT: POST /reservations を呼ぶ
});

Then('レスポンスは {int} で予約IDを返す', async function (status: number) {
  // NEXT: ステータスとレスポンスボディを検証
});

Then('在庫は {int} になる', async function (expected: number) {
  // NEXT: DB もしくは in-memory state を確認
});
