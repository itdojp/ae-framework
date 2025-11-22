# Property テスト テンプレート (fast-check 前提)

## 不変条件の例
- Idempotency: 同一 `requestId` は状態を重複変化させない
- Stock never negative: 在庫が 0 未満にならない
- Audit on error: 4xx/5xx で監査イベントが必ず出る

## ジェネレータ方針
- requestId: fc.uuid()
- quantity: fc.integer({ min: 0, max: 5 })
- users: fc.constantFrom('u1','u2','u3')
- inventory seed: fc.array(fc.record({ sku: fc.string(), stock: fc.integer({min:0, max:10}) }), {minLength:1, maxLength:3})

## 実装雛形
```ts
import fc from 'fast-check';
import { app } from '../../src/web-api/app'; // 適宜修正

describe('properties / reservations', () => {
  it('idempotent requests do not double-book', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.uuid(),
        fc.integer({ min: 1, max: 3 }),
        async (requestId, qty) => {
          // arrange
          // act twice with same requestId
          // assert state unchanged on second call
        },
      ),
      { numRuns: 50 },
    );
  });
});
```
