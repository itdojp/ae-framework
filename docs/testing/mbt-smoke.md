---
docRole: ssot
lastVerified: 2026-03-11
owner: testing-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# MBT Smoke Harness

> 🌍 Language / 言語: 日本語 / English

Verify Lite フェーズで利用できる軽量なモデルベーステスト（MBT）ハーネスを追加しました。小さな在庫管理モデルをランダム探索し、インベントリが破綻しないこと（在庫数が負にならない、総量が保存される）を検証します。

## 使い方

```text
pnpm test:mbt              # 既定で 25 シナリオ / 深さ 12
pnpm test:mbt --runs=50    # シナリオ数を増やす
pnpm test:mbt --seed=42    # 再現性のある実行
pnpm test:mbt --depth=20   # 1シナリオあたりの遷移数を調整
```

- 成功時: `artifacts/mbt/summary.json` に実行内容と final state が出力されます。
- 失敗時: `violations` に破綻内容が記録され、終了コード 1 で停止します。

## Summary JSON の構造例

```text
{
  "seed": 1728979200000,
  "runs": 25,
  "depth": 12,
  "violations": 0,
  "scenarios": [
    {
      "index": 1,
      "steps": [
        { "action": "reserve", "applied": true, "reason": null },
        { "action": "ship", "applied": true, "reason": null }
      ],
      "final": { "available": 4, "reserved": 0, "shipped": 1 },
      "violations": []
    }
  ]
}
```

Verify Lite ワークフローに統合することで、プロパティテスト・Pact と同様に MBT のスモーク結果を Step Summary へ掲載できます（Issue #1003）。
