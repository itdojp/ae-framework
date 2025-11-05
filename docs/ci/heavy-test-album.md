# Heavy Test Trend Visualization PoC

## サンプルデータ (2025-10-30T07:00:00Z)
```json
{
  "generatedAt": "2025-10-30T07:00:00Z",
  "context": {
    "runId": "1001",
    "runNumber": "50",
    "sha": "deadbeefdeadbeef",
    "ref": "refs/heads/main"
  },
  "entries": [
    {
      "label": "Mutation quick",
      "metrics": {
        "mutationScore": {
          "baseline": 99.5,
          "current": 99.1,
          "delta": -0.4
        }
      }
    },
    {
      "label": "MBT harness",
      "metrics": {
        "violations": {
          "baseline": 0,
          "current": 0,
          "delta": 0
        }
      }
    }
  ]
}
```

## Markdown レポート案
| Snapshot | Mutation Score | Δ | MBT Violations | Notes |
|----------|----------------|---|----------------|-------|
| 2025-10-30T07:00:00Z | 99.1 | -0.4 | 0 | steady |

> 今後: Observable Notebook に読み込んでヒートマップ化する計画。
