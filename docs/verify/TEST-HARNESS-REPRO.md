# Test Harness Repro Guide

## 目的
Property / Replay / MBT の失敗を seed/trace ベースで再現するための手順を定義します。

## 生成されるサマリ
- `artifacts/properties/summary.json`
- `artifacts/domain/replay.summary.json`
- `artifacts/mbt/summary.json`
- `artifacts/testing/repro-summary.{json,md}`（CI集約）

最低限の共通キー:
- `seed`
- `traceId`（存在する場合）
- `runs`
- `passed`
- `failed`
- `durationMs`
- `reproducibleCommand`

## ローカル再現
### Property
```bash
node scripts/testing/property-harness.mjs --seed=12345 --runs=50 --focus=pbt-12345
```

### Replay
```bash
REPLAY_INPUT=artifacts/domain/events.json \
REPLAY_OUTPUT=artifacts/domain/replay.summary.json \
REPLAY_SEED=0 \
REPLAY_STRICT=1 \
node scripts/testing/replay-runner.mjs --focus=replay-0
```

### MBT
```bash
node tests/mbt/run.js --seed=12345 --runs=25 --depth=12 --trace-id=mbt-12345
```

## CIでの運用
- ワークフロー: `.github/workflows/testing-ddd-scripts.yml`
- 既定（`enforce-testing` なし）: non-blocking
- `enforce-testing` あり: blocking
- `trace:<id>` ラベル: Property/Replay の focus 実行に利用

## 失敗時の確認ポイント
1. `artifacts/testing/repro-summary.md` の再現コマンドを実行
2. `counterexamplePath` がある場合は該当 JSON を確認
3. `REPLAY_DISABLE` / `REPLAY_ONLY` / `REPLAY_ONHAND_MIN` の設定差分を確認
