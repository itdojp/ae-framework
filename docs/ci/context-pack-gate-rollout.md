# Context Pack Gate Rollout（non-blocking -> blocking）

Issue: #2258

## 1. 目的
圏論的メタモデル検証（Context Pack validator群）の CI 運用を、non-blocking から blocking へ段階導入する。

## 2. 現状棚卸し（non-blocking 対象と依存ジョブ）

一次情報:
- `.github/workflows/context-pack-quality-gate.yml`
- `scripts/context-pack/run-e2e-fixture.mjs`
- `scripts/ci/context-pack-gate-observability.mjs`

| ジョブ/ステップ | 依存 | 既定モード | blocking 化トリガー |
| --- | --- | --- | --- |
| `gate` | なし | report-only 判定 | `enforce-context-pack` ラベル / `CONTEXT_PACK_ENFORCE_MAIN=1` / dispatch strict |
| `Run Context Pack dependency boundary checks` | `gate` | report-only（違反は warn 出力） | `gate.strict == true` のとき違反で fail |
| `context-pack-e2e` | `gate` | non-blocking (`continue-on-error`) | `gate.strict == true` のとき blocking |
| `Observe rollout metrics` | `context-pack-e2e` 内 | non-blocking | なし（常に観測のみ） |

## 3. 観測指標（判定基準）

観測期間: 直近 14 日（初期値）

- 失敗率（`failureRatePercent`）
  - 式: `failedRuns / totalRuns * 100`
  - 合格基準: `<= 5%`
- 失敗再現率（`reproductionRatePercent`）
  - 式: 「同一 SHA の複数 run のうち、初回失敗後に再度失敗した割合」
  - 合格基準: `>= 80%`（失敗が再現できる = 診断容易）
- MTTR（`mttr.meanMinutes`）
  - 式: 同一ブランチで失敗開始から次の成功までの平均復旧時間
  - 合格基準: `<= 120 分`
- サンプル数
  - 合格基準: `totalRuns >= 20`

実測は次コマンドで生成する。

```bash
pnpm -s run ci:context-pack:observe -- \
  --repo itdojp/ae-framework \
  --workflow-id context-pack-quality-gate.yml \
  --days 14 \
  --output-json artifacts/context-pack/context-pack-gate-observability.json \
  --output-md artifacts/context-pack/context-pack-gate-observability.md
```

## 4. 段階導入手順

1. **Phase A（既定）**
   - PR/Push で `context-pack-e2e` を実行し、report-only で観測する。
2. **Phase B（PR限定 strict）**
   - 対象 PR に `enforce-context-pack` を付与し、blocking として運用する。
3. **Phase C（main strict）**
   - Repository Variable `CONTEXT_PACK_ENFORCE_MAIN=1` を設定し、main で常時 blocking 化する。
4. **Phase D（Branch Protection）**
   - Required checks に `context-pack-e2e` を追加して merge gate に組み込む。

## 5. ロールバック条件と手順

### ロールバック条件
- 失敗率が 5% を連続 3 日で超過
- MTTR 平均が 120 分を連続 3 日で超過
- `unresolvedFailureStreaks > 0` が 24 時間以上継続

### ロールバック手順
1. Branch protection で `context-pack-e2e` の Required を一時解除
2. `CONTEXT_PACK_ENFORCE_MAIN=0` に戻す
3. PR 側は `enforce-context-pack` ラベルを外す
4. 原因修正後、Phase B から再開

## 6. 運用メモ

- E2E fixture は `fixtures/context-pack/e2e` を SSOT とする。
- 実行レポートは `artifacts/context-pack/` 配下に保存される。
- 依存境界チェックのレポートは `artifacts/context-pack/deps-summary.json` / `artifacts/context-pack/deps-summary.md` として保存される。
- 観測レポート JSON/Markdown は同ディレクトリに出力され、PR Step Summary にも転記される。
