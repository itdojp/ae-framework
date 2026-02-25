# Flake Detection Baseline (2026-02-25)

対象: `Flake Stability Schedule`（`flake-detect.yml`）  
収集日時: 2026-02-25 UTC  
収集範囲: 直近 20 run（completed）

## 1. 実行ログ集計（直近）

| 種別 | 件数 | Job実行時間(平均) | Job実行時間(最小〜最大) | 失敗件数 |
| --- | ---: | ---: | ---: | ---: |
| `detect` | 6 | 1.16分 | 1.12〜1.20分 | 0 |
| `maintenance` | 7 | 0.83分 | 0.72〜0.92分 | 7 |
| `retry` | 7 | 0.06分 | 0.03〜0.10分 | 7 |

補足:
- run全体時間は queue 待ちを含むため、`2026-02-20` の1件で 266.87分 の外れ値を確認（job実行時間は 0.83分）。
- 実行時間の評価は run全体ではなく job の started/completed を基準に扱う。

## 2. 失敗理由（代表）

### maintenance
- `Generate maintenance report` ステップで失敗し、後続の report/upload が skipped になる。
- 現象: 報告生成処理の失敗が run 全体 failure へ伝播する。

### retry
- `Select latest failed run (first attempt)` ステップで失敗し、eligibility 判定まで到達しない。
- 現象: 対象 run の探索失敗（API/取得失敗）を hard-fail している。

## 3. 今回の最適化方針

1. detect の実行プロファイルを `quick|standard|thorough` 化して dispatch で切替可能にする。  
2. detect の各 run に timeout を導入し、run 間 sleep を可変化する。  
3. retry の run 選定失敗を soft-fail 化し、`select_reason` を Step Summary に明示する。  
4. maintenance report/list の失敗を warning 化し、運用runの安定性を優先する。  

## 4. 再計測手順

```bash
gh run list --workflow flake-detect.yml --limit 20 --json databaseId,createdAt,updatedAt,conclusion,event,status,url
gh run view <run_id> --json jobs
```

上記を週次で記録し、`docs/ci/automation-slo-mttr.md` の運用観測と合わせて追跡する。
