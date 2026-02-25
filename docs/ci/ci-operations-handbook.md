# CI Operations Handbook

最終更新: 2026-02-25

目的: 日次運用で使う確認手順・再実行手順・停止判断を 1 ページで参照できるようにする。

責務境界:
- 方針（Required checks / opt-in）は `docs/ci-policy.md` を正とする
- 本書は「運用手順（運転方法）」のみを扱い、詳細診断は runbook へ委譲する
- 境界表は `docs/ci/ci-doc-boundary-matrix.md` を参照

## 1. 日次オペレーション（開始時）

1. Open PR の失敗チェックを確認する  
   `gh pr list --state open`
2. 失敗/保留ジョブを抽出する  
   `gh pr checks <PR番号>`
3. Required checks のみ確認する  
   `gh pr checks <PR番号> --required`

## 2. 失敗時の標準対応フロー

1. 失敗ジョブのログを取得する  
   `gh run view <runId> --log-failed`
2. 原因を分類する
   - 設定/権限（label・token・permissions）
   - 実装不整合（workflow/script/doc drift）
   - 一時障害（429、network、runner）
3. 修正後、失敗ジョブのみ再実行する  
   `gh run rerun <runId> --failed`

## 3. 代表的な運用ケース

### 3.1 Copilot Review Gate が失敗

- 未解決 thread 数を確認し、未解決が 0 になるまで返信/resolve する
- stale fail が残る場合は fail 側 run を rerun する

### 3.2 Docs Doctest が失敗

- まず `doctest-index` か `doctest-full` かを判別する
- ローカル再現
  - index: `DOCTEST_ENFORCE=1 pnpm run test:doctest:index`
  - full: `DOCTEST_ENFORCE=1 pnpm run test:doctest:full`
- docs-doctest 設定ドリフト検査
  - `node scripts/ci/check-docs-doctest-policy-sync.mjs`

### 3.3 429 / secondary rate limit

- 同一変更を短時間で連続 dispatch しない
- 先に `rerun --failed` を使う
- 必要に応じて `AE_GH_THROTTLE_MS` を引き上げる（既定 250ms）

## 4. 停止・復帰（Fail-safe）

### 4.1 自動化停止（緊急）

- `AE_AUTOMATION_GLOBAL_DISABLE=1`

### 4.2 部分停止

- `AE_CODEX_AUTOPILOT_ENABLED=0`
- `AE_SELF_HEAL_ENABLED=0`
- `AE_COPILOT_AUTO_FIX=0`

### 4.3 復帰

1. 根本原因の修正
2. 停止変数を戻す
3. 対象 workflow を dispatch で段階再開

## 5. 記録テンプレート（Issue/PRコメント）

- 発生時刻（UTC）
- 失敗 workflow/job
- 取得ログ runId
- 実施した修正
- rerun 結果
- 再発防止（必要時）

## 6. 関連ドキュメント

- `docs/ci/ci-doc-boundary-matrix.md`
- `docs/ci-policy.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/pr-automation.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/docs-doctest-policy.md`
- `docs/ci/automation-failure-policies.md`
