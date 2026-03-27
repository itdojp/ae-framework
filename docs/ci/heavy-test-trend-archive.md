---
docRole: ssot
lastVerified: '2026-03-27'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Heavy Test Trend Archive Requirements

This document defines archival requirements for heavy-test trend outputs and their scheduled operation model. / このドキュメントは、heavy test trend 出力のアーカイブ要件と、スケジュール運用モデルを定義します。

Primary sources / 一次情報:
- workflow: `.github/workflows/ci-extended.yml`
- trend comparison: `scripts/pipelines/compare-test-trends.mjs`
- archive helper: `scripts/pipelines/sync-test-results.mjs`
- summary helper: `scripts/pipelines/render-heavy-trend-summary.mjs`

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
- Track heavy test outputs such as Mutation quick, Property harness, and MBT smoke on a Nightly basis to detect performance or quality regressions early.
- Reuse `.cache/test-results` while preserving `reports/heavy-test-trends.json` as a history input for later visualization and analysis.
- Define the next infrastructure step for the CI stability / measurement track originally tracked in Issue `#1160`, especially the `#1005 Phase 3` line of work.

### 2. Current implementation status (as of 2025-10-28 / PR #1192 merge point)
- `ci-extended.yml` currently handles heavy test artifacts in this order:
  1. restore `.cache/test-results` through `actions/cache/restore`
  2. prepare the baseline in `.cache/test-results-baseline` with `node scripts/pipelines/sync-test-results.mjs --restore` and `--snapshot`
  3. run heavy suites (integration / property / MBT / mutation)
  4. generate baseline-vs-current Markdown / JSON through `node scripts/pipelines/compare-test-trends.mjs` and write `reports/heavy-test-trends.json`
  5. store the latest results back through `node scripts/pipelines/sync-test-results.mjs --store`
  6. upload the `heavy-test-trends` artifact with 7-day retention through `actions/upload-artifact` (only for non-PR events)
- Scheduled execution also saves heavy trend snapshots to `reports/heavy-test-trends-history/<timestamp>.json` and publishes the `heavy-test-trends-history` artifact with 30-day retention.
- `heavy-test-trends` and `heavy-test-trends-history` artifacts are therefore available only for non-PR paths. `pull_request` runs do not upload them.
- `.cache/test-results` uses event-specific cache keys:
  - Pull Request / Push: `ci-heavy-${ runner.os }-${ github.sha }`
  - Scheduled: `ci-heavy-${ runner.os }-schedule`
- `reports/heavy-test-trends.json` keeps only the latest single-run comparison.
- `.cache/test-results-baseline` overwrites the latest baseline snapshot and does not preserve multiple days of history.

### 3. Known gaps
- Trend history is effectively limited to the rolling artifact retention window. There is no built-in long-term retention beyond artifact expiry.
- Multi-snapshot summaries exist for scheduled runs through `render-heavy-trend-summary.mjs`, but there is still no always-on dashboard or external time-series store for long-horizon analysis.
- Reuse is still centered on Step Summary Markdown and JSON payloads. CSV export, BI ingestion, and other secondary analysis paths are not yet standardized.

### 4. Requirements for Nightly archival

#### 4.1 Functional requirements
1. **History persistence**
   - Save a dated copy of `reports/heavy-test-trends.json` for every Nightly / scheduled run.
   - Candidate destinations:
     - (A) in-repo history files such as `reports/heavy-test-trends/history/2025-10-28.json`
     - (B) GitHub Artifacts such as `heavy-test-trends-YYYYMMDD.json` with retention >= 30 days
     - (C) external storage such as S3 / GCS / Supabase
   - The current initial preference is (B), so operators can download history without adding new infrastructure.
2. **Baseline operation**
   - Scheduled runs should continue sharing `.cache/test-results` through `ci-heavy-${ runner.os }-schedule`, so the previous Nightly result becomes the baseline.
   - Pull Request / Push must keep SHA-based keys to prevent collisions across event types.
3. **Metadata enrichment**
   - Ensure the archived JSON can be correlated with actual keys already emitted by `compare-test-trends.mjs`:
     - `generatedAt` (timestamp)
     - `context.sha` (commit)
     - `context.ref` (branch)
     - `context.runId` / `context.runNumber`
     - `context.workflow`
   - Additional metadata can still be added inside `compare-test-trends.mjs` or by wrapping the JSON in the scheduled workflow, but downstream tools should treat the mapping above as the baseline contract.
4. **Notification / visualization hooks**
   - Design hooks for issue / Slack escalation when deltas cross thresholds, for example mutation score < 95% or MBT violations > 0.
   - Prepare NDJSON or CSV conversion for future Observable / Grafana integration.

#### 4.2 Non-functional requirements
1. **Retention**
   - Keep at least 30 days of history and delete older artifacts automatically.
   - If operators need manual download, document the process in the related runbook.
2. **Rerun tolerance**
   - Define a file naming rule that supports overwrite or append on reruns, typically including `RUN_ID` for workflow-dispatch paths.
3. **Cost / duration**
   - Reuse the existing heavy suites from `ci-extended.yml`.
   - Prefer reusing `ci-extended.yml` through `workflow_call` or `uses` rather than introducing a separate heavy-only Nightly path.
4. **Reproducibility**
   - Keep a local reproduction path based on `node scripts/pipelines/sync-test-results.mjs --restore` followed by `compare-test-trends.mjs`, producing the same output shape as Nightly.

### 5. Nightly flow proposal (rough draft)
1. Call `ci-extended.yml` from `nightly.yml` through `workflow_call`, targeting the latest `main` commit.
2. After the heavy suites finish, add archive-only steps for scheduled execution:
   ```yaml
   - name: Archive heavy test trend (JSON)
     run: |
       DATE=$(date -u +'%Y-%m-%dT%H-%M-%SZ')
       mkdir -p reports/heavy-test-trends-history
       cp reports/heavy-test-trends.json "reports/heavy-test-trends-history/${DATE}.json"
   - name: Upload heavy trend history
     uses: actions/upload-artifact@v4
     with:
       name: heavy-test-trends-history
       path: reports/heavy-test-trends-history/
       retention-days: 30
   ```
3. Later, aggregate the JSON files into `heavy-test-trends.ndjson` and expose them to Observable or Grafana.

### 6. Reuse policy for `ci-extended`

| Option | Summary | Benefit | Concern |
| --- | --- | --- | --- |
| A. Add `workflow_call` to existing `ci-extended.yml` | Extend `on:` to include `workflow_call` and let Nightly use `uses: ./.github/workflows/ci-extended.yml` | Minimal change, single logic source | `github.event_name` becomes `workflow_call`, so label-based conditions need review |
| B. Extract a dedicated reusable workflow such as `ci-extended-job.yml` | Keep existing triggers untouched and call the extracted file from Nightly | Lower risk to current PR / Push behavior | Ongoing sync cost and duplication risk |
| C. Convert to a composite action | Move the reusable execution path into `./.github/actions/run-ci-extended` | Simpler workflow files | Harder logging and condition handling, plus env compatibility adjustments |

The current minimum-change recommendation is option A. If Nightly uses `workflow_call`, add inputs that force heavy execution and enable archival, then make `Determine execution flags` set `RUN_EXTENDED=true` for that path.

### 7. Metadata model
- `compare-test-trends.mjs` should expose `generatedAt` plus GitHub Actions context such as runId, runNumber, sha, and ref.
- Scheduled `reports/heavy-test-trends-history/<timestamp>.json` files should carry the same context so downstream tooling can correlate runs.
- `render-heavy-trend-summary.mjs` already acts as the summary PoC. It scans the history directory and writes recent snapshots to stdout, `reports/heavy-test-trends-history/summary.md`, and the Step Summary.
- The scheduled Slack notification step reads `summary.json` and decides whether to alert based on Warning / Critical thresholds.

### 8. Candidate next steps
1. Build a visualization PoC using Observable Notebook or generated Markdown reports.
2. Implement notification thresholds defined in `docs/ci/heavy-test-alerts.md`.
3. Decide whether manual dispatch or non-Nightly runs should also archive history.
4. Define rotation and size-control rules for `.cache/test-results-baseline`.

## 日本語

### 1. 目的
- Mutation quick / Property harness / MBT smoke などの heavy テスト結果を Nightly で継続的に追跡し、性能・品質退行を早期検知する。
- `.cache/test-results` に蓄えた成果物を再利用しつつ、`reports/heavy-test-trends.json` を履歴として収集・可視化できるようにする。
- Issue `#1160` フェーズD（特に `#1005 Phase3`）で掲げている「CI 安定化・計測強化」の次ステップとして、基盤要件を整理する。

### 2. 現状の実装 (2025-10-28 時点 / PR #1192 マージ時点)
- `ci-extended.yml` は以下の流れで heavy テスト成果物を扱う（PR #1192）:
  1. `actions/cache/restore` で `.cache/test-results` を復元
  2. `node scripts/pipelines/sync-test-results.mjs --restore` と `--snapshot` で baseline (`.cache/test-results-baseline`) を準備
  3. heavy スイート（integration/property/MBT/mutation）を実行
  4. `node scripts/pipelines/compare-test-trends.mjs` で baseline vs current の Markdown/JSON を生成 (`reports/heavy-test-trends.json`)
  5. `node scripts/pipelines/sync-test-results.mjs --store` で最新結果をキャッシュへ格納
  6. `actions/upload-artifact` で `heavy-test-trends` アーティファクトを 7 日保持（Pull Request ではアップロードされない）
- スケジュール実行時は heavy テストトレンドを `reports/heavy-test-trends-history/<timestamp>.json` に保存し、アーティファクト `heavy-test-trends-history`（保持 30 日）として公開する。
- `heavy-test-trends` / `heavy-test-trends-history` アーティファクトは non-PR path でのみ生成され、`pull_request` 実行では取得できない。
- `.cache/test-results` はイベントに応じたキャッシュキーを使用し、Pull Request / Push では `ci-heavy-${ runner.os }-${ github.sha }`、スケジュール実行では `ci-heavy-${ runner.os }-schedule` を用いる。
- `reports/heavy-test-trends.json` は単一ランの比較結果のみ保持（最新 1 件）。
- Baseline は `.cache/test-results-baseline` 内で最新スナップショットを上書きするため、複数日分は残らない。

### 3. 既知の課題
- 履歴は artifact の保持期間に依存しており、artifact expiry を超える長期保管は built-in では提供されていない。
- `render-heavy-trend-summary.mjs` による複数スナップショット要約はあるが、常設ダッシュボードや外部時系列ストアは未整備である。
- 可視化手段は引き続き Step Summary の Markdown と JSON が中心であり、CSV や BI 連携などの二次利用フローは標準化されていない。

### 4. Nightly アーカイブに必要な要件

#### 4.1 機能要件
1. **履歴保存**
   - Nightly / schedule 実行ごとに `reports/heavy-test-trends.json` のコピーを日付付きで保存する。
   - 保存先候補:
     - (A) リポジトリ内ヒストリーファイル（例: `reports/heavy-test-trends/history/2025-10-28.json` を生成してコミット/PR）
     - (B) GitHub Artifacts（例: `heavy-test-trends-YYYYMMDD.json`, retention >= 30 日）
     - (C) 外部ストレージ（S3 / GCS / Supabase 等）に API 経由でアップロード
   - 初期段階では (B) を優先し、手動ダウンロード可能な形で履歴を確保する。将来 (A) で差分 PR を自動作成する案も検討する。
2. **Baseline 運用**
   - スケジュール実行時は `.cache/test-results` を `ci-heavy-${ runner.os }-schedule` で共有し、前回 Nightly の成果物を baseline として復元できる。
   - Pull Request / Push は従来どおりコミット SHA ベースのキーを利用し、異なるイベント間での衝突を防ぐ。
3. **メタデータ付与**
   - JSON 出力に実行コンテキストのメタ情報を付与し、履歴データ間の参照性を高める。最低限、現行実装に合わせて次のキーを前提とする:
     - `generatedAt`（`timestamp` に相当）
     - `context.sha`（`commit` に相当）
     - `context.ref`（`branch` に相当）
     - `context.runId` / `context.runNumber`
     - `context.workflow`
   - 追加のメタデータが必要な場合は、`compare-test-trends.mjs` に追加フィールドを渡すか、Nightly workflow 側でラップ JSON を生成する。
4. **通知 / 可視化フック**
   - Δ が閾値を超えた場合に issue / Slack 通知を出す設計を検討する（例: mutation score < 95%、MBT violations > 0 など）。
   - 将来的に Observable / Grafana での可視化を想定し、NDJSON または CSV への変換スクリプトを用意する。

#### 4.2 非機能要件
1. **保持期間**
   - 最低 30 日分の履歴を保持し、古いアーティファクトは自動削除する。手動でダウンロードする場合は関連 runbook に手順を記載する。
2. **再実行耐性**
   - rerun 時も同じ日付ファイルを上書き・追記できるよう、workflow dispatch で `RUN_ID` を含めたファイル名規則を定義する。
3. **コスト / 時間**
   - 既存の CI Extended と同じ heavy テストを使う。
   - Nightly では `ci-extended.yml` を `workflow_call`（または `uses`）で再利用し、追加の job 時間を最小化する。
4. **再現性**
   - 開発者がローカルで `node scripts/pipelines/sync-test-results.mjs --restore` の後に `compare-test-trends.mjs` を実行し、Nightly と同じ出力形式で再現できるようにする。

### 5. Nightly フロー案（ラフ案）
1. `nightly.yml` から `workflow_call` で `ci-extended.yml` を再利用する（main 最新コミットを対象に実行）。
2. heavy suite 完了後に以下を追加する（スケジュール実行のみ archive する条件付き）:
   ```yaml
   - name: Archive heavy test trend (JSON)
     run: |
       DATE=$(date -u +'%Y-%m-%dT%H-%M-%SZ')
       mkdir -p reports/heavy-test-trends-history
       cp reports/heavy-test-trends.json "reports/heavy-test-trends-history/${DATE}.json"
   - name: Upload heavy trend history
     uses: actions/upload-artifact@v4
     with:
       name: heavy-test-trends-history
       path: reports/heavy-test-trends-history/
       retention-days: 30
   ```
3. 将来: 上記 JSON をまとめた `heavy-test-trends.ndjson` を生成し、Grafana / Observable Notebook に連携する。

### 6. `ci-extended` 再利用方針の検討

| 方針 | 概要 | メリット | 懸念点 |
|------|------|-----------|--------|
| A. `workflow_call` を既存 `ci-extended.yml` に追加 | `on: [pull_request, push, schedule, workflow_dispatch, workflow_call]` とし、Nightly から `uses: ./.github/workflows/ci-extended.yml` で呼び出す | 単一ファイルでロジックを共有できる。Nightly 側は inputs / secrets を渡すだけで済む | `workflow_call` 実行時の `github.event_name` は `workflow_call` になるため、ラベルベースの条件判定を見直す必要がある |
| B. `ci-extended.yml` の job を `workflow_call` 専用ファイルに切り出す（例: `ci-extended-job.yml`） | 既存 `ci-extended.yml` は従来トリガーのまま、Nightly からは切り出した再利用 workflow を呼ぶ | PR / Push 等の既存挙動に影響しない | 切り出し後の同期コストが発生し、重複更新リスクがある |
| C. Composite Action 化 | `./.github/actions/run-ci-extended` に処理をまとめ、既存 `ci-extended` や Nightly から参照する | ワークフローファイルの記述を簡素化できる | `run` ステップのロギングが追いづらくなり、環境変数や `if` 条件の互換性を再調整する必要がある |

初期案では A（`workflow_call` を追加）を採用するのが最小の修正で済む。Nightly 実行時は `workflow_call` に渡す inputs として「heavy テスト実行を必ず有効化」「アーカイブをオンにするフラグ」などを追加し、`Determine execution flags` ステップで `RUN_EXTENDED=true` を強制する分岐を設ける。

### 7. メタデータ
- `compare-test-trends.mjs` は `generatedAt` に加え、GitHub Actions の runId / runNumber / sha / ref などを `context` フィールドに自動付与する。
- スケジュール実行で生成された `reports/heavy-test-trends-history/<timestamp>.json` には同じ `context` 情報が含まれるため、後段で履歴解析する際に run 単位で突合できる。
- `scripts/pipelines/render-heavy-trend-summary.mjs` は履歴ディレクトリを走査し、直近スナップショットを Markdown として標準出力・`reports/heavy-test-trends-history/summary.md`・Step Summary に出力する PoC として機能する。
- スケジュール実行の Slack 通知ステップでは上記 `summary.json` を参照し、Warning / critical 判定をもとにチャンネルへ連絡する。

### 8. 次ステップ候補
1. 収集データの可視化 PoC（Observable Notebook または static Markdown レポート生成）。
2. `docs/ci/heavy-test-alerts.md` に沿った通知閾値の実装。
3. Nightly 以外（手動 dispatch など）で履歴保存を有効化するかの検討。
4. `.cache/test-results-baseline` のローテーションやサイズ制御ルール整備。
