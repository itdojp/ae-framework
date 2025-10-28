# Heavy Test Trend Archive Requirements

## 目的
- Mutation quick / Property harness / MBT smoke などの heavy テスト結果を Nightly で継続的に追跡し、性能・品質退行を早期検知する。
- `.cache/test-results` に蓄えた成果物を再利用しつつ、`reports/heavy-test-trends.json` を履歴として収集・可視化できるようにする。
- ISSUE #1160 フェーズD（特に #1005 Phase3）で掲げている「CI 安定化・計測強化」の次ステップとして、基盤要件を整理する。

## 現状の実装 (2025-10-28 時点)
- `ci-extended.yml` は以下の流れで heavy テスト成果物を扱う（PR #1192）:
  1. `actions/cache/restore` で `.cache/test-results` を復元
  2. `node scripts/pipelines/sync-test-results.mjs --restore` と `--snapshot` で baseline (`.cache/test-results-baseline`) を準備
  3. heavy スイート（integration/property/MBT/mutation）を実行
  4. `node scripts/pipelines/compare-test-trends.mjs` で baseline vs current の Markdown/JSON を生成 (`reports/heavy-test-trends.json`)
  5. `node scripts/pipelines/sync-test-results.mjs --store` で最新結果をキャッシュへ格納
  6. `actions/upload-artifact` で `heavy-test-trends` アーティファクトを 14 日保持
- `reports/heavy-test-trends.json` は単一ランの比較結果のみ保持（最新 1 件）。長期履歴は別途保管されない。
- Baseline は `.cache/test-results-baseline` 内で最新スナップショットを上書きするため、複数日分は残らない。

## 既知の課題
- 「直近ランとの差分」は把握できるが、「週次・月次トレンド」が追跡できない。
- Nightly / Scheduled 実行で `heavy-test-trends` アーティファクトをダウンロードしない限り、過去結果が失われる。
- `.cache/test-results` のキーが `ci-heavy-${ runner.os }-${ github.sha }` のため、main の連続実行では新しいキャッシュが毎回作成され、履歴が散逸する。
- 可視化手段が Step Summary の Markdown と JSON のみであり、ダッシュボードや CSV などの二次利用が想定されていない。

## Nightly アーカイブに必要な要件

### 機能要件
1. **履歴保存**  
   - Nightly / schedule 実行ごとに `reports/heavy-test-trends.json` のコピーを日付付きで保存する。  
   - 保存先候補:  
     - (A) リポジトリ内ヒストリーファイル（例: `reports/heavy-test-trends/history/2025-10-28.json` を生成してコミット/PR）  
     - (B) GitHub Artifacts (e.g. `heavy-test-trends-YYYYMMDD.json`, retention ≥ 30 日)  
     - (C) 外部ストレージ (S3 / GCS / Supabase 等) に API 経由でアップロード  
   - 初期段階では (B) を優先し、手動ダウンロード可能な形で履歴を確保する。将来 (A) で差分 PR を自動作成する案も検討。
2. **Baseline 運用**  
   - Nightly 開始時に「前回 Nightly の成果物」を baseline として復元できること。  
   - キャッシュキーを `ci-heavy-nightly-${ runner.os }` など「コミットハッシュ非依存」に変更する案を検討し、Nightly 間で継続利用できるようにする。
3. **メタデータ付与**  
   - JSON 出力に `runId`, `commit`, `workflow`, `branch`, `timestamp` などのメタ情報を付与し、履歴データ間の参照性を高める。  
   - `compare-test-trends.mjs` に追加フィールドを渡す or Nightly workflow 側でラップ JSON を生成する。
4. **通知/可視化フック**  
   - Δ が閾値を超えた場合に issue/Slack 通知を出す設計を検討（例: mutation score < 95%、MBT violations > 0 など）。  
   - 将来的に Observable / Grafana での可視化を想定し、NDJSON or CSV への変換スクリプトを用意する。

### 非機能要件
1. **保持期間**: 最低 30 日分の履歴を保持し、古いアーティファクトは自動削除。手動でダウンロードする場合は README に手順を記載。  
2. **再実行耐性**: rerun 時も同じ日付ファイルを上書き・追記できるよう、workflow dispatch で `RUN_ID` を含めたファイル名規則を定義。  
3. **コスト/時間**: 既存の CI Extended と同じ heavy テストを使うため、Nightly では `ci-extended.yml` を `workflow_call`（または `uses`）で再利用し、追加のジョブ時間を最小化する。  
4. **アクセス性**: 開発者がローカルで `node scripts/pipelines/sync-test-results.mjs --restore` → `compare-test-trends.mjs -o reports/heavy-test-trends.<date>.json` を実行し、Nightly と同じ出力形式で再現できるようにする。

## Nightly フロー案（ラフ案）
1. `nightly.yml` から `workflow_call` で `ci-extended.yml` を再利用する（main 最新コミットを対象に実行）。  
2. heavy suite 完了後に以下を追加（スケジュール実行のみ archive する条件付き）:
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
3. 将来: 上記 JSON をまとめた `heavy-test-trends.ndjson` を生成し、Grafana / Observable Notebook に連携。

### ci-extended 再利用方針の検討

`ci-extended.yml` を Nightly から再利用する方法としては以下の選択肢がある。現状のラベル判定ロジックや restore/cache 処理との整合性を踏まえて決定する。

| 方針 | 概要 | メリット | 懸念点 |
|------|------|-----------|--------|
| A. `workflow_call` を既存 `ci-extended.yml` に追加 | `on: [pull_request, push, schedule, workflow_dispatch, workflow_call]` とし、Nightly から `uses: ./.github/workflows/ci-extended.yml` で呼び出す | 単一ファイルでロジックを共有できる。Nightly 側は inputs/secret を渡すだけで済む | `workflow_call` 実行時の `github.event_name` は `workflow_call` になるため、ラベルベースの条件判定を見直す必要がある（ただし `!= pull_request` 分岐でフル実行するため影響は軽微）。 |
| B. `ci-extended.yml` の job を `workflow_call` 専用ファイルに切り出し (`ci-extended-job.yml`) | 既存 `ci-extended.yml` は従来トリガーのまま、Nightly からは切り出した再利用 workflow を呼ぶ | PR/PUSH 等の既存挙動に影響しない。Nightly 用に別 inputs を定義しやすい | 切り出し後の同期コストが発生。重複更新リスク。 |
| C. Composite Action 化 | `./.github/actions/run-ci-extended` に処理をまとめ、既存 `ci-extended` や Nightly から参照 | ワークフローファイルの記述を簡素化できる | 大量の `run` ステップ（cache/save/summary 等）を composite 内に移すとロギングが追いづらくなる。環境変数や `if` 条件の互換性を再調整する必要がある。 |

初期案では A（`workflow_call` を追加）を採用するのが最小の修正で済む。Nightly 実行時は `workflow_call` に渡す inputs として「重いテスト実行を必ず有効化」「アーカイブをオンにするフラグ」などを追加し、`Determine execution flags` ステップで `RUN_EXTENDED=true` を強制する分岐を設ける。  
将来的に B または C へ移行する場合は、本ドキュメントに手順と影響範囲を追記する。

### メタデータ
- `compare-test-trends.mjs` は `generatedAt` に加え、GitHub Actions の runId/runNumber/sha/ref などを `context` フィールドに自動付与する。  
- スケジュール実行で生成された `reports/heavy-test-trends-history/<timestamp>.json` には同じ `context` 情報が含まれるため、後段で履歴解析する際に run 単位で突合できる。

## 次ステップ候補
1. キャッシュキー & メタデータ改善（`ci-heavy-nightly-*`、`compare-test-trends` へのメタ情報追加）。  
2. Nightly workflow での履歴アーカイブ実装（最初は GitHub Artifact ベース）。  
3. 収集データの可視化 PoC（Observable Notebook or static Markdown レポート生成）。  
4. 通知基準（閾値）と Slack/Issue 連携の設計。

---

最新状況や決定事項は Issue #1005 / #1160 に同期し、実装着手時には本ドキュメントを更新する。
