# Integration テスト向けランタイム制御メモ

Integration スイートでは、テストごとの一時ディレクトリ作成や後処理の漏れを防ぐために `tests/_helpers/integration-test-utils.ts` を経由して共通ロジックを利用します。本ドキュメントでは主要ヘルパーと関連環境変数の使い方を整理します。

## 主要ヘルパー

| ヘルパー | 役割 | 典型的な利用箇所 |
|----------|------|------------------|
| `createIntegrationTempDir(prefix?: string)` | `tmpdir()` 配下に専用ディレクトリを作成し、後処理で自動削除 | `beforeEach` で作業ディレクトリや `outputDir` を差し替える際に利用 |
| `registerIntegrationCleanup(task)` | `afterEach` フックの共通クリーンアップにタスクを登録 | `serviceManager.shutdown()` やグローバル状態リセット処理 |
| `drainIntegrationCleanupTasks()` / `resetIntegrationCleanupTasks()` | 共通 afterEach から内部的に利用されるタスク管理 | テスト側で直接触る必要は基本的にありません |
| `applyIntegrationRetry(testApi)` | `AE_INTEGRATION_RETRY` に応じて vitest の `retry()` を一括適用 | flake 調査で一時的に再試行回数を上げたいとき |

### 使用例: tempDir とクリーンアップ

```ts
let integrationTempDir: string;

beforeEach(async () => {
  integrationTempDir = await createIntegrationTempDir('my-suite-');
  const manager = new ServiceManager();
  await manager.initialize();

  registerIntegrationCleanup(async () => {
    await manager.shutdown();
  });
});
```

`registerIntegrationCleanup` に登録した処理は、`tests/_setup/afterEach.integration.ts` がテスト毎に逆順で実行します。`integration-cli` / `system-validation` / `test-orchestrator` などのスイートでは、`outputDir` や phase-state 用の一時ディレクトリもこの仕組みで自動削除されます。

### 使用例: retry の一括適用

```ts
import { applyIntegrationRetry } from '../_helpers/integration-test-utils.js';

applyIntegrationRetry(it); // describe 前で呼び出す
```

CLI から再試行回数を増やす場合は `AE_INTEGRATION_RETRY=3 pnpm test:int` のように環境変数を指定します。値が数値でない場合や 1 以下の場合は無視され、デフォルトで 1（再試行なし）となります。

## AE_INTEGRATION_TRACE_HANDLES でハンドルリーク調査

共通 afterEach ではデフォルトで `why-is-node-running` を読み込まずオーバーヘッドを抑えています。ハンドルリークの詳細を確認したいときは、以下のように環境変数を設定してください。

```bash
AE_INTEGRATION_TRACE_HANDLES=1 pnpm test:int
```

有効化すると `why-is-node-running` が動的にロードされ、テスト終了時に開いているハンドルの詳細を出力します。CI ではデフォルト無効のまま運用し、ローカル調査や flake 再現時のみ切り替えることを推奨します。

### 典型的な出力例

```
why-is-node-running? There are 2 handle(s) keeping the process running
# Timeout
  at new Timeout (node:internal/timers:XXX:YY)
  ...

# Server TCPWrapper
  at createServer (node:net:XXX:YY)
  ...
```

表示されたハンドルはテスト終了時点で開いているリソースを示します。`Timeout` や `Server` が残っている場合は、テスト側で `clearTimeout` や `server.close()` を呼び忘れていないか確認してください。

### CI での利用メモ

- `gh run rerun <run_id> -e AE_INTEGRATION_TRACE_HANDLES=1` のように再実行時の環境変数で有効化できます。
- 常時 ON にするとログが肥大化するため、失敗再現時のみ短期的に使用し、原因究明後は必ず無効化します。
- GitHub Actions 手順の共通コメントは `.github/workflows/verify-lite.yml` のジョブ冒頭コメントも参照してください。

## AE_INTEGRATION_RETRY の推奨運用

- **デフォルト値は 1（再試行なし）**  
  `applyIntegrationRetry` は環境変数を数値化し、1 以下や不正値の場合は 1 にフォールバックします。通常運用では明示的に設定しないか、`AE_INTEGRATION_RETRY=1` のままにします。
- **flake 調査や CI の一時緩和にのみ利用**  
  一時的に再試行を増やす場合は `AE_INTEGRATION_RETRY=3 pnpm test:int` のように明示設定します。失敗ログを確認したうえで再試行が必要か判断し、恒久対応（テスト修正・ロジック改善）が完了したらデフォルトへ戻します。
- **CI 方針**  
  Verify Lite / integration ワークフローでは標準で `AE_INTEGRATION_RETRY=1`。bot や開発者が flake を診断するときのみ増加させ、常時の多回実行で失敗を覆い隠さない運用を徹底します。必要に応じて `gh run rerun <runId>` 時に環境変数を付与してください。

## 運用の指針

1. **副作用のあるリソースは必ず `registerIntegrationCleanup` に登録する。**  
   ServiceManager などが例外で途中停止しても後処理が走るようにする。
2. **作業ディレクトリや成果物は `createIntegrationTempDir` で隔離する。**  
   `outputDir: join(tempDir, 'test-results')` のように suffix を与えると分かりやすい。
3. **flake 解析時のみ `AE_INTEGRATION_RETRY` / `AE_INTEGRATION_TRACE_HANDLES` を利用する。**  
   デフォルトは最小限のオーバーヘッドで動作し、必要なときだけ機能を有効化する。
4. **新しい integration スイートを追加する場合は最初に helper を組み込む。**  
   既存スイート（`integration-cli` / `system-validation` / `test-orchestrator` / `optimization/system`）を雛形として流用すると高速です。

これらの手順に従うことで、リソースリークやテスト間干渉を最小化しつつ、必要に応じて詳細なデバッグ情報を取得できます。

## Heavy Test Artifacts Cache（CI Extended / Mutation / MBT）

CI Extended（`run-ci-extended` / `run-mutation` / `run-mbt` / `run-property`）を再実行する際は、heavy テスト成果物を `.cache/test-results` から復元して再利用できます。mutation survivors や MBT summary、property harness summary を活用すると再実行時間が短縮され、サマリ確認や差分比較が容易になります。

### ローカル／rerun 手順

```bash
# キャッシュ状況の確認
node scripts/pipelines/sync-test-results.mjs --status

# 既存キャッシュを復元し baseline をスナップショット
node scripts/pipelines/sync-test-results.mjs --restore
node scripts/pipelines/sync-test-results.mjs --snapshot

# CI Extended 相当のスイートを実行
pnpm run test:ci:extended

# baseline との比較結果を確認（Markdown が標準出力 / Step Summary に出力される）
node scripts/pipelines/compare-test-trends.mjs

# 成果物をキャッシュへ反映（ローカル更新後）
node scripts/pipelines/sync-test-results.mjs --store
```

`--status` は各カテゴリ（Mutation / MBT / Property）の source / cache / baseline の有無を表示します。CI では `.github/workflows/ci-extended.yml` が依存インストール後に `--restore`・`--snapshot` を呼び出し、ステップ終了後に `--store` で更新するため、再実行（rerun）でも `.cache/test-results` が復元対象として利用されます。`compare-test-trends.mjs` は baseline が存在する場合に差分（スコア・violations 等）を Markdown で出力し、`GITHUB_STEP_SUMMARY` が設定されていれば Step Summary に追記します。

#### GitHub Actions での利用
- `gh run rerun <runId>` 実行時、キャッシュがヒットすれば自動的に成果物を展開し、その後のステップで再計算をスキップできます。
- キャッシュキーは Pull Request / Push では `ci-heavy-${{ runner.os }}-${{ github.sha }}`、スケジュール実行では `ci-heavy-${{ runner.os }}-schedule` を使用します。Nightly 間で baseline を共有しつつ、PR や手動実行ではコミットごとの独立性を維持します。
- ローカルで更新した成果物を共有したい場合は GitHub Actions の rerun ではなく、ブランチ／PR 内で `node scripts/pipelines/sync-test-results.mjs --store` を一度実行してから push し、キャッシュを更新させてください。
- スケジュール実行（`github.event_name == 'schedule'`）では `reports/heavy-test-trends-history/<timestamp>.json` が自動生成され、アーティファクト `heavy-test-trends-history`（保持 30 日）として保存されます。JSON 内の `context` フィールドに runId / runNumber / SHA などの GitHub Actions 情報が含まれるため、履歴解析や可視化に活用できます。

この仕組みを活用することで、MBT や mutation quick の長時間処理を繰り返し実行せず、再検証やレポート整合性の確認を効率化できます。


`pnpm node scripts/pipelines/render-heavy-trend-summary.mjs --limit 5` を実行すると、履歴 JSON から最新のサマリ Markdown を生成し Step Summary に追記できます。閾値をカスタマイズしたい場合は `--warn-*` / `--critical-*` オプションを指定し、`--json-output` でアラート判定を取得できます。