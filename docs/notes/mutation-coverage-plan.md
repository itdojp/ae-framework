# Mutation Coverage Improvement Plan (Week2)

## 残存サバイバー対応計画（2025-10-07 更新）
- 優先サバイバー:
  1. `versionIndex` 減算系（Math.min 変異）
  2. `Buffer` 判定の OR 変異（`reviveEntryData`）
  3. `findLatestKey` 空集合パスのフォールト注入
- 対応アクション:
  - `findLatestKey` の負例テストを追加し、空集合時の挙動を明示する。
  - `reviveEntryData` に TypedArray/SharedArrayBuffer の fixture を追加し、`Buffer.isBuffer` 以外も安全化。
  - `versionIndex` 減算系は import/export の差分検証テストを拡充し、算出結果を期待値で固定。
- フォローアップ Issue: 追跡用に `EnhancedStateManager` 用の mutation backlog (#TODO) を作成して進捗を共有する。

## 現状サマリ（2025-10-06 更新）
- `./scripts/mutation/run-scoped.sh --quick --mutate src/utils/enhanced-state-manager.ts`（2025-10-02 10:50 開始）
  - 走行時間: **約 135 分**（time-limit 未指定のため全 457 ミュータントを順次実行）
  - ミューテーションスコア: **9.85%**（killed 45 / survived 412 / no-cover 0 / errors 0）
  - Survivor は初期化ガード（`ensureInitialized`）、インポート時の optional chaining、`persistToDisk`／`shutdown` の例外ハンドリング、TTL/インデックス再構築、チェックサム算出、イベント emit 周辺に集中。
- `STRYKER_TIME_LIMIT=900 ./scripts/mutation/run-scoped.sh --quick --mutate src/utils/enhanced-state-manager.ts -c configs/stryker.enhanced.config.js`（2025-10-02 19:43 開始）
  - 走行時間: **約 9 分 15 秒**（command runner で `tests/unit/utils/enhanced-state-manager.test.ts` のみ実行）
  - ミューテーションスコア: **62.58%**（killed 286 / survived 171 / no-cover 0 / errors 0）
  - quick run が現実的な時間に短縮され、サバイバーはトランザクション、スナップショット、復元系の分岐へ集約。
  - `tests/unit/utils/enhanced-state-manager.test.ts` に初期化イベント／ssotLoaded／snapshot／自動トランザクション／ロールバック系のユニットテストを追加し、該当ミュータントの一部を kill 済み。
- `STRYKER_TIME_LIMIT=420 npx stryker run configs/stryker.enhanced.config.js`（2025-10-06 11:06 開始）
  - 走行時間: **約 2 分 54 秒**（incremental レポートをクリアしてフル quick ラン）
  - ミューテーションスコア: **65.51%**（killed 302 / survived 159 / no-cover 0 / errors 0）
  - `reviveEntryData` のレガシー配列復元と `createSnapshot` の phase/entity フィルタをテストでカバーし、Section2 のターゲットである 65% ラインを突破。
- `STRYKER_TIME_LIMIT=420 npx stryker run configs/stryker.enhanced.config.js --mutate src/utils/enhanced-state-manager.ts --concurrency 1`（2025-10-06 17:02 開始）
  - 走行時間: **約 11 分 19 秒**（DisableTypeChecks の warning は継続するが quick ランは安定）
  - ミューテーションスコア: **67.25%**（killed 310 / survived 151 / no-cover 0 / errors 0）
  - GC ログ分岐（`runGarbageCollection`）と TTL 失効パスをユニットテスト追加でカバーし、サバイバーが `normalizeImportedEntry` の Buffer 復元・checksum 再計算・optional chaining 分岐に集約された。
- `STRYKER_TIME_LIMIT=420 npx stryker run configs/stryker.enhanced.config.js --mutate src/utils/enhanced-state-manager.ts --concurrency 1`（2025-10-07 07:19 再実行）
  - 走行時間: **約 12 分 02 秒**
  - ミューテーションスコア: **72.02%**（killed 332 / survived 129 / no-cover 0 / errors 0）
  - logicalKey 欠落時の例外、TTL 未指定ケース、object payload 圧縮時の checksum、imported version 上限をテストでカバー。残サバイバーは versionIndex の減少（Math.min 変異）と Buffer 判定（OR 化）などに集約されたため、次ステップは version diff の明示検証と TypedArray など別形態 payload での判定を強化する。
- `STRYKER_TIME_LIMIT=420 npx stryker run configs/stryker.enhanced.config.js --mutate src/utils/enhanced-state-manager.ts --concurrency 1`（2025-10-07 09:37 再実行）
  - 走行時間: **約 10 分 34 秒**（DisableTypeChecks の warning は継続）
  - ミューテーションスコア: **62.69%**（killed 289 / survived 172 / no-cover 0 / errors 0）
  - 新規テストで importState 経路の型安全性を向上させた結果、`reviveEntryData` の Buffer 判定分岐や `calculateChecksum`／`loadFromPersistence` の例外処理が再びサバイバーとなった。次アクションは Buffer 判定の additional fixtures、checksum 再計算の負例、`shutdown`／`persistToDisk` の例外パスに対するユニットテスト追加。
- `STRYKER_TIME_LIMIT=420 npx stryker run configs/stryker.enhanced.config.js --mutate src/utils/enhanced-state-manager.ts --concurrency 1`（2025-10-07 10:26 再実行）
- `STRYKER_TIME_LIMIT=420 npx stryker run configs/stryker.enhanced.config.js --mutate src/utils/enhanced-state-manager.ts --concurrency 1`（2025-10-07 10:45 再実行）
  - 走行時間: **約 10 分 58 秒**
  - ミューテーションスコア: **67.25%**（killed 310 / survived 151 / no-cover 0 / errors 0）
  - metadata/tags/id の保持テストと Buffer インスタンスの復元確認により `checksum`・`source`・`tags` 系のミュータントを除去。残りは `reviveEntryData` の TypedArray ハンドリングと `findLatestKey` の空セット処理に集約しているため、TypedArray/空配列用の追加テストが今後のターゲット。
- Quick mutation run `./scripts/mutation/run-scoped.sh --quick` は TokenBucket/Bulkhead テストの修正で従来の queue full 起因のエラーは解消。ただし CircuitBreaker property/integration 系が残存し、引き続き initial run failure になる点を記録。
  - 走行時間: **約 11 分 04 秒**
  - ミューテーションスコア: **64.86%**（killed 299 / survived 162 / no-cover 0 / errors 0）
  - Buffer/metadata 復元・チェックサム・シャットダウン周りのユニットテストを追加し、`reviveEntryData` の Buffer 分岐や `persistToDisk`/`shutdown` の例外再throw をカバー。残サバイバーは `normalizeImportedEntry` 内のメタデータ補完（source／phase／tags 既存値の尊重）に集中しているため、既存メタデータを保持する回帰テストが次の候補。
- `./scripts/mutation/run-scoped.sh --quick --mutate src/api/server.ts`（2025-10-02 再実行）は **100.00%**（killed 155 / survived 0 / no-cover 0 / errors 0 / 実行 66s）。
- `./scripts/mutation/run-scoped.sh --quick`（差分無しのデフォルト quick ラン）は 2025-10-02 10:43 時点で **完走 & score 100.00%**。TokenOptimizer が圧縮で空文字列化した際に元データへフォールバックするよう修正し、先の `seed:1083850253` failure を解消。
  - ただし `STRYKER_TIME_LIMIT=180` で再実行した際には `tests/property/token-optimizer.trim-edge.trailing-comma.boundary.pbt.test.ts` が sandbox で失敗し Dry run が中断。trim-edge 系プロパティの期待値調整が新たな課題。
- `make test-mutation`（限定スコープ一括モード）は約 35 分で完走。スコアは 56% 台で、EnhancedStateManager に survivors が集中している。
- TokenOptimizer 関連の Property/Unit は単体実行では緑化するが、Stryker サンドボックスでは上記プロパティが再現的に失敗するため仕様の見直しが必要（`docs/notes/token-optimizer-test-status.md` に詳細追記）。
- TypeScript Checker (`tsconfig.stryker.json`) は strict 設定で稼働中。ランナーは Vitest (`vitest.stryker.config.ts`) のまま。

## ボトルネック
1. **EnhancedStateManager の初期化/インポート網羅不足** — survivor が残っている箇所に対し、より細かいユニット／integration テストが必要。
2. **Stryker quick ランの安定化** — TokenOptimizer のフォールバック調整で quick ランは復旧したが、今後のリファクタ時に再発しないよう property の期待値と fast-check ジェネレータを継続的に監視する必要がある。
3. **一括モードの実行時間** — 30 分超の run を減らすため、差分ベースで mutate 対象を絞り、テスト拡充で kill 率を底上げする。

## 方針
- **スコープの段階的拡張**: 当面は `src/utils/enhanced-state-manager.ts`・`src/api/server.ts` に集中し survivor を削る。一定水準まで到達したら `src/services/**` などへ拡大。
- **ユニットテスト拡充**: Survivor が残る箇所を狙ったテストを追加（EnhancedStateManager の TTL/rollback、mutation で露呈した optional chaining 破壊など）。
- **Stryker 環境整備**: `disableTypeChecks` の対象を見直す、または `execute-contracts.ts` を Babel が解釈できる形に書き換える。TokenOptimizer には `export const estimateTokens = ...` ラッパーを追加し、CJS 変換時でも named export が維持されるようにする。
- **CI 連携**: Quick ランが復旧したら GitHub Workflow に再度組み込み、Step Summary へサバイバー JSON を添付する。

## クイックランと差分選定メモ
- `./scripts/mutation/run-scoped.sh --quick`: concurrency=1 / timeoutMS=10000 / time-limit=420s。
- `./scripts/mutation/gather-mutate-patterns.sh`: `git diff` から mutate 対象を抽出するヘルパー。CI は `origin/main...HEAD` 差分を前提。
- `./scripts/mutation/run-scoped.sh --auto-diff[=<ref>]`: 差分 + 追加指定を組み合わせて quick ランを実行。
- Stryker v8 では config ファイルを位置引数で渡す必要があるため、run-scoped.sh 側で `--config` を使わない実装に調整済み。

## TODO
- [x] `scripts/verify/execute-contracts.ts` を try/catch で書き換え、Babel/Stryker が解釈できるようにする。
- [x] Email property の入力制約を見直し、Zod バリデーションの `Invalid email` を解消する。
- [x] TokenOptimizer の `estimateTokens` を named export として公開し、Stryker サンドボックスでも利用できるようにする。
- [x] `tests/contracts/prompt-validation.test.ts` の成功率を安定化（現在 7/10）。
- [x] `tests/integration/test-orchestrator.test.ts` のモック生成ヘルパーを追加し、ReferenceError を解消する。
- [ ] Docker 最適化テスト用のフィクスチャ／スキップ戦略を整備し、ファイル依存の失敗を解消する。
- [x] Stryker の vitest ランナーに `configs/vitest.mutation.config.ts` を強制適用（`configFile` 設定 or command runner への切り替え）。
- [ ] EnhancedStateManager survivor（`versionIndex` / `stateImported` / `findKeyByVersion`）向けユニットテストを追加。
- [ ] TokenOptimizer trim-edge 系プロパティの sandbox failure を解消（trailing comma の期待値/実装を見直す）。
- [x] Quick ランが復旧したら `reports/mutation/mutation.json` を Step Summary / Artifact に再添付。（verify-lite / mutation-quick ワークフローで Artifact アップロードを再有効化）
- [ ] 一括モードの mutate 対象を差分ベースで自動抽出し、実行時間を短縮する。
- [x] `tests/property/token-optimizer.priority.order.pbt.test.ts` の仕様を再定義し、Stryker サンドボックスでも deterministic に通るよう fast-check ジェネレータとアサーションを調整する（2025-10-02: フォールバック実装 & 追加ユニットテストでケア）。
- [x] `src/api/server.ts` survivor のうち `span` 欠損時のガードを追加検証（no-span でも TypeError が出ないことをテストで保証）。
- [x] `src/api/server.ts` の `Date.now()` 差分に対するテストを導入し、duration フィールドの妥当性を確認。
- [x] ユーザーエージェント属性 (`http.user_agent`) がヘッダ有無で期待通り記録されるテストを追加。
- [x] テスト環境専用のセキュリティ設定 (`NODE_ENV === 'test'`) を確認するユニットテストを追加。
- [x] Telemetry 属性（`SERVICE_COMPONENT` / `SERVICE_OPERATION`）が期待通り記録されることを検証するテストを追加。
- [x] `trace.getTracer` が `undefined` を返す成功パスで `setAttributes` / `end` を呼ばないことを検証するテストを追加。
- [x] Fastify `logger` オプションが true であることを確認するユニットテストを追加。
- [x] `genReqId` 生成値の形式（`req_<timestamp>_<random>`）を検証するユニットテストを追加。
- [x] 空の UserAgent でリクエストした場合に `http.user_agent: 'unknown'` が記録されることを検証するユニットテストを追加。
- [x] `trace.getTracer` に渡す名前が `ae-framework-api` であることを保証するユニットテストを追加。
- [x] onResponse フックの `if (span)` ガードを成功パス/失敗パス双方で明示的に検証し、残存サバイバーを除去。
- [x] 初期化ガード (`isInitialized`)、`emit('stateManagerInitialized')` など初期化フローのサバイバーに対するユニットテストを追加。
- [x] トランザクションイベント／スナップショット生成（phase / entities 判定）まわりの分岐を網羅するテストを追加。
- [x] Buffer 復元（`data.type === 'Buffer'`) のサバイバーをカバーするテストを追加（checksum 算出系は別途強化予定）。
- [ ] 永続化（`persistToDisk` / `shutdown`）時のエラー処理とログ出力を property-based テストで補強。

## 備考
- 2025-10-08: EnhancedStateManager のバイナリ encode/round-trip テストを追加し、quick run スコアが 67.39%（killed 465 / survived 225）に到達。`verify-lite` ワークフローで mutation レポートを Step Summary とアーティファクトに再添付する整備を進める。
- TokenOptimizer テスト緑化の詳細は `docs/notes/token-optimizer-test-status.md` にまとめ済み。
- Podman rootless + compose での Stryker 実行は問題なし。Quick ランが緑化した段階で CI へ組み戻す。

## 再開時の手順メモ
1. `pnpm vitest run tests/property/token-optimizer.trim-edge.trailing-comma.boundary.pbt.test.ts --reporter dot --runInBand` で Stryker sandbox 再現ケースを潰し、必要に応じて期待値を調整する。
2. 修正後に `./scripts/mutation/run-scoped.sh --quick` を再実行し、Dry run 成功と Mutation スコアを確認。レポート (`reports/mutation/*`) は再生成して差分を確認する。
3. EnhancedStateManager 周辺の未対応サバイバーについて、`./scripts/mutation/run-scoped.sh --quick --mutate src/utils/enhanced-state-manager.ts` と `pnpm vitest run tests/unit/utils/enhanced-state-manager.test.ts --reporter dot` をセットで回し、テスト追加→再計測を繰り返す。
4. Docker 最適化テスト用フィクスチャが整い次第、`make test-mutation` をフルスコープで再走し、CI 連携（Artifact 添付 & Step Summary）を復旧させる。
