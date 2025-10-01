# Mutation Coverage Improvement Plan (Week2)

## 現状サマリ
- 直近の `./scripts/mutation/run-scoped.sh --quick --mutate src/utils/enhanced-state-manager.ts`（2025-09-30 02:30 JST 実行）
  - 走行時間: **約 4 分 24 秒**
  - ターゲット: `src/utils/enhanced-state-manager.ts`
  - ミューテーションスコア: **58.33%**（killed 175 / survived 102 / no-cover 23 / errors 49）
  - 追加ユニットテスト（lazy initialize の重複防止、metadata version 取り込み）が 40.88% → 58.33% まで押し上げ。残存ミュータントは `versionIndex` 再構築・`stateImported` イベント payload・`findKeyByVersion` の null ガードに集中。
- `./scripts/mutation/run-scoped.sh --quick --mutate src/api/server.ts`（2025-09-30 実行）はスコア **100.00%** を維持（survived 0 / timeout 0 / no-cover 0 / errors 31）。Telemetry span helper 追加後の状態に変化なし。
- `make test-mutation`（限定スコープ一括実行）は 56% 台を再現（約 35 分）。現状 survivor の大半は EnhancedStateManager に集中。
- TypeScript Checker は `tsconfig.stryker.json` 厳格設定で稼働中。現状型エラーはゼロ。
- ランナーは Vitest (`vitest.stryker.config.ts`) を使用。限定スコープのクイックランを基点に段階的拡張を図る方針。


## ボトルネック
1. **EnhancedStateManager の初期化/インポート網羅不足**: `ensureInitialized` 反転・optional chaining 破壊のミュータントが survive しており、初期化フローの観測が足りない。
2. **Property / MBT 起因の no-cover**: 生成テストが対象ロジックを十分に行き来できず、Stryker が `no-cover` 判定を出している箇所が多い。
3. **一括モードの実行時間**: Quick モードは 5 分以内だが一括モードは 30 分超のため、差分ベースのスコープ選定を徹底しながらユニットテスト拡充で kill 率を底上げする必要がある。

## 方針
- **段階的なスコープ絞り込み**: まず `src/domain/**/*.ts`、`src/utils/enhanced-state-manager.ts`、`src/api/server.ts` のみ対象にし、確実に kill 率を伸ばす。
- **ユニットテスト拡充**: 上記対象に対してユニットテストを追加し、ミュータントが kill されるラインを増やす。
- **Stryker 設定の最適化**: `reporters` に JSON を追加して結果を機械的に追跡、`mutate` を限定し、実行時間を短縮。
- **段階的な拡張**: スコアが 30% 以上に到達したら、`src/api` の他ファイル / `src/services` へ対象を広げる。

## クイックランと差分選定の自動化
- `./scripts/mutation/run-scoped.sh --quick`: concurrency=1 / timeoutMS=10000 / time-limit=420 秒で `src/api/server.ts` のみを対象に 5〜6 分で完走するモード。実行後に `reports/mutation/index.html` と `reports/mutation/mutation.json` が上書きされる。
- `./scripts/mutation/gather-mutate-patterns.sh [base_ref] --output <file>`: `git diff` の結果から TypeScript ファイルを抽出し、Stryker の `--mutate-file` オプションに渡せるパターン一覧を生成する。CI では `origin/main` との差分を出力して一時ファイルに保存する想定。
- `./scripts/mutation/run-scoped.sh --auto-diff[=<ref>]`: `gather-mutate-patterns.sh` を内部呼び出しし、`origin/main` との差分から mutate パターンを自動生成して Stryker に渡す。`--mutate` や `--mutate-file` と併用すると差分 + 追加指定のパターンで実行できる。
- `./scripts/mutation/list-survivors.mjs`: `reports/mutation/mutation.json` から Survived ミュータントを JSON で抽出。Verify Lite の Mutation quick ステップがこのスクリプトを呼び出し、トップ 10 件を Step Summary へ貼り付けつつ、最大 50 件のリストを `mutation-survivors-json` アーティファクトとして保存する。
- `.github/workflows/mutation-quick.yml`: `workflow_dispatch` で `run-scoped.sh --quick` を実行し、生成された HTML / JSON レポートをアーティファクトとしてアップロードする。ブランチ push 後に実行確認する。
- `.github/actions/mutation-auto-diff/`: 共通 composite action として base ref fetch / auto-diff 実行 / summary 収集 / アーティファクト化を提供。`mutation-quick` と `verify-lite` で利用。
- CI で `--auto-diff` を利用する場合は、実行ジョブの冒頭で `git fetch origin main --depth=1` 等を行い、比較対象ブランチをローカルに用意しておく。
- 差分に応じたスポット実行例: `./scripts/mutation/gather-mutate-patterns.sh HEAD~1 --output /tmp/mutate.list && ./scripts/mutation/run-scoped.sh --quick --mutate-file /tmp/mutate.list`

### EnhancedStateManager サバイバー洗い出しメモ（2025-09-30）
- `gh workflow run Mutation Quick` を実行すると、Step Summary にトップ10件、アーティファクト `mutation-survivors-json` に最大50件の Survived ミュータントが保存される。ローカルでも `node scripts/mutation/list-survivors.mjs --limit 20` で同じ JSON を参照できる。
- 現状の survive 集中箇所（直近 quick run レポートより）:
  - `src/utils/enhanced-state-manager.ts:640-680` — import 正規化 (`normalizeImportedState`)。`metadata` / `versionIndex` 欠落時の再生成が未テスト。
  - `src/utils/enhanced-state-manager.ts:700-740` — `findKeyByVersion` / `versionIndex` 再構築。削除済エントリに遭遇した際のフォールバックをアサートする必要あり。
  - `src/utils/enhanced-state-manager.ts:780-820` — `stateImported` イベント payload。AEIR ↔ Buffer 変換時に `event.payload.data` が空にならないことを保証するテストが不足。
- テスト追加 TODO（Week2→Week3 ブリッジ）:
  1. import 時に `metadata.entries` が存在しなくても生成されることを確認するユニットテスト。
  2. `ensureInitialized` の早期リターンを反転させたミュータントを kill するため、未初期化状態で `withTransaction` を呼ぶケースの追加。
  3. TTL=0 のアップサート後に GC が `versionIndex` / `keyIndex` の整合性を保つか検証するケース。
  4. `stateImported` イベントが圧縮 Buffer と AEIR を扱う場合の payload 型チェック（optional chaining 破壊対策）。
- 上記テストは `tests/unit/utils/enhanced-state-manager.test.ts` に順次追加し、必要に応じて Property ベースの補強を検討する。

## 次のステップ
1. `stryker.config.js` と `tsconfig.stryker.json` を更新し、mutate/TypeScript の対象を `src/domain`, `src/utils/enhanced-state-manager.ts`, `src/api/server.ts` に限定（実施済み）。
2. `make test-mutation` は `scripts/mutation/run-scoped.sh` 経由で実行され、デフォルトで同範囲を使用。環境変数で短時間の追加パターンも設定可能。
3. EnhancedStateManager 向けの追加ユニットテストを設計: `versionIndex` 再構築ループの副作用検証、`stateImported` イベント payload の assertion、`findKeyByVersion` の null ガード観測など surviving mutant に紐づく分岐を網羅。
4. 差分対象で `make test-mutation` / quick run を再実行し、HTML/JSON レポートで kill 率を確認。
5. 結果に基づき `src/api/routes/**` や `src/services/container/**` など次の領域を選定し、必要なテストを設計。
6. CI 連携を想定し、Stryker Dashboard か JSON レポートをアーティファクトとして保管。

## 指標
- 直近スコア: **58.33%**（EnhancedStateManager quick run）
- フェーズ1 目標: 30%（限定スコープ）→ 達成済み
- フェーズ2 目標: 50%（API routing + domain）→ 達成済み（API server 100% / EnhancedStateManager 56%）
- フェーズ3 目標: 65%（サービス層の主要メソッドをカバー）→ survivors 解消と Property/MBT カバレッジ拡充が必要

## メモ
- `errors` が多いファイルは `mutator.excludedMutations` や `ignorePatterns` で一時的に外す。
- Vitest で重いテストは `test:unit` の対象外にし、必要であれば `--runInBand` で安定化。
- 長時間ランに備えて `timeoutMS` / `dryRunTimeout` を調整し、CI タイムアウトを防止。


## 最新結果
- 2025-09-30 再実行 (`./scripts/mutation/run-scoped.sh --quick --mutate src/utils/enhanced-state-manager.ts`, lazy initialize・metadata import テスト追加): 約4分24秒で完了。スコア **58.33%**、survived 102 / no-cov 23 / errors 49。未対応ミュータントは `versionIndex` 更新ループの no-op 化、`stateImported` イベント payload の破壊、`findKeyByVersion` の null ガード無視に集約。
- 2025-09-30 再実行 (`./scripts/mutation/run-scoped.sh --quick --mutate src/utils/enhanced-state-manager.ts`, インデックス/トランザクション系テストを追加): 約4分25秒で完了。スコア **56.67%**、survived 107 / no-cov 23 / errors 49。`ensureInitialized` 反転・optional chaining を潰すテストが未整備のため survivor が残存。
- 2025-09-28 再実行 (`./scripts/mutation/run-scoped.sh` + `vitest.stryker.config.ts` 更新): 約5分で完了。スコア **22.67%**、survived 92 / no-cov 82 / errors 11。API server の availability / runtime-guard を中心に kill できたが、Quantity バリデーションや runtime guard の例外系は未カバー。
- 2025-10-02 再実行 (可用性エッジケース + 予約成功/再利用ルートのテレメトリ検証を追加): 約5分42秒で完了。スコア **57.26%**、survived 82 / no-cov 21 / errors 12。残存は再利用レスポンスの `validateResponse` 呼び出し引数・span ガード・quantity フォールバックの条件式など。
- 2025-09-28 再実行 (reservation business-rule, span fallback, guard bypass のテストを拡充): 約5分33秒で完了。スコア **68.46%**、survived 65 / no-cov 11 / errors 12。リクエスト検証のテレメトリ文脈 (`endpoint`/`operation`) と item-not-found ハンドラ、quantity フォールバック条件が残存。
- 2025-09-28 再実行 (request validation context・missing quantity sentinel・item-not-found timer のアサーションを追加): 約5分47秒で完了。スコア **72.80%**、survived 57 / no-cov 11 / errors 12。残存ミュータントはヘルスチェックのテレメトリ、予約入力バリデーションの timer 結果、health エンドポイントの span 分岐など上流フェーズに集中。
- 2025-09-28 再実行 (health テレメトリと予約バリデーション失敗のメトリクスを網羅): 約5分44秒で完了。スコア **80.40%**、survived 45 / no-cov 4 / errors 12。残存は onResponse カウンタ文字列と health チェックのバリデーション失敗/例外分岐（console.error, span 未設定）に集中。
- 2025-09-28 再実行 (onResponse カウンタと health 失敗時の span 欠損をテスト追加): 約5分45秒で完了。スコア **83.60%**、survived 40 / no-cov 1 / errors 12。残るのは onResponse の 4xx スパン例外分岐と health バリデーション失敗時の `console.error` 実装差異。
- 原因: `tsconfig.stryker.json` が `src/api` / `src/services` を含んでいたため、Stryker が全体を解析 → 37 分。config を修正済みなので次回実行で縮小効果を確認する。
- 2025-09-28 再実行 (onResponse 4xx span 例外と health ガードテストを拡充): 約5分45秒で完了。スコア **86.40%**、survived 33 / no-cov 1 / errors 12。残存は応答 duration 計算 (`Date.now() - startTime`) の演算ミュータントと health span 分岐の true 固定化です。
- 2025-09-28 再実行 (リクエストヘッダ計測と health span 両分岐をテスト): 約5分43秒で完了。スコア **90.40%**、survived 23 / no-cov 1 / errors 12。残りは request ヘッダの user-agent エイリアスと health span 固定化ミュータントです。
- 2025-09-28 再実行 (request user-agent fallback + duration guard テスト): 約5分42秒で完了。スコア **92.80%**、survived 18 / no-cov 0 / errors 12。残存は onRequest の tracer span 名称 (`ae-framework-api`) と health span true 固定化です。
- 2025-09-28 再実行 (user-agent ブランク送信のユニットテスト調整 + onResponse duration ガード確認後の追走): 約5分56秒で完了。スコア **92.52%**、survived 19 / no-cov 0 / errors 16。残りのミュータントは `src/api/server.ts` の user-agent `trim()` チェック、および `startTime` フォールバックと duration 計算、health span 分岐の真偽固定化。これらに対応するエッジケース・タイマー計測テストを Week2 の残タスクに加える。
- 2025-09-28 再実行 (`STRYKER_TIME_LIMIT=420 ./scripts/mutation/run-scoped.sh` 最新): 約5分59秒で完了。スコア **94.49%**、survived 14 / no-cov 0 / errors 16。残存ミュータントは `securityConfig` のテスト環境分岐（NODE_ENV 判定と `{ enabled: true }` 指定）、`user-agent` 型ガード、`startTime` フォールバック、health span 例外分岐といった実質同等パスに集中。これらはFastifyがヘッダを文字列化する仕様や span 例外処理の等価変換が原因で、Week3 (#1002) での追加テスト設計/実装（カスタム request 注入やhook順制御）が必要。
- 2025-09-28 再実行 (quick モード追加 + JSON レポート保存 + inventory fixture 化): 約5分28秒で完了。スコア **99.61%**、survived 1 / no-cov 0 / errors 16。JSON レポートは `reports/mutation/mutation.json`、HTML レポートは `reports/mutation/index.html` に出力されるようになった。残存ミュータントは `src/api/server.ts:57` の user-agent 判定が `true` 固定化されるケースで、Fastify sentinel (`lightMyRequest`) を kill できる追加ユニットテスト or 実装側での sentinel 正規化が今後の課題。
- 2025-09-28 再実行 (normalizeUserAgent 実装 + sentinel テスト強化): 約6分16秒で完了。スコア **99.62%**、survived 0 / no-cov 0 / errors 16。`normalizeUserAgent` で非文字列・空文字・Fastify sentinel (`lightMyRequest`) を明示的に `unknown` 扱いとし、ユニットテストで直接検証することで ConditionalExpression ミュータントを完全に kill。
- 2025-09-29 再実行 (quick モード / `timeout` 420s): 約6分59秒で完了。スコア **90.99%**、survived 16 / no-cov 13 / errors 19。予約キャンセル応答のバリデーション負パスや timer/telemetry の例外系が未カバー。`reports/mutation/index.html` / `mutation.json` を更新済み。残タスクとして該当分岐のユニットテスト追加とテレメトリ検証を Week3 (#1002) に引き継ぐ。



## コンパイルエラー系ミュータントのメモ
- 集計 (reports/mutation/mutation.json 時点):
  - 6 件: `Map([...])` の要素を空配列に置き換えるミュータント → inventory 初期化で型不整合
  - 3 件: `normalizeUserAgent` で `trim` 呼び出しが unknown 型扱いになる改変
  - 1 件: `normalizeUserAgent` が戻り値を返さない BlockStatement へ置き換わる改変
  - 1 件: `normalizeUserAgent` の typeof 比較を空文字へ書き換える改変
  - 1 件: `createTimer` 呼び出しに引数が入る改変
  - 1 件: `enhancedTelemetry.createTimer` の戻り値を利用しない改変 など
- いずれも TypeScript の型安全性に守られているため、当面は CompileError として残しつつスコア外で監視する。将来的にノイズが問題になる場合は `ignorePatterns` での除外 or helper を純粋関数化して型変換を抑止する方針が考えられる。
- quick モードでは `src/api/server.ts` に 19 件の CompileError ミュータントが残存。`normalizeUserAgent` の戻り値削除や `Map` 初期化を空配列化する改変が原因で、TypeScript の型チェック段階で弾かれている。
- CompileError は Mutation Score の分母に含まれず、テストで検知する必要はないが、レポート上のノイズを減らしたい場合は `stryker.conf.js` で該当 mutator を `ignorePatterns` に指定する。
- 詳細は `reports/mutation/mutation.json` の `status == "CompileError"` を抽出すると確認できる。例: `id=0` は BlockStatement 化で `normalizeUserAgent` が戻り値を失うケース。
- 2025-09-30 `./scripts/mutation/run-scoped.sh --quick`（`src/api/server.ts`）
  - スコア **100.00%**（kill 324 / survive 0 / errors 25 / no-cov 0）
  - 対応内容: `recordSpanMetrics` / `recordSpanError` helper の導入と span フェイルセーフユニットテスト（`tests/unit/api/server.test.ts`）追加で残ミュータントを解消
