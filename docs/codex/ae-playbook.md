# CodeX CLI 0.38 × ae-framework プレイブック設計（最小版）

目的
- CodeX CLI 0.38 を外部オーケストレータとして用い、ae-framework の主要フェーズを順次実行しながら中間生成物（artifacts）を受け渡し、最終的に「ビルド・軽量テスト通過」まで到達する最小プレイブックを提供する。

スコープ（段階導入）
- Phase-1（本PR範囲: 設計）
  - 設計ドキュメント（本書）
- Phase-2（最小実装）
  - プレイブック本体 scripts/codex/ae-playbook.mjs（Setup→QA→Spec/Contracts/Replay/Simulation）
  - アーティファクト標準化（artifacts/ae/... 配下）
- Phase-3（拡張）
  - Formal（verify-tla/verify-apalache/presence/timeout/clamp）opt-in 統合
  - Coverage/Adapters（report-only）取り込み
- Phase-4（運用補助）
  - codex 用テンプレ（任意の codex.yaml）
  - 失敗時の再開 --resume／スキップ --skip=<phase>

アーキテクチャ
- 実行ハブ: Node スクリプト（例: scripts/codex/ae-playbook.mjs）でフェーズを順次実行
- 出力標準: artifacts/ae/<phase>/… に JSON/MD/LOG を配置し、最新状況を artifacts/ae/context.json に集約
- 失敗方針: Setup/Build/Unit Test は fail-fast、Formal/Adapters/Coverage は warn & continue（report-only）

フェーズ定義（最小→拡張）
1) Setup
   - 実行: `corepack enable && pnpm i && pnpm build`
   - 出力: `artifacts/ae/setup/build.log`
2) Spec/IR（任意: spec 不在ならスキップ）
   - 例: `node dist/src/cli/index.js spec compile --input specs/app.yaml --out artifacts/ae/spec/ir.json`
   - 出力: `artifacts/ae/spec/ir.json`
3) Contracts/Replay（report-only）
   - `node scripts/spec/generate-contracts.mjs --in artifacts/ae/spec/ir.json --out artifacts/ae/spec/contracts.json`
   - `node scripts/spec/generate-replay-fixtures.mjs --in artifacts/ae/spec/contracts.json --out artifacts/ae/spec/replay.json`
   - 出力: `artifacts/ae/spec/{contracts.json,replay.json}`
4) 決定的シミュレーション（report-only）
   - `node scripts/simulation/deterministic-runner.mjs --in artifacts/ae/spec/replay.json --out artifacts/ae/sim/sim.json`
   - 出力: `artifacts/ae/sim/sim.json`
5) QA/軽量テスト
   - `pnpm run test:fast`
   - `node dist/src/cli/index.js qa --light`（または `pnpm tsx src/cli/qa-cli.ts --light`）
   - 出力: `artifacts/ae/qa/qa.log`（任意）
6) Coverage/Adapters（Phase-3以降, report-only）
   - coverage: `artifacts/coverage/coverage-summary.json` を収集（既存と合流）
   - adapters: `artifacts/adapters/{a11y.json,perf.json,lh.json}`
7) Formal（Phase-3以降, opt-in / 非ブロッキング）
   - `node scripts/formal/verify-tla.mjs` → `artifacts/formal/tla-summary.json`
   - `node scripts/formal/verify-apalache.mjs`（存在時）→ `artifacts/formal/apalache-summary.json`
   - `node scripts/formal/validate-conformance-summary.mjs`（non-blocking）
   - （本プレイブック最小統合は verify-tla/verify-apalache を順次起動し、hermetic-reports/formal 直下の summary/log を検出して context.json に記録。aggregateは今後の拡張で対応）
8)（任意）ビルド・スモーク実行
   - `pnpm build`（再）/ `node dist/...` 最小実行
   - 出力: `artifacts/ae/build/smoke.log`

アーティファクト標準
- `artifacts/ae/context.json`（最新フェーズ・出力ファイル一覧・タイムスタンプ・exitCode 等）
- `artifacts/ae/spec/{ir.json,contracts.json,replay.json}`
- `artifacts/ae/sim/sim.json`
- `artifacts/coverage/coverage-summary.json`
- `artifacts/adapters/{a11y.json,perf.json,lh.json}`
- `artifacts/formal/{tla-summary.json,apalache-summary.json,formal-aggregate.json}`

エラー処理/再実行
- fail-fast: Setup/Build/Unit Tests
- warn & continue: Formal/Adapters/Coverage（report-only）
- `--resume` で context.json から再開、`--skip=<phase>` で対象フェーズをスキップ
- タイムアウト/リトライ: Formal 等は GNU `timeout` があれば使用（verify-* に準拠）

セキュリティ/Hermetic
- ネットワークを要する処理は既定 off、明示フラグで opt-in
- 外部バイナリ（例: Apalache）は presence チェックのみで非ブロッキング

CodeX CLI 0.38 からの実行例
- 初回〜軽量ルート
  - `codex run node scripts/codex/ae-playbook.mjs --resume --skip=formal,adapters`
- Formal を含む
  - `codex run node scripts/codex/ae-playbook.mjs --enable-formal --formal-timeout=60000`

実装ステップ（小PR分割）
1) PR1（本PR）: 設計ドキュメント（本書）
2) PR2: 最小プレイブック（Setup→QA→Spec/Contracts/Replay/Simulation）+ artifacts/ae/context.json の記録
3) PR3: Formal をプレイブックへ統合（presence/timeout/clamp, opt-in）
4) PR4: 任意の codex テンプレ（codex/ae.playbook.yaml）と `package.json` に `codex:run` を追加
5) PR5: 軽い統合テスト（ドライラン/特定フェーズのみ実行）

整合/関連ドキュメント
- docs/quality/formal-runbook.md（Formal 実行の個別ランブック）
- docs/quality/coverage-required.md（Coverage 運用/Required 化）
- docs/quality/adapter-thresholds.md（Adapters の report-only/enforce 運用）

備考
- 長行ログ/MD 整形（formal-aggregate）は wrap/clamp を環境変数で制御（デフォルトは既存値を踏襲）
- Spec 不在のプロジェクトでは Spec/Contracts/Replay/Simulation を自動スキップ設計
