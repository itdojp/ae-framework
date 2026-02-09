# ae-framework 詳細説明資料

> Language / 言語: English | 日本語

---

## English (Summary)

This document describes the current product structure, core components, and operational flows for ae-framework.

---

## 日本語

## 1. スコープと前提
ae-framework は、エージェント協調型SDLCを支える「仕様・検証・CI運用」の基盤です。プロダクトの中心は以下です。

- 仕様の登録と検証（Spec & Verification Kit）
- CI品質ゲート（verify-lite、coverage、securityなど）
- CLIとスクリプトによる運用自動化

前提条件は `docs/product/OVERVIEW.md` を参照してください。

## 2. 全体アーキテクチャ（論理）

### 2.1 レイヤ構成
1. **運用レイヤ**  
   - GitHub Actions: `.github/workflows/*`
   - PRコメントやラベル運用（verify-lite 等）
2. **実行レイヤ**  
   - CLI: `src/cli/*` と `package.json bin`
   - スクリプト: `scripts/*`
3. **仕様・検証レイヤ**  
   - 仕様: `spec/`, `docs/spec/registry.md`
   - 形式検証: `scripts/formal/*`
   - テスト: `tests/*`, `spec/bdd/*`
4. **成果物レイヤ**  
   - アーティファクト: `artifacts/*`
   - レポート: `reports/*`

### 2.2 主要コンポーネント

#### CLI
`package.json` の `bin` により以下のCLIが定義されています。

- `ae`, `ae-framework`: メインCLI（`src/cli/index.ts`）
- `ae-phase`: フェーズ関連CLI（`src/cli/phase-cli.ts`）
- `ae-approve`: 承認フロー用CLI（`src/cli/approval-cli.ts`）
- `ae-slash`: Slash コマンド関連CLI（`src/cli/slash-cli.ts`）
- `ae-ui`: UI向けエイリアス（`src/cli/ae-ui-alias.ts`）
- `ae-sbom`: SBOM関連CLI（`src/cli/sbom-cli.ts`）
- `ae-resilience`: レジリエンス機能CLI（`src/cli/resilience-cli.ts`）
- `ae-benchmark`: ベンチマークCLI（`src/cli/benchmark-cli.ts`）
- `ae-server`: サーバー起動（`src/cli/server-runner.ts`）

上記とは別に、メインCLI（`src/cli/index.ts`）は **サブコマンド** を登録しており、開発時は `pnpm run ae-framework -- <command>` 形式で呼び出せます。

代表的なサブコマンド（定義元）は以下です。

- `spec`（`src/cli/spec-cli.ts`）
- `state-machine`（`src/cli/state-machine-cli.ts`）
- `codegen`（`src/cli/codegen-cli.ts`）
- `fix`（CEGIS自動修復、`src/cli/cegis-cli.ts`）
- `enhanced-state`（`src/cli/enhanced-state-cli.ts`）
- `circuit-breaker`（`src/cli/circuit-breaker-cli.ts`）
- `security`（`src/cli/security-cli.ts`）
- `entry`（`src/cli/entry-runner-cli.ts`）
- `help`（`src/cli/help-cli.ts`。`pnpm run help` と同等の出力を目標）
- `setup`（`src/cli/setup-cli.ts`）
- `quality`（`src/cli/quality-cli.ts`）
- `qa`（`src/cli/qa-cli.ts`）
- `conformance`（`src/cli/conformance-cli.ts`）
- `integration`（`src/cli/integration-cli.ts`）
- `resilience`（`src/cli/resilience-cli.ts`）
- `sbom`（`src/cli/sbom-cli.ts`）
- `status` / `board`（`src/cli/progress-cli.ts`。`pnpm run progress:summary` の結果を参照）

#### 仕様と検証
- 仕様レジストリ: `docs/spec/registry.md`
- フォーマル検証: `docs/quality/formal-runbook.md`, `scripts/formal/*`
- 仕様コンパイル/検証: `spec:compile`, `spec:lint`, `spec:validate`（`package.json scripts`）

#### テスト体系
- ユニット、統合、プロパティテスト、BDD、MBTを分離した構成
- 例: `tests/property/`, `tests/integration/`, `spec/bdd/`

#### CIと品質ゲート
主要ワークフローは `.github/workflows/` に集約されています。

- 代表的なゲート: `verify-lite.yml`, `coverage-check.yml`, `workflow-lint.yml`
- 形式検証: `formal-verify.yml`, `formal-aggregate.yml`
- セキュリティ: `security.yml`, `sbom-generation.yml`
- その他: `ci-fast.yml`, `ci-extended.yml`, `pr-verify.yml`

### 2.3 形式検証スタック（拡張後）
`scripts/formal/*` は全ツールを non-blocking で統一運用し、`artifacts/hermetic-reports/formal/` に summary を出力します。

- ランナー: `verify:conformance`, `verify:alloy`, `verify:tla`, `verify:smt`, `verify:kani`, `verify:spin`, `verify:csp`, `verify:lean`, `scripts/formal/verify-apalache.mjs`
- 統合実行: `pnpm run verify:formal`
- 集約: `pnpm run formal:summary`（`aggregate-formal.mjs` + `print-summary.mjs`）

**CSP(cspx) 拡張点**
- `verify:csp` は `CSP_RUN_CMD -> cspx -> refines -> cspmchecker` の順でバックエンド選択
- `cspx` 利用時は `csp-summary.json` と `cspx-result.json` を固定パス出力
- `schema_version=0.1` を互換基準とし、非互換は `status=unsupported` として要約
- `formal-aggregate.yml` の PR 集約は `backend/status/resultStatus/exitCode` を表示

## 3. リポジトリ構成（主要ディレクトリ）

| ディレクトリ | 役割 |
| --- | --- |
| `src/` | コア実装、CLI、MCPサーバー |
| `scripts/` | CI/品質/検証の自動化スクリプト |
| `docs/` | ドキュメント群 |
| `spec/` | 仕様レジストリと仕様定義 |
| `tests/` | テスト（ユニット、統合、プロパティ、レジリエンスなど） |
| `packages/` | サブパッケージ（spec-compiler 等） |
| `templates/` | 仕様・品質・CIのテンプレート |
| `artifacts/`, `reports/` | 実行結果・集約レポートの出力先 |
| `configs/` | TypeScript/テスト/CI設定類 |

## 4. 主要フロー

### 4.1 ローカル検証フロー（例）
1. 依存導入: `pnpm install`
2. 最小検証: `pnpm run lint`, `pnpm run test:fast`
3. 形式検証（任意）: `pnpm run verify:formal`

### 4.2 CIフロー（例）
1. PR作成
2. `verify-lite` を中心に軽量ゲートを通過
3. 必要に応じて `run-formal` ラベルまたは `workflow_dispatch` で `formal-verify` を実行
4. 必要なら `enforce-formal` ラベルで Apalache `ran/ok` をゲート化

### 4.3 仕様検証フロー
1. 仕様の登録と更新（`spec/`）
2. `spec:validate` で構文検証
3. 形式検証で反例や不整合を検出

## 5. 成果物とトレーサビリティ

- `artifacts/` と `reports/` にCI成果物を集約
- 形式検証やテスト結果の要約は CI コメントと連動
- 形式検証の主成果物: `artifacts/hermetic-reports/formal/summary.json`
- CSP 詳細成果物: `artifacts/hermetic-reports/formal/csp-summary.json`, `artifacts/hermetic-reports/formal/cspx-result.json`
- トレーサビリティ設計は `docs/verify/TRACEABILITY-GUIDE.md` を参照

## 6. セキュリティとコンプライアンス

- セキュリティ検証ワークフロー: `security.yml`, `sbom-generation.yml`
- SBOM生成や依存監査を含む運用を想定

## 7. 制約と注意点
- 本プロダクトはCI/CDの定義と運用基盤を提供するが、運用代行は行いません
- エージェントの実行環境は外部に依存します

## 8. 関連資料
- 概要説明資料: `docs/product/OVERVIEW.md`
- 利用マニュアル: `docs/product/USER-MANUAL.md`
- 実装準拠の全体構成: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- 全体ナビゲーション: `docs/README.md`
