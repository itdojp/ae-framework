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
3. 必要に応じて `ci-extended` や `formal-verify` をopt-inで実行

### 4.3 仕様検証フロー
1. 仕様の登録と更新（`spec/`）
2. `spec:validate` で構文検証
3. 形式検証で反例や不整合を検出

## 5. 成果物とトレーサビリティ

- `artifacts/` と `reports/` にCI成果物を集約
- 形式検証やテスト結果の要約は CI コメントと連動
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
- 全体ナビゲーション: `docs/README.md`
