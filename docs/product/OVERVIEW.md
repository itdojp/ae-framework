# ae-framework 概要説明資料

> Language / 言語: English | 日本語

---

## English (Summary)

ae-framework is an agentic SDLC orchestrator and spec verification kit that standardizes requirements, tests, and CI quality gates.

- Purpose: align requirements, verification, and CI automation for auditable development
- Key capabilities: spec registry, verification pipelines, quality gates, GitHub Actions workflows
- Delivery: project skeleton, CLI tooling, scripts, and templates for automation
- Non-goals: hosted CI/CD service, agent runtime, or IDE plugin
- Prerequisites: Node.js >=20.11 and <23, pnpm 10.0.0, GitHub Actions environment

---

## 日本語

### 1. 目的と位置づけ
ae-framework は、エージェント協調型のSDLCを実行するための「オーケストレーター兼 仕様・検証キット」です。要求から検証までの流れを標準化し、監査可能で再現性のある品質管理を実現します。

### 2. 解決する課題
- 要件・仕様・テスト・CIの断絶による品質管理の不整合
- 大規模検証の再現性不足と退行検知の遅延
- エージェント活用時の成果物品質のばらつき

### 3. 提供価値
- 仕様と検証の一貫運用を可能にするスクリプトとワークフロー
- 品質ゲートやトレーサビリティの可視化
- 小さなPR単位での可逆運用とCI最適化

### 4. 主な構成要素
- GitHub Actions を中心としたCIワークフロー群
- CLIとスクリプトによる仕様・検証・品質の自動化
- 仕様レジストリ、検証結果、アーティファクト集約の仕組み
- Claude Code / CodeX などのエージェント統合の導線

### 5. 対象ユーザーと利用シーン
- プロダクト開発チーム（PM、開発、QA、運用）
- エージェントを開発フローに組み込むプロジェクト
- 仕様検証や重い品質テストを運用するチーム

### 6. 非対象
- エージェント実行ランタイムやIDEプラグインの提供
- ホスト型CI/CDサービスの提供
- UIテンプレートやフロントエンド専用のスターター
- Node.js/pnpm を導入できない実行環境のみのプロジェクト（現行CLIと `verify:lite` スクリプト（`pnpm run verify:lite`）を実行できない）
- CI成果物の保持や監査証跡を必要としない運用（ae-framework の主要価値が活かしにくい）

### 7. 前提条件（根拠）
- Node.js: `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm: `10.0.0`（`package.json` の `packageManager`）
- CI基盤: GitHub Actions（`.github/workflows/` に定義）

### 8. 導入の最小ステップ
1. 依存関係の導入: `pnpm install`
2. 開発フック: `pnpm run setup-hooks`
3. 最小検証: `pnpm run lint` と `pnpm run test:fast`

### 9. 現行全体像（2026-02-09 時点）
- **主要バイナリ**: `ae` / `ae-framework`、`ae-phase`、`ae-approve`、`ae-slash`、`ae-ui`、`ae-sbom`、`ae-resilience`、`ae-benchmark`、`ae-server`
- **運用方式**: `verify-lite` を必須ゲート、重い検証はラベル/dispatch で opt-in 実行（`.github/workflows/`）
- **形式検証スタック**: `verify:formal` で conformance/Alloy/TLA/SMT/Apalache/Kani/SPIN/CSP/Lean4 を非ブロッキング統合
- **CSP 拡張連携**: `verify:csp` が `cspx` を優先利用し、`csp-summary.json` と `cspx-result.json` を契約化（`schema_version=0.1` 前提）
- **集約の可観測性**: `formal-aggregate` が `backend/status/resultStatus/exitCode` をPR向けに集約表示
- **エージェント/MCP**: `src/mcp-server/*` に intent/test-generation/verify/spec-synthesis 等のサーバ実装
- **フロントエンド基盤**: `apps/web`、`apps/storybook`、`packages/ui`、`packages/design-tokens`
- **成果物の代表例**: `artifacts/hermetic-reports/formal/*.json`、`artifacts/hermetic-reports/conformance/summary.json`、`artifacts/progress/summary.json`、`reports/quality-gates/*`
- **設定体系**: `ae-framework.yml`（フェーズ/ガード）と `ae.config.*`（mode/ガード詳細）の二系統
- **公開境界**: npm export は `dist/src/index.js`、CLIは `bin` で公開（`package.json`）

### 10. 関連資料
- 詳細説明資料: `docs/product/DETAIL.md`
- 利用マニュアル: `docs/product/USER-MANUAL.md`
- 適用対象・入力/出力・ツール適性: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- 現行全体構成（実装準拠）: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- Minimal Adoption: `docs/product/MINIMAL-ADOPTION.md`
- 全体ナビゲーション: `docs/README.md`
- 構成と運用: `docs/project-organization.md`
- 位置づけ/比較: `docs/product/POSITIONING.md`
