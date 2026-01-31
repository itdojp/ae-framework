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

### 7. 前提条件（根拠）
- Node.js: `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm: `10.0.0`（`package.json` の `packageManager`）
- CI基盤: GitHub Actions（`.github/workflows/` に定義）

### 8. 導入の最小ステップ
1. 依存関係の導入: `pnpm install`
2. 開発フック: `pnpm run setup-hooks`
3. 最小検証: `pnpm run lint` と `pnpm run test:fast`

### 9. 関連資料
- 詳細説明資料: `docs/product/DETAIL.md`
- 利用マニュアル: `docs/product/USER-MANUAL.md`
- 典型的な利用シナリオ: `docs/product/USE-CASES.md`
- 全体ナビゲーション: `docs/README.md`
- 構成と運用: `docs/project-organization.md`
- コマンド体系（実行モード別）: `docs/product/COMMAND-MODES.md`
