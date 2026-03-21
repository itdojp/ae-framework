---
docRole: derived
canonicalSource:
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
- README.md
lastVerified: '2026-03-22'
---
# ae-framework 概要説明資料

> Language / 言語: English | 日本語

---

## English

### 1. Purpose and Positioning
`ae-framework` is an assurance control plane for agent-driven SDLC. It standardizes the flow from requirements to verification, evidence, and PR / release decisions so that teams can operate with auditability and reproducibility.

### 2. Problems It Addresses
- Broken handoffs between requirements, specifications, tests, and CI decisions
- Weak reproducibility for heavy verification and delayed regression detection
- Inconsistent artifact quality when multiple agents participate in delivery

### 3. Value Proposition
- Scripts and workflows that keep specifications and verification in one operating model
- Visibility for quality gates, evidence, and traceability outputs
- Small, reversible PR operations with CI optimization and opt-in heavy checks

### 4. Main Building Blocks
- GitHub Actions workflows as the primary CI execution surface
- CLI commands and scripts for specification, verification, and quality automation
- Decision artifacts such as `assurance-summary`, `quality-scorecard`, `hook-feedback`, and `ae-handoff`
- Specification registry and aggregation using `Context Pack`, `boundary-map`, and `change-package`
- Policy automation through `policy-gate`, `gate`, and release / post-deploy summaries
- Integration paths for agent operators such as Claude Code and Codex

### 5. Target Users and Scenarios
- Product delivery teams across PM, engineering, QA, and operations
- Projects that introduce agents into the development workflow
- Teams that need specification-driven validation, heavy quality checks, or evidence retention

### 6. Non-goals
- Agent runtimes or IDE plugins
- Hosted CI/CD as a service
- UI starter kits or frontend-only scaffolds
- Environments that cannot run the current Node.js / pnpm toolchain required by `pnpm run verify:lite`
- Operating models that do not need retained CI evidence or audit trails

### 7. Prerequisites
- Node.js: `>=20.11 <23` (`package.json` `engines.node`)
- pnpm: `10.0.0` (`package.json` `packageManager`)
- CI surface: GitHub Actions (`.github/workflows/`)

### 8. Minimum Adoption Path
1. Install dependencies with `pnpm install`
2. Set up hooks with `pnpm run setup-hooks`
3. Run the minimum checks: `pnpm run lint` and `pnpm run test:fast`

### 9. Current System Snapshot (as of 2026-03-22)
- Main PR baseline on `main`: `verify-lite`, `policy-gate`, and `gate`
- Formal verification stack consolidated behind `pnpm run verify:formal`
- Assurance control plane artifacts generated under `artifacts/assurance/`, `artifacts/quality/`, `artifacts/agents/`, and `artifacts/handoff/`
- Context Pack boundary management available through `spec/context-pack/boundary-map.json` and `pnpm run context-pack:verify-boundary-map`
- Policy evaluation supports staged migration with JS decisions and OPA shadow comparison
- Frontend / UI support lives under `apps/web`, `apps/storybook`, `packages/ui`, and `packages/design-tokens`

### 10. Related Documents
- Detailed guide: `docs/product/DETAIL.md`
- User manual: `docs/product/USER-MANUAL.md`
- Product-fit / input-output map: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- Input-only repository pattern: `docs/product/INPUT-ONLY-SPEC-REPO-PATTERN.md`
- Current implementation overview: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- Minimal adoption guide: `docs/product/MINIMAL-ADOPTION.md`
- Full docs index: `docs/README.md`
- Positioning and comparison: `docs/product/POSITIONING.md`

---

## 日本語

### 1. 目的と位置づけ
ae-framework は、エージェント協調型のSDLCを実行するための **assurance control plane** です。要求から検証、証跡、PR / release 判断までの流れを標準化し、監査可能で再現性のある品質管理を実現します。

### 2. 解決する課題
- 要件・仕様・テスト・CIの断絶による品質管理の不整合
- 大規模検証の再現性不足と退行検知の遅延
- エージェント活用時の成果物品質のばらつき

### 3. 提供価値
- 仕様と検証の一貫運用を可能にするスクリプトとワークフロー
- 品質ゲート、証跡、トレーサビリティの可視化
- 小さなPR単位での可逆運用とCI最適化

### 4. 主な構成要素
- GitHub Actions を中心としたCIワークフロー群
- CLIとスクリプトによる仕様・検証・品質の自動化
- `assurance-summary`、`quality-scorecard`、`hook-feedback`、`ae-handoff` などの判断用 artifact
- `Context Pack` / `boundary-map` / `change-package` を使った仕様レジストリと検証結果の集約
- `policy-gate`、`gate`、release/post-deploy summary による判断面の自動化
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

### 9. 現行全体像（2026-03-14 時点）
- **主要バイナリ**: `ae` / `ae-framework`、`ae-phase`、`ae-approve`、`ae-slash`、`ae-ui`、`ae-sbom`、`ae-resilience`、`ae-benchmark`、`ae-server`
- **Required checks**: `verify-lite`、`policy-gate`、`gate` を main branch の日常PRゲートとして運用
- **運用方式**: `verify-lite` を基準ゲートとし、重い検証はラベル/dispatch で opt-in 実行（`.github/workflows/`）
- **形式検証スタック**: `verify:formal` で conformance/Alloy/TLA/SMT/Apalache/Kani/SPIN/CSP/Lean4 を非ブロッキング統合
- **CSP 拡張連携**: `verify:csp` が `cspx` を優先利用し、`csp-summary.json` と `cspx-result.json` を契約化（`schema_version=0.1` 前提）
- **assurance control plane**: `artifacts/assurance/assurance-summary.json`、`artifacts/quality/quality-scorecard.json`、`artifacts/agents/hook-feedback.json`、`artifacts/handoff/ae-handoff.json` を判断用 artifact として生成
- **Context Pack 境界管理**: `spec/context-pack/boundary-map.json` と `pnpm run context-pack:verify-boundary-map` により、slice 依存と循環を任意実行で検証
- **ポリシー評価**: `policy-gate.yml` が JS decision と OPA shadow compare を併記し、`AE_POLICY_ENGINE_MODE` で段階移行
- **集約の可観測性**: `formal-aggregate` が `backend/status/resultStatus/exitCode` をPR向けに集約表示し、`automation-observability-weekly` が SLO / MTTR を継続観測
- **エージェント/MCP**: `src/mcp-server/*` に intent/test-generation/verify/spec-synthesis 等のサーバ実装
- **フロントエンド基盤**: `apps/web`、`apps/storybook`、`packages/ui`、`packages/design-tokens`
- **成果物の代表例**: `artifacts/hermetic-reports/formal/*.json`、`artifacts/hermetic-reports/conformance/summary.json`、`artifacts/quality/quality-scorecard.json`、`artifacts/agents/hook-feedback.json`、`artifacts/handoff/ae-handoff.json`
- **設定体系**: `ae-framework.yml`（フェーズ/ガード）と `ae.config.*`（mode/ガード詳細）の二系統
- **公開境界**: npm export は `dist/src/index.js`、CLIは `bin` で公開（`package.json`）

### 10. 関連資料
- 詳細説明資料: `docs/product/DETAIL.md`
- 利用マニュアル: `docs/product/USER-MANUAL.md`
- 適用対象・入力/出力・ツール適性: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- 入力のみリポジトリ・パターン（ベンチ/評価用途）: `docs/product/INPUT-ONLY-SPEC-REPO-PATTERN.md`
- 現行全体構成（実装準拠）: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- Minimal Adoption: `docs/product/MINIMAL-ADOPTION.md`
- 全体ナビゲーション: `docs/README.md`
- 構成と運用: `docs/project-organization.md`
- 位置づけ/比較: `docs/product/POSITIONING.md`
