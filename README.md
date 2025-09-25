# ae-framework: AI-Agent Enabled Framework

[![validate-artifacts-ajv](https://github.com/itdojp/ae-framework/actions/workflows/validate-artifacts-ajv.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/validate-artifacts-ajv.yml)
[![workflow-lint](https://github.com/itdojp/ae-framework/actions/workflows/workflow-lint.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/workflow-lint.yml)
[![testing-ddd-scripts](https://github.com/itdojp/ae-framework/actions/workflows/testing-ddd-scripts.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/testing-ddd-scripts.yml)
[![coverage-check](https://github.com/itdojp/ae-framework/actions/workflows/coverage-check.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/coverage-check.yml)
[![pr-summary-comment](https://github.com/itdojp/ae-framework/actions/workflows/pr-summary-comment.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/pr-summary-comment.yml)

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese) | [Documentation / ドキュメント](#documentation-ドキュメント)

---

## English

Note: Top-level documentation has been consolidated under `docs/` to keep the repository root tidy.

**AI-Agent Enabled Framework for Test-Driven Development with 6-Phase Automation**

> Minimal human intervention, maximum specification compliance. Intent → Formal → Tests → Code → Verify → Operate with TDD enforcement.

### 🚀 Key Features

- **Complete Claude Code Integration**: All 6 phases automated through Task Tool adapters
- **TDD Enforcement**: Automatic Test-Driven Development compliance
- **OpenTelemetry Monitoring**: Real-time quality and performance metrics
- **Phase 6 UI Generation**: React + Next.js components in <30 seconds
- **Bilingual Support**: Japanese/English documentation and UI

### 🤖 Claude Code Task Tool Integration (All Phases)

#### Full Automation
ae-framework provides **complete 6-phase automation** in Claude Code environment without additional configuration:

**Phase 1: Intent Analysis** 🎯
```
User: Please analyze the project requirements

Claude Code: Executing Intent Task Adapter for requirement analysis...

✅ Intent Analysis Complete - 12 requirements identified
📋 Next steps:
  • Proceed to Phase 2 (Natural Language Requirements)
```

**Phase 6: UI/UX & Frontend Delivery** 🎨
```
User: Generate UI components

Claude Code: Executing UI Task Adapter for component generation...

📊 OpenTelemetry initialized for ae-framework Phase 6
✅ Generated 21 files for 3/3 entities
📊 Test Coverage: 100% (threshold: 80%)
♿ A11y Score: 96% (threshold: 95%) ✅  
⚡ Performance Score: 78% (threshold: 75%) ✅
```

### 🎯 6-Phase Workflow

1. **Intent Analysis**: Extract requirements from natural language
2. **Natural Language Requirements**: Structure and validate requirements
3. **User Stories Creation**: Generate user stories and acceptance criteria
4. **Validation**: Cross-validate requirements, stories, and specifications
5. **Domain Modeling**: Create domain-driven design models
6. **UI/UX & Frontend Delivery**: Generate React components with testing

### 📦 Quick Start

```bash
# Install framework
npm install ae-framework

# Initialize project with TDD
ae-framework init my-project --tdd

# Generate complete feature
ae-framework feature "User Authentication"
ae-framework generate:tests  # RED phase
ae-framework generate:code   # GREEN phase
ae-framework verify         # Quality verification
ae-framework ui-scaffold --components  # UI generation
```

### 🎨 Phase 6: UI/UX Features

- **React + Next.js**: Modern component generation
- **Design System**: Radix UI + Tailwind CSS + Design Tokens
- **Accessibility**: WCAG 2.1 AA compliance (96% score)
- **Testing**: Playwright E2E + Storybook + Vitest
- **i18n**: Multi-language support (ja/en)
- **OpenTelemetry**: Real-time quality monitoring

### 📊 Quality Gates & Metrics

- ✅ Test Coverage: ≥80%
- ✅ A11y Score: ≥95% (WCAG 2.1 AA)
- ✅ Performance Score: ≥75% (Lighthouse CI)
- ✅ TypeScript: Zero type errors, strict mode
- ✅ ESLint: Zero syntax errors

Type Coverage Policy
- Baseline: 65% is measured and commented on PRs.
- Label-gated enforcement: Add PR label `enforce-typecov` to enforce 70% (CI fails if below).
- Details: see `docs/quality/type-coverage-policy.md`.

Error Handling Policy (CLI)
- Unknown-first error handling across CLI: `catch (error: unknown)` + `toMessage(error)` for safe formatting
- Unified error prefix: `❌ <short prefix>: <message>` with chalk.red
- Static import for `error-utils` to improve type-safety and bundling

### 🤝 Contributing

We welcome international contributions! Please see our [Contributing Guide](CONTRIBUTING.md).

### 📚 Documentation

- [Quick Start Guide](docs/getting-started/QUICK-START-GUIDE.md)
- [Claude Code Integration](docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)
- [CodeX Integration](docs/integrations/CODEX-INTEGRATION.md)
  - [CodeX Quick Start](docs/integrations/QUICK-START-CODEX.md)
- [API Reference](docs/reference/API.md)
- [CLI Commands](docs/reference/CLI-COMMANDS-REFERENCE.md)

### 🧪 CI Quick Guide

- Minimal checks locally
  - `pnpm run test:unit` / `pnpm run test:fast`
  - Benchmark focused tests: see `docs/handoff/README.md`
  - Quality gates may fail depending on environment/policy
    - Use `ae-framework quality run --env development --dry-run` for smoke
    - Type coverage policy is reported at 65% baseline; `enforce-typecov` label enforces 70%
    - Some jobs (security/audit/container) require network/secrets and may be red on forks
    - Workflow lint & printf policy:
      - Run guard + actionlint locally: `pnpm lint:workflows` (guard always runs; actionlint via Docker if available)
      - No Docker? Use `pnpm lint:workflows:nodocker` (guard + self-test; actionlint runs in CI)
      - See potential conversions: `pnpm ci:guard:suggest` (non-destructive suggestions)
      - Run basic guard self-test locally: `pnpm ci:test:guard`
      - Run guard + self-test in one command: `pnpm ci:guard:all`
      - When appending to `$GITHUB_OUTPUT`/`$GITHUB_ENV`, use `printf` and quote the target file:
        - `printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"`
        - `printf "%s\n" "NAME=value" >> "$GITHUB_ENV"`
        - Grouped appends are allowed:
          ```bash
        {
          printf "%s\n" "one=1"
          printf "%s\n" "two=2"
        } >> "$GITHUB_OUTPUT"
        ```
      - Quick conversions: see `docs/ci/echo-to-printf-recipes.md`
    - See `docs/ci-policy.md` for details

---

## Japanese

注記: ルート直下のドキュメントを `docs/` 配下に整理し、トップ階層をスリム化しました。

**TDD強制機能付き6フェーズ自動化のAIエージェント対応フレームワーク**

> 人手最小＆仕様準拠最大。Intent→Formal→Tests→Code→Verify→Operate の6フェーズ。

### 📢 最新アップデート
- **🆕 [🧪 Phase 2.3: Integration Testing System](./docs/phases/PHASE-2-3-INTEGRATION-TESTING.md)** - 包括的統合テストとE2Eテストオーケストレーション
- **🆕 [🛡️ Phase 2.2: Runtime Conformance System](./docs/phases/PHASE-2-2-RUNTIME-CONFORMANCE.md)** - リアルタイム適合性検証とCEGIS連携
- **[🔧 Phase 2.1: CEGIS Auto-Fix System](./docs/architecture/CEGIS-DESIGN.md)** - 反例誘導帰納合成による自動コード修復
- **[🎨 Phase 6 UI/UX & Frontend Delivery完全実装](./docs/phases/phase-6-uiux.md)** - React + Next.js UI自動生成とOpenTelemetryテレメトリ
- **[🚀 Phase 2-5 Claude Code Task Tool統合](./docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - 全フェーズの完全自動化を実現

### 🔧 Claude Code Task Tool 統合（全フェーズ対応）

#### 🚀 完全自動統合
ae-framework は Claude Code 環境で**全6フェーズ**を自動統合。追加設定なしで利用可能：

**Phase 1: Intent Analysis 🎯**
```

### 📁 Repository Layout
- Overview: `docs/README.md`
- Project organization: `docs/project-organization.md`
- Architecture notes: `docs/architecture/`
- Quality and verification: `docs/quality/`
- Benchmarks (req2run): `docs/benchmark/`
- Articles: `docs/articles/` (e.g., Zenn)
- CLI smoke example: `examples/cli-smoke/`
User: プロジェクトの要件分析をお願いします

Claude Code: Intent Task Adapterを使用して要件分析を実行します...

✅ Intent Analysis Complete - 12 requirements identified
📋 Next steps:
  • Proceed to Phase 2 (Natural Language Requirements)
```

**Phase 6: UI/UX & Frontend Delivery 🎨**
```
User: UI コンポーネントを生成してください

Claude Code: UI Task Adapterでコンポーネント生成中...

📊 OpenTelemetry initialized for ae-framework Phase 6
✅ Generated 21 files for 3/3 entities
📊 Test Coverage: 100% (threshold: 80%)
♿ A11y Score: 96% (threshold: 95%) ✅  
⚡ Performance Score: 78% (threshold: 75%) ✅
```

### CLI実行も全フェーズ対応
```bash
# Phase 1: Intent分析
ae-framework intent --analyze --sources="requirements.md"

# Phase 6: UI/UX & Frontend Delivery
ae-framework ui-scaffold --components
ae-framework ui-scaffold --state
ae-framework ui-scaffold --tokens
ae-framework ui-scaffold --a11y

# ae-ui エイリアス（同等の動作）
ae-ui scaffold --components
ae-ui scaffold --state  
ae-ui scaffold --tokens
ae-ui scaffold --a11y
```

### 🎯 主要機能

#### 🤖 AI-Powered Development Features

**🤖 Test Generation Agent (NEW!)**
自動的に包括的なテストを生成する AI エージェント：
- **要件からテスト生成**: 自然言語の要件から完全なテストスイートを作成
- **コードからテスト逆生成**: 既存コードを分析してテストを生成（リバースTDD）
- **Property-Based Testing**: 数学的性質からプロパティテストを自動設計
- **BDD シナリオ生成**: ユーザーストーリーから Gherkin シナリオを作成

**🛡️ TDD Enforcement Features**
TDD（Test-Driven Development）原則の遵守を自動的に強制：
- **TDD Guard**: コードファイルに対応するテストファイルの存在を強制
- **Test Execution Guard**: コミット前の全テスト通過を確認
- **RED-GREEN Cycle Guard**: RED→GREEN→REFACTORサイクルの遵守をチェック
- **Coverage Guard**: 最低カバレッジ（80%）の維持を監視

### 🎨 Phase 6: UI/UX & Frontend Delivery

#### 品質ゲート（概要）
- 型カバレッジ: 基準65%（PRコメント報告）、ラベル `enforce-typecov` 付与時に70%を強制（未満でCI失敗）。
- 詳細は `docs/quality/type-coverage-policy.md` を参照してください。

エラーハンドリング方針（CLI）
- 全CLIで unknown-first: `catch (error: unknown)` + `toMessage(error)` による安全な整形
- エラー出力の統一: `❌ <短い前置き>: <本文>`（chalk.red）
- `error-utils` は静的 import 化（型安全性とバンドル最適化）

### 🧪 CI クイックガイド

- ローカルでの最小確認
  - `pnpm run test:unit` / `pnpm run test:fast`
  - ベンチマーク系の重点テストは `docs/handoff/README.md` を参照
- Quality Gates は環境/ポリシーによりREDになる場合があります
  - `ae-framework quality run --env development --dry-run` でスモーク
  - 型カバレッジは65%基準のレポート、`enforce-typecov` ラベルで70%強制
  - セキュリティ/監査/コンテナ系はネットワーク・シークレット前提のためフォーク環境ではREDになり得ます

**OpenTelemetryテレメトリ監視**
Phase 6では**OpenTelemetry**を使用してリアルタイム品質監視を実行：

**監視メトリクス:**
- **品質メトリクス**: テストカバレッジ(≥80%)、A11yスコア(≥95%)、パフォーマンススコア(≥75%)
- **効率性メトリクス**: スキャフォールド時間(<30秒)、E2Eテスト時間(<5分)、ビルド時間
- **保守性メトリクス**: コンポーネント複雑度(<10)、未使用CSS率(<5%)、デザイントークン使用率(≥95%)

**生成されるファイル構成**
```

### 📁 リポジトリ構成
- 概要: `docs/README.md`
- プロジェクト構成: `docs/project-organization.md`
- アーキテクチャ: `docs/architecture/`
- 品質と検証: `docs/quality/`
- ベンチマーク（req2run）: `docs/benchmark/`
- 記事: `docs/articles/`（Zenn など）
- CLI スモーク例: `examples/cli-smoke/`
ae-framework/
├── packages/
│   ├── design-tokens/                       # デザイントークン
│   └── ui/                                  # UIコンポーネントライブラリ
├── apps/
│   ├── web/                                 # Next.js Webアプリケーション
│   │   ├── app/{entity}/page.tsx            # 一覧ページ
│   │   ├── app/{entity}/[id]/page.tsx       # 詳細ページ
│   │   ├── messages/ja.json                 # 日本語翻訳
│   │   ├── messages/en.json                 # 英語翻訳
│   │   └── __e2e__/{entity}.spec.ts         # E2Eテスト
│   └── storybook/                           # Storybookドキュメント
└── templates/ui/                            # Handlebarsテンプレート
```

**技術仕様:**
- **Framework**: Next.js 14 App Router
- **UI Library**: Radix UI + Tailwind CSS + shadcn/ui  
- **Design System**: Design Tokens + Class Variance Authority (CVA)
- **Forms**: React Hook Form + Zod validation
- **State**: TanStack Query 5 for server state
- **Testing**: Playwright E2E + Storybook + Vitest
- **i18n**: next-intl 多言語対応 (ja/en)
- **A11y**: WCAG 2.1 AA準拠 + eslint-plugin-jsx-a11y
- **Telemetry**: OpenTelemetry for quality metrics

### 📦 Installation

```bash
# Node.js 20+ required
# (optional) Enable Corepack to use bundled pnpm
# corepack enable
pnpm install

# Install Git hooks for TDD enforcement
pnpm run setup-hooks

# Build the framework
pnpm run build
```

### 🚀 Quick Start

```bash
# 1. Initialize a new project with TDD enforcement
ae-framework init my-project --tdd

# 2. Create a feature specification
ae-framework feature "User Authentication"

# 3. Generate tests (Phase 3 - RED)
ae-framework generate:tests

# 4. Generate implementation (Phase 4 - GREEN)
ae-framework generate:code

# 5. Verify quality (Phase 5)
ae-framework verify

# 6. Generate UI Components (Phase 6)
ae-framework ui-scaffold --components
# または
ae-ui scaffold --components

# 7. Deploy (Phase 6)
ae-framework deploy
```

---

## 🔒 TypeScript Policy / TypeScript ポリシー

### @ts-expect-error Usage Policy

When using `@ts-expect-error` comments, follow this structured format:

```typescript
// @ts-expect-error owner:@username expires:YYYY-MM-DD reason: detailed description
```

**Required fields:**
- `owner:@username` - GitHub handle responsible for the suppression
- `expires:YYYY-MM-DD` - Date when this suppression should be reviewed/removed
- `reason: description` - Detailed explanation (minimum 12 characters)

**Examples:**
```typescript
// @ts-expect-error owner:@alice expires:2025-12-31 reason: narrowing todo for complex union
const result = complexUnion as string;

// @ts-expect-error owner:@bob expires:2025-06-15 reason: legacy API compatibility until v2 migration
legacyApi.unsafeMethod(data);
```

**Policy enforcement:**
- ✅ CI validates all `@ts-expect-error` comments
- ⚠️ Local development shows warnings only
- 🔍 Script: `node scripts/ci/check-expect-error.mjs`

---

## Documentation / ドキュメント

### 🚀 Getting Started / 導入・クイックスタート
- **[🚀 Quick Start Guide](docs/getting-started/QUICK-START-GUIDE.md)** - 15分で始めるae-framework / 15-minute ae-framework introduction
- **[🎨 Phase 6 Getting Started](docs/getting-started/PHASE-6-GETTING-STARTED.md)** - UI/UX専用クイックスタート / UI/UX focused quick start
- [Setup Guide](docs/getting-started/SETUP.md) - 基本セットアップ / Basic setup

### 📝 Practical Guides / 実用ガイド
- **[🎯 Development Instructions Guide](docs/guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md)** - 実際の開発指示方法 / Practical development instruction methods
- **[🚀 Claude Code Automation Guide](docs/guides/CLAUDE-CODE-AUTOMATION-GUIDE.md)** - 要求から実装まで完全自動化 / Complete automation from requirements to implementation
- [Usage Guide](docs/guides/USAGE.md) - 一般的な使い方ガイド / General usage guide

### 🎯 Phase-by-Phase Details / フェーズ別詳細
- [Phase 2: Natural Language Requirements](docs/phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md) - 自然言語要件処理 / Natural language requirement processing
- **🆕 [Phase 2.1: CEGIS Auto-Fix System](docs/architecture/CEGIS-DESIGN.md)** - 反例誘導帰納合成による自動コード修復 / Counterexample-guided inductive synthesis for automatic code repair
- **🆕 [Phase 2.2: Runtime Conformance System](docs/phases/PHASE-2-2-RUNTIME-CONFORMANCE.md)** - リアルタイム適合性検証とCEGIS連携 / Real-time conformance verification and CEGIS integration
- **🆕 [Phase 2.3: Integration Testing System](docs/phases/PHASE-2-3-INTEGRATION-TESTING.md)** - 包括的統合テストとE2Eテストオーケストレーション / Comprehensive integration and E2E test orchestration
- **[Phase 6: UI/UX & Frontend Delivery](docs/phases/phase-6-uiux.md)** - React + Next.js UI自動生成 / React + Next.js UI automatic generation

### 🔗 Integration & Workflow / 統合・ワークフロー
- **[Claude Code Task Tool Integration](docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - 全フェーズ統合詳細 / Complete phase integration details
- [Claude Code Workflow](docs/integrations/CLAUDECODE-WORKFLOW.md) - Claude Codeワークフロー / Claude Code workflow

### 📚 Reference / リファレンス
- **[CLI Commands Reference](docs/reference/CLI-COMMANDS-REFERENCE.md)** - 全コマンドリファレンス / Complete command reference
- [API Reference](docs/reference/API.md) - API仕様 / API specifications

### 🏗️ Architecture & Design / アーキテクチャ・設計
- **[TDD Framework Architecture](docs/architecture/TDD-FRAMEWORK-ARCHITECTURE.md)** - TDDフレームワーク設計 / TDD framework design
- [System Architecture](docs/architecture/ARCHITECTURE.md) - システムアーキテクチャ / System architecture

### 📚 Complete Navigation / 全体ナビゲーション
**[docs/README.md](docs/README.md)** - 全ドキュメントの体系的ナビゲーションガイド / Systematic documentation navigation guide

---

## 🤝 Contributing

We welcome contributions! Please see our [Contributing Guide](CONTRIBUTING.md) for details.
貢献を歓迎します！詳細は[コントリビューションガイド](CONTRIBUTING.md)をご覧ください。

## 📄 License

MIT License - see [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

Built with:
- MCP SDK for agent communication
- OpenAI/Anthropic APIs for AI capabilities
- Next.js 14 + React 18 for UI generation
- Radix UI + Tailwind CSS for design system
- OpenTelemetry for telemetry and monitoring
- Vitest for testing framework

### CI Gate
- PR: `PR Verify` workflow runs `ae verify`, replay smoke, uploads artifacts (14d retention).
- Nightly: `nightly-monitoring` runs flake(×30) and compares two seeded benches (≤5%) at JST 04:15.
- Replay policy: PR=**replay** by default, main/nightly may record separately if needed.
- Required check: set **PR Verify / verify** as a required status in branch protection (use `./scripts/setup-branch-protection.sh`).
- Slack alerts: verify/nightly failures notify Slack (requires `SLACK_WEBHOOK_URL` secret).

#### Verification Environment Controls
- `AE_TYPES_STRICT=1`: CI strict mode (failures exit 1), `0` for local soft mode (warnings only)
- `AE_LINT_SCOPE`: ESLint scope pattern (default: `"src/{providers,commands}/**/*.ts"`)
- `AE_TSC_PROJECT`: TypeScript project config (default: `"tsconfig.verify.json"`)
- `AE_EXPECT_ERROR_STRICT=1`: Enable @ts-expect-error policy enforcement (default: enabled)

#### Benchmark Policy
- Default tolerance: 5% for performance regression detection
- Environment override: Set `BENCH_TOLERANCE` to customize (takes priority over command arguments)
- Nightly monitoring: Automated bench comparison with seeded runs for consistency

#### Flake Detection Policy
- Default: 5-10 runs for standard flake detection
- Opt-in extended testing: Add `run-flake` label to PR for 20-30 runs (statistical analysis)
- Extended flake tests use `continue-on-error: true` to avoid blocking PR merges

#### Cassette Policy
- **Generated cassettes** (`artifacts/cassettes/`): Never commit (build artifacts, ignore in git)
- **Fixed cassettes** (if needed): Use `cassettes/fixtures/` with mandatory code review
- **PR policy**: New cassettes OK, existing cassette changes require review
- **Alternative storage**: Consider separate repo or Git LFS for large cassette collections

#### Slack Alerts Setup
1. Go to repository **Settings** → **Secrets and variables** → **Actions**
2. Click **New repository secret**
3. Name: `SLACK_WEBHOOK_URL`, Value: your Slack webhook URL
4. Save - failures will now trigger Slack notifications
5. If secret is not set, notification step is automatically skipped

---

**ae-framework** - Automating excellence through AI-driven development 🚀

<!-- PR#269 merge verification -->
