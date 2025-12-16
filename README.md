# ae-framework: Agentic SDLC Orchestrator & Spec/Verification Kit

[![validate-artifacts-ajv](https://github.com/itdojp/ae-framework/actions/workflows/validate-artifacts-ajv.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/validate-artifacts-ajv.yml)
[![testing-ddd-scripts](https://github.com/itdojp/ae-framework/actions/workflows/testing-ddd-scripts.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/testing-ddd-scripts.yml)
[![coverage-check](https://github.com/itdojp/ae-framework/actions/workflows/coverage-check.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/coverage-check.yml)
[![pr-summary-comment](https://github.com/itdojp/ae-framework/actions/workflows/pr-summary-comment.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/pr-summary-comment.yml)

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese) | [Documentation / ドキュメント](#documentation-ドキュメント)

---

## English

ae-framework is a project skeleton plus verification toolkit that **orchestrates agent-driven SDLC work**. It standardises specifications, verification, and CI automation so human/agent collaboration stays auditable and repeatable.

### Positioning: SDLC governance & verification harness for agent-assisted development

ae-framework is a governance and verification harness for agent-assisted software development. It turns *specs*, *verification outputs*, and *regression signals* into **versioned, schema-validated artifacts** and enforces them in CI—so AI-assisted changes stay **auditable**, **reproducible**, and **policy-driven**.

How the existing building blocks map to enterprise needs:

- **Auditability / traceability**: traceable spec format + PR/CI reports make it possible to link **intent → implementation → tests → results**.
- **Reproducibility**: cached/snapshotted heavy-test artifacts and trend comparisons reduce “works on my machine” and help repeat the same checks over time.
- **SDLC governance**: CI quality gates (lint/test/type coverage, label gating, policies) make “what is allowed to merge” explicit and enforceable.
- **Risk control for AI-assisted changes**: mutation / MBT / property-based verification and nightly heavy tests surface regressions beyond unit tests.

### What this repository provides
- **Agentic SDLC orchestrator**: Ready-to-run GitHub Actions (PR verify, nightly heavy tests, Slack alerts) and CLI scripts that keep requirements, tests, and regression signals aligned.
- **Spec & Verification Kit**: Traceable spec format, mutation/MBT/property verification pipelines, and comparison tooling for heavy test trends (`scripts/pipelines/compare-test-trends.mjs`).
- **Project scaffolding & policies**: pnpm workspace layout, lint/test/type-coverage gates, label gating (typecov, flake), and TDD-friendly Git hooks.
- **Cacheable heavy test artifacts**: `scripts/pipelines/sync-test-results.mjs` to restore/store/snapshot mutation + MBT results; `heavy-test-trends` artifacts for CI triage.
- **Agent integrations**: Playbooks and connectors for Claude Code / CodeX; JSON-first outputs and AJV validation to keep agent-produced artifacts safe.

### What this is not
- Not an agent runtime or IDE plugin — bring your own agent.
- Not a general-purpose Next.js UI kit or design system starter.
- Not a hosted CI/CD service — workflows are provided for self-hosted GitHub runners or forks.

### Differentiation vs adjacent tool categories

| Category | Primary optimization | Typical gap in audit/compliance workflows | ae-framework’s role (difference) |
|---|---|---|---|
| **IDE copilots / coding agents** (e.g., Copilot/Cursor/Claude Code/CodeX) | Interactive coding speed and convenience | Intent, evidence, and regression signals are often **not standardized as artifacts**, and enforcement is outside the IDE | Works with any agent, but **standardizes artifacts + enforces verification gates in CI** so changes remain auditable/repeatable |
| **DevOps / CI platforms** (e.g., GitHub Actions/Harness/CircleCI/Buildkite) | Executing pipelines reliably at scale | Provide execution infrastructure, but not an opinionated **agentic spec→verification→evidence** workflow | Ships the **workflows/scripts/schemas** for agent-assisted SDLC governance; runs *on top of* your existing CI |
| **Agent frameworks** (e.g., LangChain/AutoGen/CrewAI) | Runtime orchestration, tool use, agent collaboration patterns | Strong on “how agents act,” weaker on “how organizations **prove** the change is safe” | Not a runtime. Provides the **verification + artifact discipline** that can wrap any agent runtime |

### Quick start (local)
```bash
# Prereqs: Node.js 20+, pnpm (corepack enable)
pnpm install
pnpm run setup-hooks

# Fast feedback
pnpm run lint
pnpm run test:fast

# Mutation quick run (mktemp-based; supports STRYKER_TEMP_DIR)
STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick

# Heavy test cache & trend snapshot
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/sync-test-results.mjs --snapshot
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

### Documentation pointers
- Overview & nav: `docs/README.md`, `docs/project-organization.md`
- CI/quality gates: `docs/ci/phase2-ci-hardening-outline.md`, `docs/ci/label-gating.md`
- Heavy test observability: `docs/ci/heavy-test-trend-archive.md`, `docs/ci/heavy-test-alerts.md`, `docs/ci/heavy-test-album.md`
- Specification & verification: `docs/quality/`, `docs/ci-policy.md`, `docs/testing/integration-runtime-helpers.md`
- Connectors & agent workflows: `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`, `docs/integrations/CODEX-INTEGRATION.md`

---

## Japanese

ae-framework は **エージェント協調型のSDLCオーケストレーター兼「仕様・検証キット」** です。指示・仕様・検証の流れを標準化し、エージェントと開発者が同じルールで再現性のある品質管理を行えるようにします。

### ポジショニング：エージェント支援開発の「SDLCガバナンス + 検証ハーネス」

ae-framework は、生成AI/エージェント支援開発向けの **ガバナンス/検証ハーネス**です。仕様（Spec）、検証結果、回帰シグナルを **バージョン管理可能かつスキーマ検証済みの成果物**として残し、CIで強制することで、AI混在の変更でも **監査可能性**・**再現性**・**統制（ガバナンス）**を確保しやすくします。

既存の構成要素を “市場に刺さる要件” に翻訳すると次の通りです。

- **監査/トレーサビリティ**: トレーサブルな仕様 + CIレポートにより、**意図 → 実装 → テスト → 結果**を追跡しやすい
- **再現性**: ヘビーテスト成果物のキャッシュ/スナップショットとトレンド比較で、同じ検証を継続的に回しやすい
- **SDLCガバナンス**: lint/test/型カバレッジ/ラベルゲーティング/ポリシーにより、「マージ可能条件」を明文化してCIで強制できる
- **AI混在変更のリスク低減**: mutation/MBT/property検証 + 夜間ヘビーテストで、ユニットテストだけでは見落としやすい退行を検知しやすい

### 提供するもの
- **SDLCオーケストレーター**: PR Verify／夜間ヘビーテスト／Slack通知などのGitHub ActionsとCLIスクリプトで、要件・テスト・退行検知を一元化。
- **仕様・検証キット**: トレーサブルな仕様フォーマット、mutation/MBT/Propertyテストのパイプライン、`scripts/pipelines/compare-test-trends.mjs` によるトレンド比較。
- **プロジェクト骨子とポリシー**: pnpmワークスペース、Lint/Test/型カバレッジのゲート、ラベルゲーティング（typecov・flake）、TDDフック。
- **ヘビーテスト成果物のキャッシュ**: `scripts/pipelines/sync-test-results.mjs` による store/restore/snapshot、`heavy-test-trends` アーティファクトでCIトリアージを高速化。
- **エージェント統合指針**: Claude Code / CodeX 向けプレイブック、JSON成果物のAJV検証など、エージェント生成物を安全に扱うための手順。

### 提供しないもの
- エージェント実行ランタイムやIDEプラグイン（各自のエージェントを利用）。
- 汎用のNext.js UIスターターやデザインシステム配布物。
- ホスト型CI/CDサービス（GitHub Actionsの定義を提供）。

### 競合カテゴリとの差分（隣接ツールとの棲み分け）

| カテゴリ | 主な最適化対象 | 監査/コンプライアンス観点での典型的な弱点 | ae-framework の位置づけ（差分） |
|---|---|---|---|
| **IDE系コーディング支援/エージェント**（例: Copilot/Cursor/Claude Code/CodeX） | 対話的な実装速度・操作性 | 仕様・証跡・回帰指標が **標準化された成果物として残りにくい**／強制はIDE外に出がち | エージェントは選べる前提で、**成果物標準化 + 検証ゲートをCIで強制**し監査/再現性を担保しやすくする |
| **DevOps/CI基盤**（例: GitHub Actions/Harness/CircleCI/Buildkite） | パイプライン実行の信頼性・スケール | 実行基盤は提供するが、エージェント支援開発の **spec→検証→証跡** を一貫させる作法は別途必要 | 既存CI上で動く **ワークフロー/スクリプト/スキーマ** を提供し、エージェント支援SDLCの統制を実装する |
| **Agent framework系**（例: LangChain/AutoGen/CrewAI） | エージェント実行/協調/ツール利用の設計 | 「どう動かすか」は強いが、「変更が安全だと **証明**する運用（証跡/ゲート）」は弱くなりがち | ランタイムではなく、任意のエージェント実行系を **検証・成果物規律** で包むレイヤ |

### すぐ試す
```bash
# 前提: Node.js 20+, pnpm (corepack enable)
pnpm install
pnpm run setup-hooks

pnpm run lint
pnpm run test:fast

# Mutation quick（mktemp利用、STRYKER_TEMP_DIR対応）
STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick

# ヘビーテスト結果のキャッシュ運用
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/sync-test-results.mjs --snapshot
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

### ドキュメントへの入り口
- 全体概要: `docs/README.md`, `docs/project-organization.md`
- CI/品質ゲート: `docs/ci/phase2-ci-hardening-outline.md`, `docs/ci/label-gating.md`
- ヘビーテスト観測: `docs/ci/heavy-test-trend-archive.md`, `docs/ci/heavy-test-alerts.md`, `docs/ci/heavy-test-album.md`
- 仕様と検証: `docs/ci-policy.md`, `docs/testing/integration-runtime-helpers.md`, `docs/quality/`
- エージェント統合: `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`, `docs/integrations/CODEX-INTEGRATION.md`

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

- Full navigation: `docs/README.md`
- Quick starts: `docs/getting-started/QUICK-START-GUIDE.md`, `docs/getting-started/PHASE-6-GETTING-STARTED.md`
- CLI Reference: `docs/reference/CLI-COMMANDS-REFERENCE.md`, API: `docs/reference/API.md`

## 🤝 Contributing / 貢献

We welcome contributions! See [CONTRIBUTING.md](CONTRIBUTING.md).
貢献を歓迎します！詳細は[CONTRIBUTING.md](CONTRIBUTING.md)をご覧ください。

## 📄 License / ライセンス

MIT License - see [LICENSE](LICENSE).

## 🙏 Acknowledgments

Built with: MCP SDK, Claude/CodeX task tools, pnpm workspace, Vitest, AJV, GitHub Actions.

---

ae-framework — automating agentic specification, verification, and CI quality gates.
