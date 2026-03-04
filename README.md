# ae-framework: Agentic SDLC Orchestrator & Spec/Verification Kit

[![validate-artifacts-ajv](https://github.com/itdojp/ae-framework/actions/workflows/validate-artifacts-ajv.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/validate-artifacts-ajv.yml)
[![testing-ddd-scripts](https://github.com/itdojp/ae-framework/actions/workflows/testing-ddd-scripts.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/testing-ddd-scripts.yml)
[![coverage-check](https://github.com/itdojp/ae-framework/actions/workflows/coverage-check.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/coverage-check.yml)
[![pr-ci-status-comment](https://github.com/itdojp/ae-framework/actions/workflows/pr-ci-status-comment.yml/badge.svg)](https://github.com/itdojp/ae-framework/actions/workflows/pr-ci-status-comment.yml)

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese) | [Documentation / ドキュメント](#documentation-ドキュメント)

---

## English

ae-framework is a project skeleton plus verification toolkit that **orchestrates agent-driven SDLC work**. It standardises specifications, verification, and CI automation so human/agent collaboration stays auditable and repeatable.

### What this repository provides
- **Agentic SDLC orchestrator**: Ready-to-run GitHub Actions (PR verify / verify-lite, nightly heavy tests, Slack alerts) and CLI scripts that keep requirements, tests, and regression signals aligned.
- **Spec & Verification Kit**: Traceable spec format, mutation/MBT/property verification pipelines, and formal runners for Alloy/TLA/SMT/Apalache/Kani/SPIN/CSP(cspx)/Lean4 with unified summaries.
- **Project scaffolding & policies**: pnpm workspace layout, lint/test/type-coverage gates, label gating (typecov, flake), and TDD-friendly Git hooks.
- **Cacheable heavy test artifacts**: `scripts/pipelines/sync-test-results.mjs` to restore/store/snapshot mutation + MBT results; `heavy-test-trends` artifacts for CI triage.
- **Agent integrations**: Playbooks and connectors for Claude Code / CodeX; JSON-first outputs and AJV validation to keep agent-produced artifacts safe.

### What this is not
- Not an agent runtime or IDE plugin — bring your own agent.
- Not a general-purpose Next.js UI kit or design system starter.
- Not a hosted CI/CD service — workflows are provided for self-hosted GitHub runners or forks.

### Quick start (local)
```bash
# Prereqs: Node.js 20.11+ (<23), pnpm 10
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install
pnpm run first-run
pnpm run setup-hooks

# Fast feedback
pnpm run lint
pnpm run test:fast

# Mutation quick run (mktemp-based; supports STRYKER_TEMP_DIR)
STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick
# If report generation is intentionally optional, set MUTATION_REPORT_STRICT=0

# Formal smoke (non-blocking summary; cspx backend preferred)
pnpm run verify:formal
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck

# Heavy test cache & trend snapshot
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/sync-test-results.mjs --snapshot
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

> `npm install` is intentionally blocked by `preinstall` because this repository uses `pnpm` workspace dependencies (`workspace:*`).
> `pnpm run doctor:env` writes `artifacts/doctor/env.json` and returns `0` (ok) / `2` (warning) / `1` (error) / `3` (invalid arguments).
> `pnpm run first-run` runs `doctor:env -> build -> verify:lite` and writes summary JSON/Markdown files under the `artifacts/first-run` directory.

### Documentation pointers
- Overview & nav: `docs/README.md`, `docs/project-organization.md`
- Maintenance operations: `docs/maintenance/branch-cleanup-runbook.md`
- Worktree maintenance operations: `docs/maintenance/worktree-cleanup-runbook.md`
- TODO triage operations: `docs/maintenance/todo-triage-runbook.md`
- Current architecture snapshot: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- Zero-based ideal redesign blueprint: `docs/architecture/ZERO-BASED-IDEAL-DESIGN.md`
- Product fit (what to input/output, which tools to use): `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- PR automation (Copilot -> auto-fix -> auto-merge): `docs/ci/pr-automation.md`
- Release engineering (release verify / post-deploy): `docs/operate/release-engineering.md`
- CI/quality gates: `docs/ci/phase2-ci-hardening-outline.md`, `docs/ci/label-gating.md`, `docs/ci/harness-taxonomy.md`
- Development deep dives: [Enhanced State Manager](docs/development/enhanced-state-manager.md), [Circuit Breaker](docs/development/circuit-breaker.md)
- Docs consistency lint: `pnpm run check:doc-consistency` (`docs/quality/doc-consistency-lint.md`)
- Heavy test observability: `docs/ci/heavy-test-trend-archive.md`, `docs/ci/heavy-test-alerts.md`, `docs/ci/heavy-test-album.md`
- Specification & verification: `docs/quality/`, `docs/quality/formal-csp.md`, `docs/ci-policy.md`, `docs/testing/integration-runtime-helpers.md`
- Context Pack v1 (spec contract): `docs/spec/context-pack.md`
- Context Pack onboarding checklist: `docs/guides/context-pack-onboarding-checklist.md`
- Context Pack Phase5+ cookbook: `docs/guides/context-pack-phase5-cookbook.md`
- Context Pack troubleshooting runbook: `docs/operations/context-pack-troubleshooting.md`
- Contract catalog (input/decision/evidence/operation): `docs/reference/CONTRACT-CATALOG.md`
- Spec & Verification Kit (minimal activation guide): `docs/reference/SPEC-VERIFICATION-KIT-MIN.md`
- Connectors & agent workflows: `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`, `docs/integrations/CODEX-INTEGRATION.md`

---

## Japanese

ae-framework は **エージェント協調型のSDLCオーケストレーター兼「仕様・検証キット」** です。指示・仕様・検証の流れを標準化し、エージェントと開発者が同じルールで再現性のある品質管理を行えるようにします。

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

### すぐ試す
```bash
# 前提: Node.js 20.11+ (<23), pnpm 10
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install
pnpm run first-run
pnpm run setup-hooks

pnpm run lint
pnpm run test:fast

# Mutation quick（mktemp利用、STRYKER_TEMP_DIR対応）
STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick
# レポート生成失敗を許容する場合のみ MUTATION_REPORT_STRICT=0 を付与

# ヘビーテスト結果のキャッシュ運用
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/sync-test-results.mjs --snapshot
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

> このリポジトリは `workspace:*` を使うため、`npm install` は `preinstall` ガードで意図的に失敗させています。`pnpm install` を使用してください。
> `pnpm run doctor:env` は `artifacts/doctor/env.json` を出力し、終了コードは `0`（正常）/`2`（警告）/`1`（要修正）/`3`（引数不正）です。
> `pnpm run first-run` は `doctor:env -> build -> verify:lite` を順に実行し、`artifacts/first-run` ディレクトリに summary の JSON/Markdown を出力します。

### ドキュメントへの入り口
- 全体概要: `docs/README.md`, `docs/project-organization.md`
- 現行アーキテクチャ全体像: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- ゼロベース再設計の理想像: `docs/architecture/ZERO-BASED-IDEAL-DESIGN.md`
- 適用対象/入力/出力/ツール適性: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- PR自動化（Copilot→auto-fix→auto-merge）: `docs/ci/pr-automation.md`
- リリース運用（release verify / post-deploy verify）: `docs/operate/release-engineering.md`
- CI/品質ゲート: `docs/ci/phase2-ci-hardening-outline.md`, `docs/ci/label-gating.md`, `docs/ci/harness-taxonomy.md`
- ドキュメント検証ポリシー: `docs/ci/docs-doctest-policy.md`
- 開発向け設計ドキュメント: [Enhanced State Manager](docs/development/enhanced-state-manager.md), [Circuit Breaker](docs/development/circuit-breaker.md)
- ドキュメント整合チェック: `pnpm run check:doc-consistency`（`docs/quality/doc-consistency-lint.md`）
- ヘビーテスト観測: `docs/ci/heavy-test-trend-archive.md`, `docs/ci/heavy-test-alerts.md`, `docs/ci/heavy-test-album.md`
- 仕様と検証: `docs/ci-policy.md`, `docs/testing/integration-runtime-helpers.md`, `docs/quality/`, `docs/quality/formal-csp.md`
- Context Pack v1（仕様入力契約）: `docs/spec/context-pack.md`
- Context Pack 導入チェックリスト: `docs/guides/context-pack-onboarding-checklist.md`
- Context Pack Phase5+ 実践ガイド: `docs/guides/context-pack-phase5-cookbook.md`
- Context Pack 障害対応ランブック: `docs/operations/context-pack-troubleshooting.md`
- 契約カタログ（input/decision/evidence/operation）: `docs/reference/CONTRACT-CATALOG.md`
- Spec & Verification Kit（最小パッケージ・有効化手順）: `docs/reference/SPEC-VERIFICATION-KIT-MIN.md`
- エージェント統合: `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`, `docs/integrations/CODEX-INTEGRATION.md`

---

## 🔒 TypeScript Policy / TypeScript ポリシー

### @ts-expect-error Usage Policy

When using `@ts-expect-error` comments, follow this structured format:

```typescript
// @ts-expect-error owner:@username expires:YYYY-MM-DD reason: detailed description
const _example: number = 'type mismatch for policy example';
```

**Required fields:**
- `owner:@username` - GitHub handle responsible for the suppression
- `expires:YYYY-MM-DD` - Date when this suppression should be reviewed/removed
- `reason: description` - Detailed explanation (minimum 12 characters)

**Examples:**
```typescript
// @ts-expect-error owner:@alice expires:2027-12-31 reason: narrowing todo for complex union
const result = complexUnion as string;

// @ts-expect-error owner:@bob expires:2027-06-15 reason: legacy API compatibility until v2 migration
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
