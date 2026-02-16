# AE Framework CLI Commands Reference

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Command-line reference for the current ae-framework implementation.**

### Overview
- CLI binaries: `ae` and `ae-framework` (same entry).
- Dev (TypeScript) execution in this repo: `pnpm run ae-framework -- <command>`
- Installed usage: `pnpm exec ae <command>` or `npx ae-framework <command>`

### Output and Exit Code Contract (Baseline)
- Standard result text is printed to `stdout`.
- Diagnostics and failure reasons are printed in command output with non-zero exit code.
- Exit code policy used by stdio/automation commands:
  - `0`: completed successfully (`ok:true`).
  - `1`: internal/runtime failure (`ok:false`).
  - `2`: invalid input or unsupported action.
- `pnpm run ae-framework -- <command>` is supported; a leading standalone `--` is normalized by the CLI entrypoint.

### Basic Syntax
```bash
ae <command> [options]
```

### Configuration Discovery
The CLI auto-loads config from the project root (first match):
- `config/ae-framework.yml`
- `config/ae-framework.yaml`

If none exist, defaults are used.

---

## Core Workflow Commands

### Phase Controls
```bash
# Validate current phase (or specify)
ae check
ae check --phase 1-intent

# Run guards
ae guard
ae guard --name "TDD Guard"

# Next phase with prerequisite validation
ae next

# Validate TDD cycle guards
ae tdd
```

### Intent & Tests-First
```bash
# Intent analysis
 ae intent --analyze --sources "requirements.md"

# Intent completeness check
 ae intent --validate --sources "requirements.md"

# Tests-first prompt generation (recommended after intent)
 ae tests:suggest --template http-api --intent "Build a minimal todo API"
 ae tests:suggest --template auth --input requirements.md --output tests-first.md
# auth template placeholders ({intent},{auth_type},{roles},{resources}) are auto-resolved.
# Supported input hints: intent:, auth_type:, roles:, resources:
# - When structured hints are present, missing fields remain "unspecified".
# - For free-form text, {intent} uses the first non-empty line and other fields are inferred when possible.

# Generate acceptance/contract/property/regression test skeletons from spec AC
 ae tests:scaffold --input docs/templates/plan-to-spec-normalization-sample.md
 ae tests:scaffold --input spec/example-spec.md --spec-id order-checkout --out tests/generated/spec-kit/order-checkout
 ae tests:scaffold --input spec/example-spec.md --no-regression

# Issue requirements traceability (LG-*/REQ-* driven)
 ae traceability extract-ids \
   --issue "https://github.com/<org>/<repo>/issues/1" \
   --pattern "(?:LG|REQ)-[A-Z0-9_-]+" \
   --output docs/specs/issue-traceability-map.json

 ae traceability matrix \
   --map docs/specs/issue-traceability-map.json \
   --tests "tests/**/*" \
   --code "src/**/*" \
   --format json \
   --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# strict mode: fail on missing links (matrix input recommended)
 ae validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json
```

### Natural Language Requirements
```bash
# Analyze requirements
 ae natural-language --analyze --sources "requirements.md"

# Extract entities
 ae natural-language --extract-entities --sources "domain.md"

# Validate completeness
 ae natural-language --validate-completeness --sources "requirements.md"
```

### User Stories
```bash
# Generate stories
 ae user-stories --generate --sources "requirements.md"

# Validate stories
 ae user-stories --validate --sources "user-stories.md"

# Prioritize / estimate
 ae user-stories --prioritize --sources "backlog.md"
 ae user-stories --estimate --sources "backlog.md"
```

### Validation
```bash
# Validate requirements/stories/specs
 ae validate --requirements --sources "requirements.md"
 ae validate --stories --sources "user-stories.md"
 ae validate --specifications --sources "spec/"

# Traceability / completeness
 ae validate --traceability --sources "project/"
 ae validate --completeness --sources "artifacts/"
```

### Domain Modeling (Phase 5)
```bash
ae domain-model --analyze --sources "requirements.md,user-stories.md"
ae domain-model --entities --sources "domain-requirements.md"
ae domain-model --aggregates --sources "entities.md"
ae domain-model --contexts --sources "domain-analysis.md"
ae domain-model --rules --sources "business-rules.md"
ae domain-model --language --sources "glossary.md"
```

### UI Scaffold (Phase 6)
```bash
# Generate components from .ae/phase-state.json
 ae ui-scaffold --components
 ae ui-scaffold --state
 ae ui-scaffold --tokens
 ae ui-scaffold --a11y

# UI alias (ae-ui = ae-framework ui-scaffold; subcommand required)
 ae-ui scaffold --components
```

---

## Tooling & System Commands

### Spec (AE-Spec)
```bash
# Compile AE-Spec markdown to AE-IR JSON
 ae spec compile -i spec/example.md -o .ae/ae-ir.json

# Lint AE-IR
 ae spec lint -i .ae/ae-ir.json
 ae spec lint -i .ae/ae-ir.json --format json --output artifacts/spec/lint-report.json

# Validate (compile + lint)
 ae spec validate -i spec/example.md --output .ae/ae-ir.json
 ae spec validate -i spec/example.md --output .ae/ae-ir.json --format json --report-output artifacts/spec/validate-report.json
 # JSON schema: schema/spec-validation-report.schema.json

# Export AE-IR (default: kiro)
 ae spec export -i .ae/ae-ir.json -f kiro -o .kiro/specs
```

### Fix (CEGIS Auto-Fix)
```bash
# Apply fixes from failure artifacts
 ae fix apply --input failures.json --output .ae/auto-fix --dry-run
 ae fix apply --input failures.json --apply --verify --verify-profile lite

# Analyze failures
 ae fix analyze --input failures.json --output-format markdown

# Create a failure artifact
 ae fix create-artifact --type error --message "Null pointer" --file src/app.ts --line 10 --output failure.json

# Status / strategies
 ae fix status
 ae fix strategies --category test_failure
```

### Runtime Conformance (Phase 2.2)
```bash
# Generate samples
 ae conformance sample --rules configs/samples/sample-rules.json \
   --config configs/samples/sample-config.json \
   --data configs/samples/sample-data.json \
   --context configs/samples/sample-context.json

# Verify input data
 ae conformance verify --input data.json --rules rules.json \
   --context-file context.json --format json --output conformance-results.json

# Rules / config / metrics / status
 ae conformance rules --list
 ae conformance config --show
 ae conformance metrics --format json --export metrics.json
 ae conformance status

# Aggregate reports
 ae conformance report --directory artifacts/hermetic-reports/conformance --format both
```

### Integration Testing (Phase 2.3)
```bash
# Generate samples
 ae integration generate --type environment --name test --output test-env.json
 ae integration generate --type test --test-type e2e --name "Login" --output login-test.json
 ae integration generate --type suite --name "Auth Suite" --output auth-suite.json

# Discover tests
 ae integration discover --patterns "./tests/**/*.json" --type all --output discovery.json

# Run tests/suites
 ae integration run --tests login-test.json --environment test
 ae integration run --suites auth-suite.json --parallel --max-concurrency 4 --output-dir ./test-results

# Status / reports
 ae integration status --watch --refresh 5
 ae integration reports --list
```

### Quality Gates
```bash
# Run quality gates
 ae quality run --env development
 ae quality run --env development --no-history

# Reconcile (run + auto-fix rounds)
 ae quality reconcile --env development --max-rounds 3 --fix-input .ae/failures.json

# List / policy / validate / report
 ae quality list --env development --format summary
 ae quality policy --env development
 ae quality validate
 ae quality report --env development --format json
 ae quality init --force
```

### Entry Runner (Unified)
```bash
# Run consolidated runners
 ae entry test --profile ci-lite
 ae entry quality --list
 ae entry verify --dry-run --profile lite
 ae entry test --profile ci --root /path/to/repo
```

### Verify Profile Runner
```bash
# fast/full プロファイルを実行
 pnpm run verify:profile -- --profile fast
 pnpm run verify:profile -- --profile full

# CI向け JSON サマリ（step別 name/command/status/exit_code/duration_ms/required）
 pnpm run verify:profile -- --profile fast --json --out artifacts/verify-profile-summary.json
# required step が失敗すると overall_status=fail / exit code!=0。
# optional step の失敗は optional_fail_count に集計され、required が通れば exit code 0。
```

### Property-Based Test Runner
```bash
# Default resilient entrypoint (config auto-discovery + fallback)
 pnpm run pbt

# Use explicit config
 pnpm run pbt -- --config tests/property/vitest.config.ts

# Use environment override (lower priority than --config)
 PBT_CONFIG=tests/property/vitest.config.ts pnpm run pbt

# Pass-through vitest args
 pnpm run pbt -- tests/property/email.brand.is.pbt.test.ts --reporter=dot

# Resolution order:
# - --config/-c
# - PBT_CONFIG environment variable
# - tests/property/vitest.config.{ts,mts,js,mjs,cjs}
# - tests/property directory
#
# Error contract:
# - exit 2: PBT_CONFIG_NOT_FOUND (config/tests directory could not be resolved)
# - exit 1: test failure
# - exit 127: runner (pnpm) not found
```

### Setup
```bash
ae setup list
 ae setup suggest
 ae setup wizard
 ae setup typescript-node --name my-app --package-manager pnpm
```

### Security / SBOM / Resilience / Circuit Breaker
```bash
# Security
 ae security show-config --env development
 ae security check-headers --url http://localhost:3000/health

# SBOM
 ae sbom generate --format json --output sbom.json
 ae sbom validate sbom.json
 ae sbom compare base.json head.json

# Resilience
 ae resilience create --name default
 ae resilience health --name default
 ae resilience test --name default --operations 20 --failure-rate 0.2

# Circuit breaker
 ae circuit-breaker create --name demo
 ae circuit-breaker list
 ae circuit-breaker stats --name demo
 ae circuit-breaker health
```

### Other Utilities
```bash
# Enhanced state
 ae enhanced-state save
 ae enhanced-state load

# Progress
 ae status
 ae board

# Agent completion (LLM)
 ae agent:complete --prompt "Summarize failures" --record

# CI scaffold
 ae ci scaffold --force

# Doctor
 ae doctor env

# Adapt
 ae adapt jest --coverage-lines 85
 ae adapt vitest --coverage-lines 85
```

### Benchmark (Req2Run)
```bash
# Benchmark CLI is separate
 ae-benchmark list --enabled-only
 ae-benchmark run --ci --dry-run
 ae-benchmark init --output configs/benchmark-config.json
```

> For full options: run `ae <command> --help`.

---

## 日本語

**現行実装に基づく ae-framework CLI リファレンス**

### 概要
- CLI バイナリは `ae` / `ae-framework`（同一エントリ）
- リポジトリ開発時: `pnpm run ae-framework -- <command>`
- インストール後: `pnpm exec ae <command>` / `npx ae-framework <command>`

### 出力/終了コード契約（ベースライン）
- 通常の実行結果は `stdout` に出力します。
- 異常時は診断メッセージを出力し、非0終了コードを返します。
- stdio/自動化コマンドの終了コード方針:
  - `0`: 正常終了（`ok:true`）。
  - `1`: 実行時エラー（`ok:false`）。
  - `2`: 入力不備または未対応アクション。
- `pnpm run ae-framework -- <command>` 形式の先頭 `--` は CLI 側で正規化され、サブオプションを解釈します。

### 基本構文
```bash
ae <command> [options]
```

### 設定ファイルの探索
CLI は以下を順に探索し、自動で読み込みます。
- `config/ae-framework.yml`
- `config/ae-framework.yaml`

存在しない場合はデフォルト設定を使用します。

---

## 主要コマンド（抜粋）

### フェーズ管理
```bash
ae check
 ae check --phase 1-intent
 ae guard --name "TDD Guard"
 ae next
 ae tdd
```

### Intent / Tests-First
```bash
ae intent --analyze --sources "requirements.md"
 ae intent --validate --sources "requirements.md"
 ae tests:suggest --template http-api --intent "Build a minimal todo API"
 # auth テンプレートの {intent}/{auth_type}/{roles}/{resources} は入力から自動展開されます
 ae traceability extract-ids --issue "https://github.com/<org>/<repo>/issues/1" --pattern "(?:LG|REQ)-[A-Z0-9_-]+" --output docs/specs/issue-traceability-map.json
 ae traceability matrix --map docs/specs/issue-traceability-map.json --tests "tests/**/*" --code "src/**/*" --format md --output docs/specs/ISSUE-TRACEABILITY-MATRIX.md
 ae tests:scaffold --input docs/templates/plan-to-spec-normalization-sample.md
 ae tests:scaffold --input docs/templates/plan-to-spec-normalization-sample.md --no-contract
```

### Phase 2–6 コア
```bash
# Natural Language
ae natural-language --analyze --sources "requirements.md"
 ae natural-language --extract-entities --sources "domain.md"
 ae natural-language --validate-completeness --sources "requirements.md"

# User Stories
ae user-stories --generate --sources "requirements.md"
 ae user-stories --validate --sources "user-stories.md"
 ae user-stories --prioritize --sources "backlog.md"
 ae user-stories --estimate --sources "backlog.md"

# Validation
ae validate --requirements --sources "requirements.md"
 ae validate --stories --sources "user-stories.md"
 ae validate --specifications --sources "spec/"
 ae validate --traceability --sources "project/"
 ae validate --traceability --strict --sources "docs/specs/ISSUE-TRACEABILITY-MATRIX.json"
 ae validate --completeness --sources "artifacts/"

# Domain Model
ae domain-model --analyze --sources "requirements.md,user-stories.md"
 ae domain-model --entities --sources "domain-requirements.md"
 ae domain-model --aggregates --sources "entities.md"
 ae domain-model --contexts --sources "domain-analysis.md"
 ae domain-model --rules --sources "business-rules.md"
 ae domain-model --language --sources "glossary.md"

# UI Scaffold
ae ui-scaffold --components
 ae ui-scaffold --state
 ae ui-scaffold --tokens
 ae ui-scaffold --a11y
 ae-ui scaffold --components
```

---

## Phase 2.1–2.3（実装済みコマンド）

### CEGIS Auto-Fix
```bash
ae fix apply --input failures.json --output .ae/auto-fix --dry-run
 ae fix analyze --input failures.json --output-format markdown
 ae fix create-artifact --type error --message "Null pointer" --file src/app.ts --line 10 --output failure.json
 ae fix status
 ae fix strategies --category test_failure
```

### Runtime Conformance
```bash
ae conformance sample --rules configs/samples/sample-rules.json \
  --config configs/samples/sample-config.json \
  --data configs/samples/sample-data.json \
  --context configs/samples/sample-context.json

 ae conformance verify --input data.json --rules rules.json \
  --context-file context.json --format json --output conformance-results.json

 ae conformance rules --list
 ae conformance config --show
 ae conformance metrics --format json --export metrics.json
 ae conformance status
 ae conformance report --directory artifacts/hermetic-reports/conformance --format both
```

### Integration Testing
```bash
ae integration generate --type environment --name test --output test-env.json
 ae integration generate --type test --test-type e2e --name "Login" --output login-test.json
 ae integration generate --type suite --name "Auth Suite" --output auth-suite.json

 ae integration discover --patterns "./tests/**/*.json" --type all --output discovery.json
 ae integration run --tests login-test.json --environment test
 ae integration run --suites auth-suite.json --parallel --max-concurrency 4 --output-dir ./test-results

 ae integration status --watch --refresh 5
 ae integration reports --list
```

---

## その他の主要ツール

### Spec / Entry / Setup / Quality
```bash
# Spec
ae spec compile -i spec/example.md -o .ae/ae-ir.json
 ae spec lint -i .ae/ae-ir.json
 ae spec lint -i .ae/ae-ir.json --format json --output artifacts/spec/lint-report.json
 ae spec validate -i spec/example.md --output .ae/ae-ir.json
 ae spec validate -i spec/example.md --output .ae/ae-ir.json --format json --report-output artifacts/spec/validate-report.json
 ae spec export -i .ae/ae-ir.json -f kiro -o .kiro/specs

# Entry runner
ae entry test --profile ci-lite
 ae entry quality --list

# Setup
ae setup list
 ae setup suggest
 ae setup wizard

# Quality
ae quality run --env development
 ae quality run --env development --no-history
 ae quality reconcile --env development --max-rounds 3 --fix-input .ae/failures.json
 ae quality list --env development --format summary
 ae quality policy --env development
 ae quality validate
 ae quality report --env development --format json
 ae quality init --force
```

### Security / SBOM / Resilience / Circuit Breaker
```bash
# Security
ae security show-config --env development
 ae security check-headers --url http://localhost:3000/health

# SBOM
ae sbom generate --format json --output sbom.json
 ae sbom validate sbom.json
 ae sbom compare base.json head.json

# Resilience
ae resilience create --name default
 ae resilience health --name default
 ae resilience test --name default --operations 20 --failure-rate 0.2

# Circuit breaker
ae circuit-breaker create --name demo
 ae circuit-breaker list
 ae circuit-breaker stats --name demo
 ae circuit-breaker health
```

### ベンチマーク（Req2Run）
```bash
ae-benchmark list --enabled-only
 ae-benchmark run --ci --dry-run
 ae-benchmark init --output configs/benchmark-config.json
```

> 詳細は `ae <command> --help` を参照してください。
