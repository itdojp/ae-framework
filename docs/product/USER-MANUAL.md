---
docRole: derived
canonicalSource:
- docs/reference/CLI-COMMANDS-REFERENCE.md
- package.json
lastVerified: '2026-03-22'
---
# ae-framework 利用マニュアル

> Language / 言語: English | 日本語

---

## English

## 1. Target Users
- product developers, QA engineers, and operators
- teams that run specification validation and CI quality gates
- teams evaluating agent integrations
- teams that need to judge whether ae-framework fits their input/output/tool boundary

For the applicability overview, see `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`.

## 2. Preconditions
- Node.js: `>=20.11 <23` (`package.json` `engines.node`)
- pnpm: `10.0.0` (`package.json` `packageManager`)
- `npm install` is intentionally blocked by the `preinstall` guard; the repository assumes pnpm
- GitHub Actions is available for CI operation
- if you use `verify:lite` as-is, the current implementation assumes a JS/TS toolchain (`pnpm types:check`, `pnpm lint`, `pnpm run build`, plus `vitest` in CI)
- for non-JS/TS products, introduce `verify:formal` / `verify:conformance` first and define language-specific lint/test/build jobs separately
- Windows is supported through PowerShell, but WSL2 is the safer baseline when tool compatibility becomes an issue

## 3. Setup

### 3.1 Install dependencies
```bash no-doctest
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install
```

If `npm install` is executed, the guard prints the migration message and exits immediately with `exit 1`.

### 3.2 Recommended first command
```bash no-doctest
pnpm run first-run
```

This runs `doctor:env -> build -> verify:lite` in sequence and stores:
- machine-readable summary JSON under `artifacts/first-run`
- human-readable summary Markdown under `artifacts/first-run`
- per-step logs under `artifacts/first-run/logs`

Exit-code contract:
- `0`: all required steps succeeded
- `1`: at least one required step failed
- `3`: invalid arguments
- `4`: summary write failure

### 3.3 Run environment diagnostics separately
```bash no-doctest
pnpm run doctor:env
```

The diagnostic result is written to `artifacts/doctor/env.json`.

Exit-code contract:
- `0`: all required checks passed
- `2`: warning-level issues only
- `1`: operator action required
- `3`: invalid arguments

### 3.4 Install development hooks
```bash no-doctest
pnpm run setup-hooks
```

### 3.5 Minimal local verification
```bash no-doctest
pnpm run lint
pnpm run test:fast
```

### 3.6 Optional configuration file
The CLI loads YAML configuration through `src/cli/config/ConfigLoader.ts`.

Resolution order:
- `config/ae-framework.yml`
- `config/ae-framework.yaml`
- `ae-framework.yml`
- `ae-framework.yaml`
- `.ae-framework.yml`
- `.ae-framework.yaml`

If none exists, the CLI runs with defaults.

## 4. Core Workflows

### 4.1 Register and validate specifications
- recommended placement: `spec/`
- reference: `docs/spec/registry.md`

Example commands:
```bash no-doctest
# AE-Spec (Markdown) -> AE-IR (JSON)
pnpm run spec:validate -i spec/example-spec.md --output .ae/ae-ir.json

# AE-IR lint
pnpm run spec:lint -i .ae/ae-ir.json

# CI-oriented JSON reports
pnpm run ae-framework -- spec lint -i .ae/ae-ir.json --format json --output artifacts/spec/lint-report.json
pnpm run ae-framework -- spec validate -i spec/example-spec.md --output .ae/ae-ir.json --format json --report-output artifacts/spec/validate-report.json
```

### 4.2 Optional formal verification
Follow `docs/quality/formal-tools-setup.md` first.

```bash no-doctest
pnpm run verify:formal
```

If you use CSP with `cspx`, the current recommended path remains:
```bash no-doctest
cargo install --git https://github.com/itdojp/cspx --rev 8a67639ea4d3f715e27feb8cd728f46866a905db --locked cspx
cspx --version
cspx typecheck --help | grep -- --summary-json
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

Expected evidence:
- `artifacts/hermetic-reports/formal/csp-summary.json`
- `artifacts/hermetic-reports/formal/cspx-result.json`
- `csp-summary.json` records `backend`, `status`, `resultStatus`, and `exitCode`

### 4.3 Execute tests
```bash no-doctest
pnpm run test:fast
pnpm run test:unit
pnpm run test:int
```

Add `pnpm run pbt` or `pnpm run bdd` when needed. `pbt` resolves config in this order:
- `--config`
- `PBT_CONFIG`
- `tests/property/vitest.config.*`
- `tests/property`

If resolution fails, expect `PBT_CONFIG_NOT_FOUND` with exit code `2`. In environments where `pnpm` is missing, the runner exits with `127`.

### 4.4 CI operating baseline
- use `verify-lite` as the default PR gate
- the current `main` required-check baseline is:
  - `Verify Lite / verify-lite`
  - `Policy Gate / policy-gate`
  - `Copilot Review Gate / gate`
- optional repository-variable based automation exists for:
  - Copilot auto-fix
  - auto-merge
- add `ci-extended` or `formal-verify` only when the change profile requires it

Primary references:
- `docs/ci/branch-protection-operations.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/copilot-auto-fix.md`
- `docs/ci/auto-merge.md`
- `docs/ci/pr-automation.md`
- `docs/quality/formal-runbook.md`

## 5. CLI Basics
See `docs/product/COMMAND-MODES.md` for entrypoint policy.

The canonical main CLI entrypoint is `src/cli/index.ts`. The benchmark side uses `src/cli/benchmark-cli.ts` (`ae-benchmark`), while `src/cli.ts` remains only as a `benchmark-report/v1` compatibility shim.

### 5.1 Development-time CLI help
```bash no-doctest
pnpm run ae-framework -- --help
```

### 5.2 Built CLI
```bash no-doctest
pnpm run build
pnpm exec ae --help
pnpm exec ae-framework --help
```

### 5.3 Representative subcommands
```bash no-doctest
pnpm run ae-framework -- --help
pnpm run ae-framework -- spec --help
pnpm run ae-framework -- quality run --env development
pnpm run ae-framework -- quality run --env development --no-history
pnpm run ae-framework -- security --help
pnpm run ae-framework -- conformance --help
pnpm run ae-framework -- integration --help
pnpm run ae-framework -- resilience --help
pnpm run ae-framework -- sbom --help
```

### 5.4 Exit codes and JSON errors
- `0`: success
- `2`: invalid input or contract violation
- `1`: internal or unexpected failure

When `spec lint` / `spec validate` uses `--format json`, failure responses still stay JSON-shaped, but invalid-input and internal-error payloads follow the dedicated error shape emitted by `emitSpecCommandError` rather than `schema/spec-validation-report.schema.json`.

Representative command contracts in the current implementation:

| Command | success | input error | internal error | success JSON schema |
| --- | --- | --- | --- | --- |
| `ae spec lint --format json` | `0` | `2` (`SPEC_INVALID_INPUT`) | `1` (`SPEC_INTERNAL_ERROR`) | `schema/spec-validation-report.schema.json` |
| `ae spec validate --format json` | `0` | `2` (`SPEC_INVALID_INPUT`) | `1` (`SPEC_INTERNAL_ERROR`) | `schema/spec-validation-report.schema.json` |
| `ae quality run --format json` | `0` | `2` (`--format` invalid) | `1` (blocker failure / execution error) | `schema/quality-report.schema.json` |
| `ae quality reconcile --format json` | `0` | `2` (`--format` invalid) | `1` (remaining blocker / execution error) | `schema/quality-report.schema.json` |
| `pnpm run verify:profile -- --json --profile <name>` | `0` | `2` (unknown profile) / `3` (missing `--profile`, or missing values for `--profile` / `--out`) | `1` (summary write failure and similar) | `schema/verify-profile-summary.schema.json` |

Notes:
- `ae quality run --format json` and `ae quality reconcile --format json` emit `QualityReport` to stdout when `text` is not requested.
- `ae spec lint` / `ae spec validate` emit dedicated error payloads through `emitSpecCommandError` on input/internal failures rather than the success schema above.
- `pnpm run verify:profile` prints text on input errors; success JSON is emitted only when the command runs with a valid profile and reaches the summary path.
- For artifact placement and root pollution checks, see `docs/quality/ARTIFACTS-CONTRACT.md` and `scripts/ci/check-no-root-generated-files.mjs`.

## 6. Agent Integrations
- Codex: `docs/integrations/CODEX-INTEGRATION.md`
- Claude Code: `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`
- playbook example: `pnpm run codex:run`

## 7. Representative Operational Commands
```bash no-doctest
# formal summary
pnpm run formal:summary

# spec tool checks
pnpm run spec:validate

# minimum CI-facing verification
pnpm run verify:lite

# unified fast/full profile with JSON summary
pnpm run verify:profile -- --profile fast --json --out artifacts/verify-profile-summary.json

# issue-driven traceability
pnpm run ae-framework -- traceability extract-ids --issue "https://github.com/<org>/<repo>/issues/1" --pattern "(?:LG|REQ)-[A-Z0-9_-]+" --output docs/specs/issue-traceability-map.json
pnpm run ae-framework -- traceability matrix --map docs/specs/issue-traceability-map.json --tests "tests/**/*" --code "src/**/*" --context-pack "spec/context-pack/**/*.{yml,yaml,json}" --format json --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json
pnpm run ae-framework -- validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# usefulness evaluation report
pnpm run evaluate:usefulness -- --strict-inputs --min-score 70 \
  --traceability docs/specs/ISSUE-TRACEABILITY-MATRIX.json \
  --verify-profile artifacts/verify-profile-summary.json \
  --quality-report reports/quality-gates/quality-report-ci-latest.json \
  --run-manifest-check artifacts/run-manifest-check.json

# dependency audit
pnpm run security:integrated:quick
```

Notes:
- full smoke stays on `pnpm run verify:formal`
- use `pnpm run tools:formal:check` to inspect formal tool installation
- CSP-specific procedures are in `docs/quality/formal-csp.md`
- issue-driven traceability is documented in `docs/quality/issue-requirements-traceability.md`
- usefulness evaluation inputs and scoring rules are in `docs/quality/usefulness-evaluation.md`
- strict usefulness evaluation expects all required inputs to exist; override paths explicitly when you are reusing artifacts from a different workflow sequence

## 8. Troubleshooting

### 8.1 verify-lite gate failure
- if `Verify Lite / verify-lite` is required, inspect the `verify-lite` logs and summary first
- if `Copilot Review Gate / gate` is required, confirm that Copilot review exists and every Copilot-involved conversation is resolved
- see `docs/ci/ci-troubleshooting-guide.md`
- for the gate-specific policy, see `docs/ci/copilot-review-gate.md`

### 8.2 Node.js version mismatch
- check `node -v`
- keep the runtime inside `>=20.11 <23`

### 8.3 Missing formal verification tools
- follow `docs/quality/formal-tools-setup.md`

## 9. References
- overview: `docs/product/OVERVIEW.md`
- detailed description: `docs/product/DETAIL.md`
- applicability and input/output/tool fit: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- command modes: `docs/product/COMMAND-MODES.md`
- current implementation architecture: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- top-level navigation: `docs/README.md`

---

## 日本語

## 1. 対象読者
- プロダクト開発者、QA、運用担当
- 仕様検証やCI品質ゲートを運用するチーム
- エージェント統合を検討しているチーム
- 導入対象の見極め（入力/出力/ツール適性）を行いたいチーム

適用判断の全体像は `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md` を参照してください。

## 2. 前提条件（根拠）
- Node.js: `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm: `10.0.0`（`package.json` の `packageManager`）
- `npm install` は `preinstall` ガードで失敗させる仕様（pnpm workspace 前提）
- GitHub Actions 利用可能なリポジトリ
- `verify:lite` をそのまま利用する場合は JS/TS ツールチェーン前提（`pnpm types:check`, `pnpm lint`, `pnpm run build`。CI の Verify Lite ワークフローではこれに加えて `vitest` が実行されます）
- 非JS/TSプロダクトは `verify:formal` / `verify:conformance` を先行導入し、lint/test/build は対象言語向けジョブを別途定義
- Windows は PowerShell でも実行可能ですが、ツール互換性で問題が出る場合は WSL2 を推奨

## 3. セットアップ

### 3.1 依存関係の導入
```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install
```

`npm install` を実行した場合は、pnpm へ移行するためのエラーメッセージを表示して即時終了します（exit 1）。

### 3.2 初回1コマンド（推奨）
```bash
pnpm run first-run
```

`doctor:env -> build -> verify:lite` を順に実行し、実行結果を以下に保存します。
- artifacts/first-run 配下の summary JSON（機械可読）
- artifacts/first-run 配下の summary Markdown（人間向け）
- artifacts/first-run/logs 配下のログ（各ステップ）

終了コード契約:
- `0`: すべてのステップが成功
- `1`: いずれかの必須ステップが失敗
- `3`: 引数不正
- `4`: サマリ書き込み失敗

### 3.3 環境診断（個別実行）
```bash
pnpm run doctor:env
```

診断結果は `artifacts/doctor/env.json` に保存されます。終了コード契約:
- `0`: 必須チェックすべてOK
- `2`: 警告あり（例: `dist/` 未生成、corepack未検出）
- `1`: 要修正（例: Node.js範囲外、pnpm未導入）
- `3`: 引数不正（例: 未定義オプション）

### 3.4 開発フックの導入
```bash
pnpm run setup-hooks
```

### 3.5 最小検証
```bash
pnpm run lint
pnpm run test:fast
```

### 3.6 設定ファイル（任意）
CLIは YAML 設定を探索して読み込みます（`src/cli/config/ConfigLoader.ts`）。

探索順（上から優先）:
- `config/ae-framework.yml`
- `config/ae-framework.yaml`
- `ae-framework.yml`
- `ae-framework.yaml`
- `.ae-framework.yml`
- `.ae-framework.yaml`

設定ファイルが存在しない場合は、デフォルト設定で動作します。

## 4. 基本ワークフロー

### 4.1 仕様の登録と検証
- 仕様の配置: `spec/`（詳細は `docs/spec/registry.md`）
- 検証コマンド（例: `spec/example-spec.md`）:
```bash
# AE-Spec (Markdown) -> AE-IR (JSON)
pnpm run spec:validate -i spec/example-spec.md --output .ae/ae-ir.json

# AE-IR lint
pnpm run spec:lint -i .ae/ae-ir.json

# CI向け JSON レポート（schema/spec-validation-report.schema.json 準拠）
pnpm run ae-framework -- spec lint -i .ae/ae-ir.json --format json --output artifacts/spec/lint-report.json
pnpm run ae-framework -- spec validate -i spec/example-spec.md --output .ae/ae-ir.json --format json --report-output artifacts/spec/validate-report.json
```

### 4.2 形式検証（任意）
前提: `docs/quality/formal-tools-setup.md` に従いツールを準備します。

```bash
pnpm run verify:formal
```

#### CSP(cspx) を利用する場合（推奨）
`verify:csp` は `cspx` を優先バックエンドとして利用できます。

```bash
# 再現性のため commit pin で導入
cargo install --git https://github.com/itdojp/cspx --rev 8a67639ea4d3f715e27feb8cd728f46866a905db --locked cspx

# 機能確認（summary-json 対応）
cspx --version
cspx typecheck --help | grep -- --summary-json

# smoke 実行
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

確認ポイント:
- `artifacts/hermetic-reports/formal/csp-summary.json` が生成される
- `artifacts/hermetic-reports/formal/cspx-result.json` が生成される
- `csp-summary.json` の `backend/status/resultStatus/exitCode` が記録される

### 4.3 テスト実行
```bash
pnpm run test:fast
pnpm run test:unit
pnpm run test:int
```

必要に応じて、`pnpm run pbt` や `pnpm run bdd` を追加します。`pbt` は `--config`（最優先）→ `PBT_CONFIG` 環境変数 → `tests/property/vitest.config.*` → `tests/property` ディレクトリの順で解決します。解決不能時は `PBT_CONFIG_NOT_FOUND`（exit 2）、`pnpm` 非導入環境では exit 127 になります。

### 4.4 CI運用の基本
- PR作成時に verify-lite を基本ゲートとします
- Branch protection の Required checks では、`Verify Lite / verify-lite`、`Policy Gate / policy-gate`、`Copilot Review Gate / gate` を必須化する運用が current-state の main baseline です（詳細: `docs/ci/branch-protection-operations.md`, `docs/ci/copilot-review-gate.md`）
- （任意）Copilot suggestion の自動適用（auto-fix）を有効化できます（プロジェクト単位のRepository Variables）。詳細: `docs/ci/copilot-auto-fix.md`
- （任意）auto-merge を自動有効化し、人手マージを省略する運用にできます（プロジェクト単位のRepository Variables）。詳細: `docs/ci/auto-merge.md`
- PR 自動化（Copilot→auto-fix→auto-merge）の運用全体像: `docs/ci/pr-automation.md`
- 必要に応じて `ci-extended` や `formal-verify` を追加実行します
- 詳細: `docs/ci/branch-protection-operations.md`, `docs/quality/formal-runbook.md`

## 5. CLI利用の基本
実行モードの使い分けは `docs/product/COMMAND-MODES.md` を参照してください。

メインCLIの canonical entrypoint は `src/cli/index.ts` です。<br>
ベンチマークは `src/cli/benchmark-cli.ts`（`ae-benchmark`）を利用し、`src/cli.ts` は `benchmark-report/v1` 互換用の legacy shim としてのみ残しています。

### 5.1 開発時のCLI確認
```bash
pnpm run ae-framework -- --help
```

### 5.2 ビルド後のCLI
ビルド後に `ae` または `ae-framework` を利用します（`package.json bin` が `dist/src/cli/*` を指します）。
```bash
pnpm run build
pnpm exec ae --help
# または
pnpm exec ae-framework --help
```

CLIの詳細は `docs/reference/CLI-COMMANDS-REFERENCE.md` を参照してください。

### 5.3 代表的なCLIサブコマンド（開発時）
開発時（TypeScript実行）は `pnpm run ae-framework -- <command>` を使用します。

```bash
pnpm run ae-framework -- --help
pnpm run ae-framework -- spec --help
pnpm run ae-framework -- quality run --env development
pnpm run ae-framework -- quality run --env development --no-history
pnpm run ae-framework -- security --help
pnpm run ae-framework -- conformance --help
pnpm run ae-framework -- integration --help
pnpm run ae-framework -- resilience --help
pnpm run ae-framework -- sbom --help
```

### 5.4 CLI契約（exit code / JSONエラー）
- `0`: 正常終了
- `2`: 不正入力・契約違反（例: 不正サブコマンド、必須引数不足）
- `1`: 内部エラー・想定外の失敗

`spec lint` / `spec validate` で `--format json` を指定した場合、失敗時も JSON を返します。  
例（失敗時）:

```json
{
  "error": true,
  "code": "SPEC_INVALID_INPUT",
  "message": "ENOENT: no such file or directory, open 'spec/does-not-exist.json'",
  "details": {
    "input": "spec/does-not-exist.json"
  },
  "ts": "2026-02-18T00:00:00.000Z",
  "command": "lint"
}
```

主要コマンドの契約（現行実装）:

| コマンド | success | input error | internal error | success JSON schema |
| --- | --- | --- | --- | --- |
| `ae spec lint --format json` | `0` | `2` (`SPEC_INVALID_INPUT`) | `1` (`SPEC_INTERNAL_ERROR`) | `schema/spec-validation-report.schema.json` |
| `ae spec validate --format json` | `0` | `2` (`SPEC_INVALID_INPUT`) | `1` (`SPEC_INTERNAL_ERROR`) | `schema/spec-validation-report.schema.json` |
| `ae quality run --format json` | `0` | `2` (`--format` 不正値) | `1`（blocker失敗/実行エラー） | `schema/quality-report.schema.json` |
| `ae quality reconcile --format json` | `0` | `2` (`--format` 不正値) | `1`（blocker残存/実行エラー） | `schema/quality-report.schema.json` |
| `pnpm run verify:profile -- --json --profile <name>` | `0` | `2` (`unknown profile`) / `3`（`--profile` 未指定、または `--profile` / `--out` の値欠落） | `1`（summary write failure 等） | `schema/verify-profile-summary.schema.json` |

補足:
- `ae quality run --format json` / `ae quality reconcile --format json` は、標準出力に `QualityReport` を出力します（デフォルト `text`）。
- `ae spec lint` / `ae spec validate` の入力不正・内部エラー時は、成功スキーマではなく `emitSpecCommandError` の専用 error payload を返します。
- `pnpm run verify:profile` は入力エラー時に text を出力し、成功 JSON は有効な profile で summary 生成まで到達した場合にのみ出力されます。
- 成果物配置の契約（`artifacts/**`）と root 汚染検知は `docs/quality/ARTIFACTS-CONTRACT.md` と `scripts/ci/check-no-root-generated-files.mjs` を参照してください。

## 6. エージェント統合
- CodeX 連携: `docs/integrations/CODEX-INTEGRATION.md`
- Claude Code 連携: `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`
- Playbook 実行例: `pnpm run codex:run`

## 7. 代表的な運用コマンド

```bash
# 形式検証サマリ
pnpm run formal:summary

# 仕様ツールのチェック
pnpm run spec:validate

# CI向け最小検証
pnpm run verify:lite

# fast/full を統一実行（JSONサマリ出力）
pnpm run verify:profile -- --profile fast --json --out artifacts/verify-profile-summary.json

# Issue要件ID起点のトレーサビリティ（抽出 -> matrix -> strict validate）
pnpm run ae-framework -- traceability extract-ids --issue "https://github.com/<org>/<repo>/issues/1" --pattern "(?:LG|REQ)-[A-Z0-9_-]+" --output docs/specs/issue-traceability-map.json
pnpm run ae-framework -- traceability matrix --map docs/specs/issue-traceability-map.json --tests "tests/**/*" --code "src/**/*" --context-pack "spec/context-pack/**/*.{yml,yaml,json}" --format json --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json
pnpm run ae-framework -- validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# 有用性評価レポート（JSON + Markdown）
pnpm run evaluate:usefulness -- --strict-inputs --min-score 70 \
  --traceability docs/specs/ISSUE-TRACEABILITY-MATRIX.json \
  --verify-profile artifacts/verify-profile-summary.json \
  --quality-report reports/quality-gates/quality-report-ci-latest.json \
  --run-manifest-check artifacts/run-manifest-check.json

# 依存監査
pnpm run security:integrated:quick
```

補足:
- Full smoke は `pnpm run verify:formal`
- Formal ツールの導入状況確認は `pnpm run tools:formal:check`
- CSP 詳細手順は `docs/quality/formal-csp.md`
- Issue要件IDトレーサビリティ手順は `docs/quality/issue-requirements-traceability.md`
- 有用性評価の入力契約・スコア算出規約は `docs/quality/usefulness-evaluation.md`
- strict usefulness evaluation では必要入力がすべて揃っていることが前提であり、別フローの成果物を使う場合は path override を明示してください

## 8. トラブルシューティング

### 8.1 verify-lite ゲートの失敗
- `Verify Lite / verify-lite` が Required の場合、まず `verify-lite` のログ/サマリを確認
- `Copilot Review Gate / gate` が Required の場合、Copilotのレビューが存在し、**Copilotが関与したスレッドがすべて解決済み**かを確認（PR画面で「Resolve conversation」）
- `docs/ci/ci-troubleshooting-guide.md` を参照
  - Copilot Review Gate の詳細: `docs/ci/copilot-review-gate.md`

### 8.2 Node バージョン不一致
- `node -v` を確認し、`>=20.11 <23` の範囲に調整

### 8.3 形式検証ツール不足
- `docs/quality/formal-tools-setup.md` を参照して導入

## 9. 参考資料
- 概要説明資料: `docs/product/OVERVIEW.md`
- 詳細説明資料: `docs/product/DETAIL.md`
- 適用対象・入力/出力・ツール適性: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- コマンド体系（実行モード別）: `docs/product/COMMAND-MODES.md`
- 実装準拠の全体構成: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- 全体ナビゲーション: `docs/README.md`
