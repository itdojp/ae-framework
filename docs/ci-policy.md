# CI Policy (Fast/Stable by Default) / CI ポリシー（デフォルトは高速・安定）

> 🌍 Language / 言語: English | 日本語

---

## English

This document defines CI policies to keep PR experience fast and stable while maintaining quality.

### Quickstart (local verification)
- `corepack enable && pnpm i && pnpm -s build && pnpm run test:fast`
  - Use this for pre‑PR sanity checks aligned with Verify Lite.
  - Node: use v20 (>=20.11, <23) as per `engines`
  - Optional (local security scan): `pnpm -s security:scan`
  - Optional (type check only): `pnpm -s types:check`
  - Optional (formal tools check): `pnpm -s tools:formal:check`
  - Optional (fast:plus suite): `pnpm -s test:fast:plus`
  - Optional (batch focus): `pnpm -s test:fast:batch:commands` (or `:cli` / `:property` / `:agents`)

### Verify Lite defaults
- PRs block only on Verify Lite (types:check / build). Lint runs in Verify Lite but is non‑blocking.
- Heavy jobs are opt‑in via labels and/or path conditions.
- Workflow: `.github/workflows/verify-lite.yml`

### actionlint & printf policy
- All workflows must pass `rhysd/actionlint` (use `rhysd/actionlint@v1.7.1`; see `.github/workflows/workflow-lint.yml`).
- Append to `$GITHUB_OUTPUT` / `$GITHUB_ENV` using `printf` with quoting; do not use `echo` for these files.
  - Example: `printf "name=%s\n" "$VALUE" >> "$GITHUB_OUTPUT"`
  - Example (env): `printf "%s=%s\n" "FOO" "$VALUE" >> "$GITHUB_ENV"`
  - Ensure a trailing newline; missing `\n` may break parsing
  - Multiline output:
    - `printf '%s<<EOF\n%s\nEOF\n' 'summary' "$MULTILINE" >> "$GITHUB_OUTPUT"`
  - Local actionlint run:
    - Docker: `docker run --rm -v "$PWD":/repo -w /repo ghcr.io/rhysd/actionlint:1.7.1`
    - Homebrew (macOS): `brew install actionlint`

### Goals
- Block only lightweight, deterministic checks on PRs
- Heavy/unstable checks run opt-in via labels or path conditions
- Comprehensive checks run on main and scheduled jobs

### Required Checks (PR blocking)
- Verify Lite (types:check / build) — note: lint within Verify Lite is non‑blocking
- Optionally enable validate-artifacts-ajv / coverage-check as required
  - Workflows: `.github/workflows/validate-artifacts-ajv.yml`, `.github/workflows/coverage-check.yml` (see also `docs/quality/coverage-required.md`)
  - Enforce via Branch protection: Settings → Branches → main → Require status checks (add Verify Lite and selected checks)
  - Repository variables: set under Settings → Variables → Repository variables (e.g., `COVERAGE_DEFAULT_THRESHOLD`, `COVERAGE_ENFORCE_MAIN`)

### Policy sources & precedence
- Threshold/DoD sources resolve in this order: policy > AE-IR > ae.config (hints only; warn on use). See also `SECURITY.md` and `docs/quality/coverage-policy.md`.
 - When multiple thresholds exist within the same source, merge via the strictest comparator (e.g., `>=95%` is stricter than `>=90%`).

Modes (report-only vs enforce)
- report-only: non-blocking; post PR comments/artifacts for visibility
- enforce: blocking when thresholds are violated; enable via `enforce-*` labels or Branch protection required checks

Examples (label combos)
- Non‑blocking exploratory run: add `ci-non-blocking` + selected `run-*` labels
- Security check (report-only): add `run-security` (optionally `ci-non-blocking`)
- Security enforcement on PR: add `run-security` + `enforce-security`

Label value patterns
- `coverage:<pct>` / `perf:<pct>` / `lh:<pct>` — integer 0–100 (no `%`)
- `trace:<id>` — free-form identifier (letters/digits/hyphen/underscore)
- `lang:ja` / `lang:en` — PR summary language selector

### Opt-in Labels
- `ci-non-blocking`: run selected jobs with continue-on-error (traceability, model-check, contracts, security, etc.)
- `run-security`: run heavy security jobs (Security Scanning, Dependency Audit, License Compliance, CodeQL)
- `enforce-security`: enforce security thresholds on PRs (blocking when limits exceeded). See `SECURITY.md`.
- `qa --light`: run QA in light mode (vitest -> `test:fast`); used in `ae-ci`
- `ae-benchmark run --ci --light --dry-run`: benchmark config validation only in PRs (fast & stable)
- `run-qa`: run `ae-ci` workflow’s `qa-bench` on PRs (default off)
- `run-spec`: enable spec fail-fast on PRs
- `run-drift`: enable codegen drift detection on PRs
- `run-hermetic`: enable Hermetic CI on PRs
- `run-quality`: enable quality matrix in parallel tests
- `run-flake`: enable flake-detection on PRs
 - `run-e2e`: enable E2E tests on PRs
 - `run-formal`: enable Formal Verify and aggregate report on PRs (report-only by default); see `docs/quality/formal-runbook.md`
 - `enforce-formal` / `enforce-contracts`: enforce gates for formal/contract checks (label-gated)
- `run-adapters`: report Adapter Thresholds (a11y/perf/Lighthouse) in PRs (report-only). See `.github/workflows/adapter-thresholds.yml` and `docs/quality/adapter-thresholds.md`.
- `run-cedar`: run Cedar policies quality gates (report-only). See `.github/workflows/cedar-quality-gates.yml` and `docs/quality/cedar-quality-gates.md`.
- `coverage:<pct>`: override coverage threshold for coverage-check (default 80). e.g., `coverage:75`
  - Use `/coverage <pct|clear>` to set/clear on a PR
 - `enforce-coverage`: enforce coverage threshold on PRs (blocking when below threshold). See `docs/quality/coverage-policy.md`.
  - Note: `<pct>` is an integer percent 0–100 (no `%`). Typical values 70–95.
 - `enforce-perf`: enforce performance score threshold (override via `perf:<pct>`, default `vars.PERF_DEFAULT_THRESHOLD` or 75). `<pct>` is 0–100 (no `%`).
 - `enforce-lh`: enforce Lighthouse performance threshold (override via `lh:<pct>`, default `vars.LH_DEFAULT_THRESHOLD` or 80). `<pct>` is 0–100 (no `%`).
- `lang:ja` / `lang:en`: select PR summary language (default `en`). See `docs/ci/summary-env.md`.
 - `pr-summary:detailed`: render a more detailed PR summary (vs. digest)

Workflows (selected)
- `.github/workflows/ae-ci.yml` (QA light)
- `.github/workflows/ci-fast.yml` (CI Fast batches)
- `.github/workflows/workflow-lint.yml` (actionlint)
- `.github/workflows/parallel-test-execution.yml` (quality row)
- `.github/workflows/flake-detect.yml` (flake detection)
- `.github/workflows/hermetic-ci.yml` (Hermetic CI)
- `.github/workflows/adapter-thresholds.yml` (Adapters report-only)
- `.github/workflows/cedar-quality-gates.yml` (Cedar policies quality gates)
- `.github/workflows/coverage-check.yml` (coverage gate/report)
- `.github/workflows/sbom-generation.yml` (Security/SBOM)
 - `.github/workflows/fail-fast-spec-validation.yml` (spec fail-fast)
 - `.github/workflows/formal-verify.yml` (Formal verification)
- `.github/workflows/formal-aggregate.yml` (Formal reports aggregate/comment)
- `.github/workflows/pr-summary-comment.yml` (PR summary upsert)
 - `.github/workflows/pr-verify.yml` (comprehensive PR verify)
 - `.github/workflows/auto-labels.yml` (auto-apply labels from PR title/body)


### PR comments (Coverage / Formal)
- Comments are upserted (one per header) with fixed headers to avoid duplicates:
  - Coverage: `<!-- AE-COVERAGE-SUMMARY -->`
  - Formal Aggregate: `<!-- AE-FORMAL-AGGREGATE -->`
- Coverage comment format:
  - Threshold (effective) → Derived → Policy / Policy source → Docs links
  - Threshold derivation order: label > repo variable > default
- Formal Aggregate comment:
  - Posted only when `run-formal` label is present (report‑only by default)
  - Includes Tools/Reproduce hints; respects `FORMAL_AGG_LINE_CLAMP`, `FORMAL_AGG_ERRORS_LIMIT`, `FORMAL_AGG_SNIPPET_MAX_LINES`
  - Header strings must match exactly; the upsert logic identifies comments by the fixed header line
  - Summary is also appended to `$GITHUB_STEP_SUMMARY` when available (see `pr-summary-comment.yml`)
 - See also: `docs/quality/pr-summary.md` (summary comment structure and templates)

#### Examples

Coverage summary (upserted with header)

```
<!-- AE-COVERAGE-SUMMARY -->
Coverage: Threshold (effective) 80%
Derived: label=coverage:80 > repo var=COVERAGE_DEFAULT_THRESHOLD=75 > default=70
Policy: report-only (see docs/quality/coverage-policy.md)
Links: docs/quality/coverage-policy.md
```

See also
- `docs/quality/coverage-policy.md` — detailed coverage threshold policy, enforcement toggles, and PR examples.

Formal Aggregate (posted only when `run-formal`)

```
<!-- AE-FORMAL-AGGREGATE -->
Present: Alloy/TLA/SMT summaries available
Summary: 3 tools ran, 0 errors
By-type present: Alloy=present, TLA=present, SMT=present, Apalache=skipped
Apalache ran/ok: skipped (label-gated)
Meta: Tools=installed, Reproduce=see docs/quality/formal-runbook.md
```

### Slash Commands (Instant Dispatch / Labels)
- コメントで以下を投稿すると、対象ワークフローの即時起動やラベル付与ができます（main取り込み後有効）。
  - Notes: Commands are idempotent; repeating them is safe (they upsert labels/dispatch).
  - Tip: Use `/blocking` to remove `ci-non-blocking` and restore normal blocking settings
  - Dispatch（workflow_dispatch 直起動）
    - `/verify-lite` … Verify Lite を実行
    - `/run-qa-dispatch` … ae-ci（QA light）を実行
    - `/run-security-dispatch` … sbom-generation（Security/SBOM）を実行
    - `/ci-fast-dispatch` … CI Fast を実行（バッチ系は対応ラベル付与時のみ稼働）
    - `/formal-verify-dispatch` … Formal Verify を実行（`run-formal` との併用推奨）
    - `/formal-aggregate-dispatch` … Formal Reports Aggregate を実行（`run-formal` 併用時に集約コメントを生成）
    - `/run-flake-dispatch` … flake-detect を実行
    - `/spec-validation-dispatch` … spec-validation を実行
    - `/run-cedar-dispatch` … cedar-quality-gates を実行
  - ラベル付与（Opt-in 実行/ポリシー切替）
    - `/run-qa` … `run-qa` を付与（ae-ci の QA 実行）
    - `/run-security` … `run-security` を付与（Security/SBOM 実行。PR要約も投稿）
    - `/run-cedar` … `run-cedar` を付与（Cedar policies の品質ゲートを非ブロッキングで実行）
    - `/run-adapters` … `run-adapters` を付与（Adapter Thresholds をレポート: report-only）
    - `/run-hermetic` … `run-hermetic` を付与（Hermetic CI 実行）
    - `/run-spec` … `run-spec` を付与（Fail-Fast Spec 実行）
    - `/run-drift` … `run-drift` を付与（Codegen Drift 検出）
    - `/non-blocking` … `ci-non-blocking` を付与（一部ジョブを continue-on-error）
    - `/blocking` … `ci-non-blocking` を除去（通常のブロッキング設定へ）
    - `/ready` … `do-not-merge` を除去（マージ待ちへ）
    - `/pr-digest` / `/pr-detailed` … PR要約モード切替
    - `/run-formal` / `/enforce-formal` / `/enforce-contracts` … フォーマル/契約の実行/エンフォース切替
    - `/coverage <pct|clear>` … `coverage:<pct>` を設定/クリア（しきい値上書き）
    - `/perf <pct|clear>` … `perf:<pct>` を設定/クリア（性能スコアのしきい値）
    - `/lh <pct|clear>` … `lh:<pct>` を設定/クリア（Lighthouse 性能スコアのしきい値）
    - `/enforce-typecov` … `enforce-typecov` を付与（型カバレッジ enforcement）
    - `/enforce-coverage` … `enforce-coverage` を付与（カバレッジ enforcement）
    - `/enforce-perf` … `enforce-perf` を付与（性能スコア enforcement）
    - `/enforce-lh` … `enforce-lh` を付与（Lighthouse 性能スコア enforcement）
  - 使い分け例（推奨）
    - 追加確認したいカテゴリのみラベル付与 → `/ci-fast-dispatch` で即時起動
    - Verify Lite のみを再実行 → `/verify-lite`
  - 備考: コマンドは冪等です。繰り返し実行しても安全（ラベル付与/ディスパッチをアップサート）


### Path Conditions
- Fire spec fail-fast only for changes under `spec/**`, `.ae/**`
- Trigger SBOM/Security only for dependency or major code changes
- Workflows: `.github/workflows/fail-fast-spec-validation.yml` (spec), `.github/workflows/sbom-generation.yml` (security)
 - Examples (security): changes to `**/package.json`, `pnpm-lock.yaml`, `security/**` may trigger security workflows
 - Configure in workflows via `on.pull_request.paths` and/or `if: contains(github.event.pull_request.labels.*.name, 'label')`
 - Override via labels when needed: e.g., add `run-spec` or `run-security` to force execution regardless of path filters
  - Consider `paths-ignore` to skip heavy jobs on docs-only changes (e.g., `docs/**`, `**/*.md`)
 
Examples (YAML)
```
# Path-gate spec validation
on:
  pull_request:
    paths:
      - 'spec/**'

# Label-gate security job
jobs:
  security:
    if: ${{ github.event_name != 'pull_request' || contains(github.event.pull_request.labels.*.name, 'run-security') }}
    steps:
      - run: echo 'run security steps...'
```

### test:fast (Fast CI suite)
- Purpose: verify resilience/core units and lightweight integration quickly; exclude heavy/env-dependent tests
- Current exclusions: `examples/**`, `**/__e2e__/**`, `tests/examples/**`, `tests/docker/**`, `tests/a11y/**`, `tests/property/**`, `tests/traceability/**`, `tests/security/**`, `tests/contracts/**`, `tests/integration/**`, `tests/resilience/integration.test.ts`, `tests/conformance/**`, `tests/cegis/**`, `tests/cli/**`, `tests/commands/**`, `tests/api/**`, `tests/tdd-setup.test.ts`
- Re‑enablement: green each category in small PRs and remove from exclusions; keep changes revertable.
  - First batch: reintroduced `tests/utils/**`
  - Second batch: reintroduced `tests/traceability/**` (skipped smoke test only)
  - Third batch: reintroduced `tests/utils/circuit-breaker*.test.ts`（実装を整合させ全緑化）
  - Fourth batch: reintroduced `tests/utils/phase-1-validation.test.ts`（初期化を明示し外部状態依存を解消）
  - Fifth batch: reintroduced `tests/contracts/**`（contract validation はCI安定範囲に調整済）

### QA CLI
- `ae qa --light`: runs a light QA pass (`vitest` `test:fast`); used by the `ae-ci` workflow.

### Security/Compliance
- Default: not required on PRs; label/path gated; run under `run-security`, aggregate results as artifacts
- PR summary comment (non-blocking) is posted when `run-security` is set (dependency vulnerabilities and top licenses)
- Enforce/gate gradually after team agreement (separate issue)
 - See `SECURITY.md` for thresholds/enforcement policy and PR comment example.

### Operations Notes
- In emergencies, use `ci-non-blocking` to avoid blocking PRs
- After merge, comprehensive CI on main (nightly/weekly) provides coverage
- Keep required checks centered on Verify Lite; others non-required by default
- For small PR batches, consider adding `ci-non-blocking` to reduce blocking during iteration
- Note: `ci-non-blocking` does not bypass required checks; those remain enforced by branch protection

### References
- Agent collaboration rules and CI label policies: `AGENTS.md`
- Slash command mappings: `.github/workflows/agent-commands.yml`
- CI label gating details: `docs/ci/label-gating.md`
 - CI labels cheatsheet: `docs/cheatsheets/ci-labels-cheatsheet.md`
 - Contributor quick refs (labels): `CONTRIBUTING.md` (labels table)
 - Type coverage policy: `docs/quality/type-coverage-policy.md`
 - Benchmarks: `docs/benchmark/README.md`
 - Formal tools setup: `docs/quality/formal-tools-setup.md`
 - Formal checks overview: `docs/verify/FORMAL-CHECKS.md`
 - Repository variables (quick ref):
   - `COVERAGE_DEFAULT_THRESHOLD`, `COVERAGE_ENFORCE_MAIN`
   - `PERF_DEFAULT_THRESHOLD`, `LH_DEFAULT_THRESHOLD`
 - PR summary env/toggles: `docs/ci/summary-env.md`
 - Adapters thresholds: `docs/quality/adapter-thresholds.md`
 - Cedar quality gates: `docs/quality/cedar-quality-gates.md`

### PR author checklist (quick)
- Run Quickstart locally (`build` + `test:fast`); add `types:check` / `security:scan` as needed
- Add labels to opt into heavy jobs (`run-qa`, `run-security`, `run-formal`) — prefer `ci-non-blocking` during iteration
- Set thresholds via labels when needed (`coverage:<pct>`, `perf:<pct>`, `lh:<pct>`) and enforce with `enforce-*`
- Use slash commands to trigger or adjust runs (`/verify-lite`, `/run-qa-dispatch`, `/coverage <pct>`, `/non-blocking`/`/blocking`)
- Mark ready with `/ready` once green; keep PRs small and revertable

### Troubleshooting (quick)
- Label not taking effect? Verify exact label name and that the workflow reads it (paths/if gates). Try a dispatch command to force-run.
- Outputs not parsed? Ensure printf appends a trailing newline and uses the correct `key=value` or `key<<EOF` format.
- Coverage label rejected? Use integers 0–100 without `%` (e.g., `coverage:85`).

---

## 日本語

本ドキュメントは、品質を維持しつつ PR 体験を高速・安定に保つための CI 方針を定義します。

### 目的
- PR では軽量かつ決定的な検査のみをブロッキング（必須）にする
- 重い/不安定な検査はラベルやパス条件でオプトイン実行
- main と定期実行（スケジュール）で包括的な検査を実施

### 必須チェック（PR ブロッキング）
- Verify Lite（types:check / build）— 備考: lint は Verify Lite 内で非ブロッキング
- 必要に応じて validate-artifacts-ajv / coverage-check を必須化可能
 - カバレッジ運用とRequired化の詳細は `docs/quality/coverage-policy.md` を参照（しきい値の由来、ラベル/変数、main運用）
 - 対応ワークフロー: `.github/workflows/validate-artifacts-ajv.yml`, `.github/workflows/coverage-check.yml`
  - 設定（ブランチ保護）: Settings → Branches → main → Require status checks に Verify Lite と必要なチェックを追加
  - リポジトリ変数: Settings → Variables → Repository variables にて設定（例: `COVERAGE_DEFAULT_THRESHOLD`, `COVERAGE_ENFORCE_MAIN`）

### ポリシーソース / 優先順位
- しきい値 / DoD のソースは次の優先で解決: policy > AE-IR > ae.config（ヒントのみ・警告表示）。詳細は `SECURITY.md` / `docs/quality/coverage-policy.md` を参照。
 - 同一ソース内で複数のしきい値がある場合は、より厳しい（strictest）側でマージします（例: `>=95%` は `>=90%` より厳しい）。

モード（report-only / enforce）
- report-only: 非ブロッキング（PR コメント/アーティファクトの提示のみ）
- enforce: しきい値違反でブロック（`enforce-*` ラベルやブランチ保護の Required checks で有効化）

例（ラベル組み合わせ）
- 非ブロッキングでの試行: `ci-non-blocking` + 必要な `run-*` ラベルを付与
- セキュリティ（report-only）: `run-security` を付与（必要に応じて `ci-non-blocking`）
- セキュリティ（強制）: `run-security` + `enforce-security` を付与

ラベルの値フォーマット
- `coverage:<pct>` / `perf:<pct>` / `lh:<pct>` — 0〜100 の整数（`%` なし）
- `trace:<id>` — 英数・ハイフン・アンダースコアなどの識別子
- `lang:ja` / `lang:en` — PR サマリ言語の切替

### ラベル運用（Opt-in）
- `ci-non-blocking`: 一部ジョブ（traceability, model-check, contracts, security 等）を continue-on-error で実行し PR をブロックしない
- `run-security`: 重いセキュリティ系（Security Scanning, Dependency Audit, License Compliance, CodeQL 等）を PR で実行
- `enforce-security`: セキュリティしきい値を強制（超過時はブロック）。詳細は `SECURITY.md` を参照
- `qa --light`: QA を軽量実行（vitest は `test:fast` 実行）。`ae-ci` の QA ステップに適用済み
- `ae-benchmark run --ci --light --dry-run`: ベンチは PR では構成検証のみに留め、時間・安定性を優先
- `run-qa`: `ae-ci` ワークフローの `qa-bench` を PR で実行（既定は非実行）
- `run-spec`: 仕様 Fail-Fast を PR で有効化
- `run-drift`: Codegen Drift 検出を PR で有効化
- `run-adapters`: Adapter Thresholds（a11y/perf/Lighthouse）をPRでレポート（report-only）。`adapter-thresholds.yml` が要約コメントを投稿
- `run-cedar`: Cedar policies の品質ゲートを実行（report-only）。`.github/workflows/cedar-quality-gates.yml` / `docs/quality/cedar-quality-gates.md`
- `enforce-perf`: perf スコアのしきい値を強制（`perf:<pct>` ラベルで上書き、既定は `vars.PERF_DEFAULT_THRESHOLD` または 75）
- `enforce-lh`: Lighthouse performance スコアのしきい値を強制（`lh:<pct>` ラベルで上書き、既定は `vars.LH_DEFAULT_THRESHOLD` または 80）
- `run-hermetic`: Hermetic CI を PR で有効化
- `run-quality`: Parallel Test の quality 行を有効化
- `run-flake`: flake-detection を PR で有効化
- `run-e2e`: E2E テストを PR で有効化
- `coverage:<pct>`: coverage-check のしきい値を上書き（既定 80）。例: `coverage:75`
  - PR での設定/クリア: `/coverage <pct|clear>`
 - `enforce-coverage`: カバレッジしきい値を強制（閾値未満でブロック）。詳細は `docs/quality/coverage-policy.md` を参照
  - 注意: `<pct>` は 0〜100 の整数（`%` なし）。一般的な値は 70〜95。
 - `run-formal`: PR で Formal Verify と集約レポートを実行（既定は report-only）。`docs/quality/formal-runbook.md` を参照
 - `enforce-formal` / `enforce-contracts`: フォーマル/契約チェックのゲート化を有効化（ラベル制御）
 - `enforce-typecov`: 型カバレッジのしきい値を強制（`docs/quality/type-coverage-policy.md` を参照）
 - `qa-batch:commands` / `qa-batch:cli` / `qa-batch:property` / `qa-batch:agents`: カテゴリ別の CI Fast バッチを実行
 - `lang:ja` / `lang:en`: PR サマリの言語指定（既定 `en`）。`docs/ci/summary-env.md` を参照
 - `pr-summary:detailed`: 詳細な PR サマリを表示（既定の digest より詳細）

対応ワークフロー（抜粋）
- `.github/workflows/ae-ci.yml`（QA light）
- `.github/workflows/ci-fast.yml`（CI Fast バッチ）
- `.github/workflows/workflow-lint.yml`（actionlint）
- `.github/workflows/parallel-test-execution.yml`（quality 行）
- `.github/workflows/flake-detect.yml`（flake 検出）
- `.github/workflows/hermetic-ci.yml`（Hermetic CI）
- `.github/workflows/adapter-thresholds.yml`（Adapters レポート: report-only）
- `.github/workflows/cedar-quality-gates.yml`（Cedar 品質ゲート）
- `.github/workflows/coverage-check.yml`（カバレッジ ゲート/レポート）
- `.github/workflows/sbom-generation.yml`（Security/SBOM）
 - `.github/workflows/fail-fast-spec-validation.yml`（仕様 Fail-Fast）
 - `.github/workflows/formal-verify.yml`（フォーマル検証）
- `.github/workflows/formal-aggregate.yml`（フォーマル集約/コメント）
- `.github/workflows/pr-summary-comment.yml`（PR サマリのアップサート）
 - `.github/workflows/pr-verify.yml`（包括的な PR 検証）
 - `.github/workflows/auto-labels.yml`（PR タイトル/本文からの自動ラベリング）

### クイックスタート（ローカル検証）
- `corepack enable && pnpm i && pnpm -s build && pnpm run test:fast`
  - PR 前の健全性チェックとして Verify Lite と整合。
  - Node は v20（>=20.11, <23）を使用（`engines` に準拠）
  - 任意（ローカルセキュリティスキャン）: `pnpm -s security:scan`
  - 任意（型チェックのみ）: `pnpm -s types:check`
  - 任意（フォーマルツールチェック）: `pnpm -s tools:formal:check`
  - 任意（fast:plus スイート）: `pnpm -s test:fast:plus`
  - 任意（バッチ集中実行）: `pnpm -s test:fast:batch:commands`（他に `:cli` / `:property` / `:agents` あり）

### Verify Lite（既定）
- PR では Verify Lite（types:check / build）のみブロッキング。lint は Verify Lite 内で実行するが非ブロッキング。
- 重いジョブはラベル/パス条件でオプトイン実行。
- 対応ワークフロー: `.github/workflows/verify-lite.yml`

### actionlint と printf ポリシー
- すべてのワークフローは `rhysd/actionlint` をパスすること（`rhysd/actionlint@v1.7.1` を使用。`.github/workflows/workflow-lint.yml` を参照）。
- `$GITHUB_OUTPUT` / `$GITHUB_ENV` への追記は `printf` + 適切なクォートを使用（`echo` は不可）。
  - 例: `printf "name=%s\n" "$VALUE" >> "$GITHUB_OUTPUT"`
  - 例（環境変数）: `printf "%s=%s\n" "FOO" "$VALUE" >> "$GITHUB_ENV"`
  - 行末の改行（`\n`）を必ず含める。欠落すると解析に失敗する可能性あり
  - 複数行の出力:
    - `printf '%s<<EOF\n%s\nEOF\n' 'summary' "$MULTILINE" >> "$GITHUB_OUTPUT"`
  - ローカルでの actionlint 実行:
    - Docker: `docker run --rm -v "$PWD":/repo -w /repo ghcr.io/rhysd/actionlint:1.7.1`
    - Homebrew (macOS): `brew install actionlint`

### PRコメント（Coverage / Formal）
- 重複防止のため固定ヘッダでアップサート（1コメントを更新）:
  - Coverage: `<!-- AE-COVERAGE-SUMMARY -->`
  - Formal Aggregate: `<!-- AE-FORMAL-AGGREGATE -->`
- Coverage コメントの表示順:
  - `Threshold (effective)` → `Derived` → `Policy/Policy source` → ドキュメントリンク
  - しきい値の由来: ラベル > リポジトリ変数 > 既定
- Formal Aggregate コメント:
  - `run-formal` ラベル時のみ投稿（既定は report-only）
  - Tools/Reproduce ヒントを含み、`FORMAL_AGG_LINE_CLAMP` / `FORMAL_AGG_ERRORS_LIMIT` / `FORMAL_AGG_SNIPPET_MAX_LINES` を尊重
 - 参考: `docs/quality/pr-summary.md`（サマリコメントの構成・テンプレート）
  - サマリは `$GITHUB_STEP_SUMMARY` にも追記されます（`pr-summary-comment.yml` を参照）

#### 例

Coverage サマリ（固定ヘッダでアップサート）

```
<!-- AE-COVERAGE-SUMMARY -->
Coverage: Threshold (effective) 80%
Derived: label=coverage:80 > repo var=COVERAGE_DEFAULT_THRESHOLD=75 > default=70
Policy: report-only (see docs/quality/coverage-policy.md)
Links: docs/quality/coverage-policy.md
```

Formal Aggregate（`run-formal` ラベル時のみ投稿）

```
<!-- AE-FORMAL-AGGREGATE -->
Present: Alloy/TLA/SMT summaries available
Summary: 3 tools ran, 0 errors
By-type present: Alloy=present, TLA=present, SMT=present, Apalache=skipped
Apalache ran/ok: skipped (label-gated)
Meta: Tools=installed, Reproduce=see docs/quality/formal-runbook.md
```

### パス条件
- 仕様関連の変更（`spec/**`, `.ae/**`）のみ Fail-Fast を発火
- 依存や大規模コード変更時のみ SBOM/Security を発火
- 対応ワークフロー: `.github/workflows/fail-fast-spec-validation.yml`（仕様）, `.github/workflows/sbom-generation.yml`（セキュリティ）
 - 例（セキュリティ）: `**/package.json` や `pnpm-lock.yaml`、`security/**` の変更でセキュリティ系が発火対象
 - 設定方法: ワークフローの `on.pull_request.paths` または `if: contains(github.event.pull_request.labels.*.name, 'label')` を利用
 - ラベルでの上書き: 必要に応じて `run-spec` / `run-security` を付与し、パス条件に関わらず実行を強制可能
  - `paths-ignore` の活用: ドキュメントのみの変更時は重いジョブを避ける（例: `docs/**`, `**/*.md`）

 
例（YAML）
```
# パスで spec 検証をゲート
on:
  pull_request:
    paths:
      - 'spec/**'

# ラベルでセキュリティをゲート
jobs:
  security:
    if: ${{ github.event_name != 'pull_request' || contains(github.event.pull_request.labels.*.name, 'run-security') }}
    steps:
      - run: echo 'run security steps...'
```

### test:fast（高速CIスイート）
- 目的: Resilience/主要ユニットと軽量統合を即時検証。重い/環境依存テストは除外
- 主な除外: `examples/**`, `**/__e2e__/**`, `tests/examples/**`, `tests/docker/**`, `tests/a11y/**`, `tests/property/**`, `tests/traceability/**`, `tests/security/**`, `tests/contracts/**`, `tests/integration/**`, `tests/resilience/integration.test.ts`, `tests/conformance/**`, `tests/cegis/**`, `tests/cli/**`, `tests/commands/**`, `tests/api/**`, `tests/tdd-setup.test.ts`
- 再導入: 小PRでカテゴリ毎に緑化→除外解除。失敗時は即 revert 可能な粒度。第一弾として `tests/utils/**`、第二弾として `tests/traceability/**`（skip の軽量テストのみ）を再導入。

### QA CLI
- `ae qa --light`: 軽量 QA 実行（`vitest` の `test:fast` を実行）。`ae-ci` の QA ステップで使用。

### セキュリティ/コンプライアンス
- 既定では PR で非必須。ラベル/パス条件で制御（label/path gated）。`run-security` ラベル時のみ実行し、結果は artifacts に集約
- `run-security` ラベル時は、依存脆弱性のサマリと上位ライセンスの簡易サマリを PR コメントに自動投稿（非ブロッキング）
 - 詳細は `SECURITY.md` を参照（閾値/エンフォース、PRコメント例）。

### フォーマル（オプトイン）
- `run-formal` ラベル時のみ、Formal Verify（stub）と成果物の集約（Alloy/TLA/SMT/Apalache の要約）を実行（非ブロッキング）
- 集約結果は PR コメントにアップサート（重複を避けるためヘッダー識別）
- 必須化・閾値強化は段階導入（別Issueで合意のうえ切替）
- `enforce-formal` ラベル時は Apalache 実行結果（summary.ok）が `true` であることをチェック（非true で失敗）

#### 表示/要約の調整（環境変数）
- verify-apalache（要約整形）: `APALACHE_ERRORS_LIMIT`（既定 5）/ `APALACHE_ERROR_LINE_CLAMP`（既定 200）/ `APALACHE_SNIPPET_BEFORE`・`_AFTER`（既定 2/2）
- formal-aggregate（PRコメント整形）: `FORMAL_AGG_LINE_CLAMP`（既定 200）/ `FORMAL_AGG_ERRORS_LIMIT`（既定 5）
- 詳細は `docs/quality/formal-runbook.md` を参照

### カバレッジ（Required運用）
- 変数 `COVERAGE_ENFORCE_MAIN=1` と `COVERAGE_DEFAULT_THRESHOLD`（例: 80）を設定すると、main への push がブロッキング化
- Branch protection の Required checks に `coverage-check / gate` / `coverage-check / coverage` を追加（運用次第）
- 詳細は `docs/quality/coverage-required.md` を参照

### 運用メモ
- 緊急時は `ci-non-blocking` ラベルで PR をブロックしない運用に切替可能
- マージ後は main の包括的 CI（夜間/週次）でカバー
- 必須チェックは基本 Verify Lite を中心に、その他は非必須
- 小PR連投時は `ci-non-blocking` の活用を推奨（反復を阻害しない）
- 注意: `ci-non-blocking` は Required checks を回避しません。ブランチ保護により必須のチェックは引き続き強制されます

### 参考
- 運用ルールとCIラベルポリシー: `AGENTS.md`
- スラッシュコマンド対応表: `.github/workflows/agent-commands.yml`
- CIラベルのゲーティング詳細: `docs/ci/label-gating.md`
 - CIラベル早見表: `docs/cheatsheets/ci-labels-cheatsheet.md`
 - コントリビュータ向け早見表（ラベル）: `CONTRIBUTING.md`（ラベル表）
 - 型カバレッジポリシー: `docs/quality/type-coverage-policy.md`
 - ベンチマーク: `docs/benchmark/README.md`
 - フォーマルツールのセットアップ: `docs/quality/formal-tools-setup.md`
 - フォーマル検証の概要: `docs/verify/FORMAL-CHECKS.md`
 - リポジトリ変数（クイックリファレンス）:
   - `COVERAGE_DEFAULT_THRESHOLD`, `COVERAGE_ENFORCE_MAIN`
   - `PERF_DEFAULT_THRESHOLD`, `LH_DEFAULT_THRESHOLD`
 - PRサマリの環境/切替: `docs/ci/summary-env.md`
 - Adapters しきい値: `docs/quality/adapter-thresholds.md`
 - Cedar 品質ゲート: `docs/quality/cedar-quality-gates.md`
 
### PR作成者チェックリスト（クイック）
- ローカルで Quickstart を実行（`build` + `test:fast`）。必要なら `types:check` / `security:scan` も追加
- 重いジョブはラベルで明示（`run-qa`, `run-security`, `run-formal`）。反復時は `ci-non-blocking` の活用を推奨
- しきい値はラベルで設定（`coverage:<pct>`, `perf:<pct>`, `lh:<pct>`）。強制は `enforce-*` で
- スラッシュコマンドで実行や設定を調整（`/verify-lite`, `/run-qa-dispatch`, `/coverage <pct>`, `/non-blocking`/`/blocking`）
- 緑化後に `/ready`。PR は小さく、revert しやすく維持
 
### トラブルシューティング（クイック）
- ラベルが効かない? ラベル名の一致とワークフローでの参照（paths/if）を確認。必要ならディスパッチで強制実行。
- 出力が解析されない? printf の行末改行と `key=value` / `key<<EOF` 形式を確認。
- カバレッジのラベルが拒否? 0〜100 の整数（`%` なし）で指定（例: `coverage:85`）。
Examples (label combos)
- Non‑blocking exploratory run: add `ci-non-blocking` + selected `run-*` labels
- Security check (report-only): add `run-security` (optionally `ci-non-blocking`)
- Security enforcement on PR: add `run-security` + `enforce-security`
