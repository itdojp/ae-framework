# CI Policy (Fast/Stable by Default) / CI ポリシー（デフォルトは高速・安定）

> 🌍 Language / 言語: English | 日本語

---

## English

This document defines CI policies to keep PR experience fast and stable while maintaining quality.

### Quickstart (local verification)
- `corepack enable && pnpm i && pnpm -s build && pnpm run test:fast`
  - Use this for pre‑PR sanity checks aligned with Verify Lite.
  - Optional (local security scan): `pnpm -s security:scan`

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

### Goals
- Block only lightweight, deterministic checks on PRs
- Heavy/unstable checks run opt-in via labels or path conditions
- Comprehensive checks run on main and scheduled jobs

### Required Checks (PR blocking)
- Verify Lite (types:check / build) — note: lint within Verify Lite is non‑blocking
- Optionally enable validate-artifacts-ajv / coverage-check as required
  - Workflows: `.github/workflows/validate-artifacts-ajv.yml`, `.github/workflows/coverage-check.yml` (see also `docs/quality/coverage-required.md`)
  - Enforce via Branch protection: Settings → Branches → main → Require status checks (add Verify Lite and selected checks)

### Policy sources & precedence
- Threshold/DoD sources resolve in this order: policy > AE-IR > ae.config (hints only; warn on use). See also `SECURITY.md` and `docs/quality/coverage-policy.md`.

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
 - `enforce-perf`: enforce performance score threshold (override via `perf:<pct>`, default `vars.PERF_DEFAULT_THRESHOLD` or 75)
 - `enforce-lh`: enforce Lighthouse performance threshold (override via `lh:<pct>`, default `vars.LH_DEFAULT_THRESHOLD` or 80)
- `lang:ja` / `lang:en`: select PR summary language (default `en`). See `docs/ci/summary-env.md`.
 - `pr-summary:detailed`: render a more detailed PR summary (vs. digest)

Workflows (selected)
- `.github/workflows/ae-ci.yml` (QA light)
- `.github/workflows/ci-fast.yml` (CI Fast batches)
- `.github/workflows/parallel-test-execution.yml` (quality row)
- `.github/workflows/flake-detect.yml` (flake detection)
- `.github/workflows/hermetic-ci.yml` (Hermetic CI)
 - `.github/workflows/adapter-thresholds.yml` (Adapters report-only)
 - `.github/workflows/cedar-quality-gates.yml` (Cedar policies quality gates)


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
    - `/enforce-typecov` … `enforce-typecov` を付与（型カバレッジ enforcement）
    - `/enforce-coverage` … `enforce-coverage` を付与（カバレッジ enforcement）
  - 使い分け例（推奨）
    - 追加確認したいカテゴリのみラベル付与 → `/ci-fast-dispatch` で即時起動
    - Verify Lite のみを再実行 → `/verify-lite`


### Path Conditions
- Fire spec fail-fast only for changes under `spec/**`, `.ae/**`
- Trigger SBOM/Security only for dependency or major code changes
- Workflows: `.github/workflows/fail-fast-spec-validation.yml` (spec), `.github/workflows/sbom-generation.yml` (security)
 - Examples (security): changes to `**/package.json`, `pnpm-lock.yaml`, `security/**` may trigger security workflows
 - Configure in workflows via `on.pull_request.paths` and/or `if: contains(github.event.pull_request.labels.*.name, 'label')`
 - Override via labels when needed: e.g., add `run-spec` or `run-security` to force execution regardless of path filters
 
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

### Security/Compliance
- Default: not required on PRs; label/path gated; run under `run-security`, aggregate results as artifacts
- PR summary comment (non-blocking) is posted when `run-security` is set (dependency vulnerabilities and top licenses)
- Enforce/gate gradually after team agreement (separate issue)
 - See `SECURITY.md` for thresholds/enforcement policy and PR comment example.

### Operations Notes
- In emergencies, use `ci-non-blocking` to avoid blocking PRs
- After merge, comprehensive CI on main (nightly/weekly) provides coverage
- Keep required checks centered on Verify Lite; others non-required by default

### References
- Agent collaboration rules and CI label policies: `AGENTS.md`
- Slash command mappings: `.github/workflows/agent-commands.yml`

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

### ポリシーソース / 優先順位
- しきい値 / DoD のソースは次の優先で解決: policy > AE-IR > ae.config（ヒントのみ・警告表示）。詳細は `SECURITY.md` / `docs/quality/coverage-policy.md` を参照。

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
 - `run-formal`: PR で Formal Verify と集約レポートを実行（既定は report-only）。`docs/quality/formal-runbook.md` を参照
 - `enforce-formal` / `enforce-contracts`: フォーマル/契約チェックのゲート化を有効化（ラベル制御）
 - `enforce-typecov`: 型カバレッジのしきい値を強制（`docs/quality/type-coverage-policy.md` を参照）
 - `qa-batch:commands` / `qa-batch:cli` / `qa-batch:property` / `qa-batch:agents`: カテゴリ別の CI Fast バッチを実行
 - `lang:ja` / `lang:en`: PR サマリの言語指定（既定 `en`）。`docs/ci/summary-env.md` を参照
 - `pr-summary:detailed`: 詳細な PR サマリを表示（既定の digest より詳細）

対応ワークフロー（抜粋）
- `.github/workflows/ae-ci.yml`（QA light）
- `.github/workflows/ci-fast.yml`（CI Fast バッチ）
- `.github/workflows/parallel-test-execution.yml`（quality 行）
- `.github/workflows/flake-detect.yml`（flake 検出）
- `.github/workflows/hermetic-ci.yml`（Hermetic CI）
 - `.github/workflows/adapter-thresholds.yml`（Adapters レポート: report-only）
 - `.github/workflows/cedar-quality-gates.yml`（Cedar 品質ゲート）

### クイックスタート（ローカル検証）
- `corepack enable && pnpm i && pnpm -s build && pnpm run test:fast`
  - PR 前の健全性チェックとして Verify Lite と整合。
  - 任意（ローカルセキュリティスキャン）: `pnpm -s security:scan`

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

### 参考
- 運用ルールとCIラベルポリシー: `AGENTS.md`
- スラッシュコマンド対応表: `.github/workflows/agent-commands.yml`
