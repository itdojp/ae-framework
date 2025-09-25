# CI Policy (Fast/Stable by Default) / CI ポリシー（デフォルトは高速・安定）

> 🌍 Language / 言語: English | 日本語

---

## English

This document defines CI policies to keep PR experience fast and stable while maintaining quality.

### Goals
- Block only lightweight, deterministic checks on PRs
- Heavy/unstable checks run opt-in via labels or path conditions
- Comprehensive checks run on main and scheduled jobs

### Required Checks (PR blocking)
- Verify Lite (types:check / lint / build)
- Optionally enable validate-artifacts-ajv / coverage-check as required

### Outputs/Env Append Policy (printf required)
- When appending to GitHub special files, do not use `echo`.
- Always use `printf` with quoting:
  - `printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"`
  - `printf "%s\n" "NAME=value" >> "$GITHUB_ENV"`
- Grouped appends are allowed and recommended for clarity:
  ```bash
  {
    printf "%s\n" "one=1"
    printf "%s\n" "two=2"
  } >> "$GITHUB_OUTPUT"
  ```
- A guard runs in CI (workflow-lint) to block `echo >> $GITHUB_OUTPUT/$GITHUB_ENV` and to require quoted targets.
 - See also: docs/ci/printf-guard.md for full guidance and examples.
  - Quick conversions: docs/ci/echo-to-printf-recipes.md
 - Additional constraints enforced by the guard:
   - Trailing newline required in printf format (prefer `"%s\n"`)
   - Forbid `tee -a` to `$GITHUB_OUTPUT`/`$GITHUB_ENV`
   - Forbid deprecated `::set-output`

### Opt-in Labels
- `ci-non-blocking`: run selected jobs with continue-on-error (traceability, model-check, contracts, security, etc.)
- `run-security`: run heavy security jobs (Security Scanning, Dependency Audit, License Compliance, CodeQL)
- `qa --light`: run QA in light mode (vitest -> `test:fast`); used in `ae-ci`
- `ae-benchmark run --ci --light --dry-run`: benchmark config validation only in PRs (fast & stable)
- `run-qa`: run `ae-ci` workflow’s `qa-bench` on PRs (default off)
- `run-spec`: enable spec fail-fast on PRs
- `run-drift`: enable codegen drift detection on PRs
- `run-hermetic`: enable Hermetic CI on PRs
- `run-quality`: enable quality matrix in parallel tests
- `run-flake`: enable flake-detection on PRs
- `run-e2e`: enable E2E tests on PRs
- `coverage:<pct>`: override coverage threshold for coverage-check (default 80). e.g., `coverage:75`
 - `qa-batch:commands` / `qa-batch:cli` / `qa-batch:property` / `qa-batch:agents`: run additional CI Fast batches for the specific categories (opt-in)

### Comment formatting (Coverage/Adapters)
- Coverage / Adapters comments show:
  - Threshold (effective)
  - Derived: label > repo var > default（a11yは固定: critical=0, serious=0）
  - Policy / Policy source（enforced via label, or report-only）
  - Links to docs

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
  - ラベル付与（Opt-in 実行/ポリシー切替）
    - `/run-qa` … `run-qa` を付与（ae-ci の QA 実行）
    - `/run-security` … `run-security` を付与（Security/SBOM 実行。PR要約も投稿）
    - `/run-hermetic` … `run-hermetic` を付与（Hermetic CI 実行）
    - `/run-spec` … `run-spec` を付与（Fail-Fast Spec 実行）
    - `/run-drift` … `run-drift` を付与（Codegen Drift 検出）
    - `/non-blocking` … `ci-non-blocking` を付与（一部ジョブを continue-on-error）
    - `/ready` … `do-not-merge` を除去（マージ待ちへ）
    - `/pr-digest` / `/pr-detailed` … PR要約モード切替
    - `/run-formal` / `/enforce-formal` / `/enforce-contracts` … フォーマル/契約の実行/エンフォース切替
    - `/coverage <pct|clear>` … `coverage:<pct>` を設定/クリア（しきい値上書き）
    - `/enforce-typecov` … `enforce-typecov` を付与（型カバレッジ enforcement）
    - `/enforce-coverage` … `enforce-coverage` を付与（カバレッジ enforcement）
  - 使い分け例（推奨）
    - 追加確認したいカテゴリのみラベル付与 → `/ci-fast-dispatch` で即時起動
    - Verify Lite のみを再実行 → `/verify-lite`

<!-- duplicate section removed: Slash Commands (Instant Dispatch) repeated -->

### Path Conditions
- Fire spec fail-fast only for changes under `spec/**`, `.ae/**`
- Trigger SBOM/Security only for dependency or major code changes

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
- Default: not required on PRs; run under `run-security`, aggregate results as artifacts
- PR summary comment (non-blocking) is posted when `run-security` is set (dependency vulnerabilities and top licenses)
- Enforce/gate gradually after team agreement (separate issue)

### Operations Notes
- In emergencies, use `ci-non-blocking` to avoid blocking PRs
- After merge, comprehensive CI on main (nightly/weekly) provides coverage
- Keep required checks centered on Verify Lite; others non-required by default

---

## 日本語

本ドキュメントは、品質を維持しつつ PR 体験を高速・安定に保つための CI 方針を定義します。

### 目的
- PR では軽量かつ決定的な検査のみをブロッキング（必須）にする
- 重い/不安定な検査はラベルやパス条件でオプトイン実行
- main と定期実行（スケジュール）で包括的な検査を実施

### 必須チェック（PR ブロッキング）
- Verify Lite（types:check / lint / build）
- 必要に応じて validate-artifacts-ajv / coverage-check を必須化可能
 - カバレッジ運用とRequired化の詳細は `docs/quality/coverage-policy.md` を参照（しきい値の由来、ラベル/変数、main運用）

### ラベル運用（Opt-in）
- `ci-non-blocking`: 一部ジョブ（traceability, model-check, contracts, security 等）を continue-on-error で実行し PR をブロックしない
- `run-security`: 重いセキュリティ系（Security Scanning, Dependency Audit, License Compliance, CodeQL 等）を PR で実行
- `qa --light`: QA を軽量実行（vitest は `test:fast` 実行）。`ae-ci` の QA ステップに適用済み
- `ae-benchmark run --ci --light --dry-run`: ベンチは PR では構成検証のみに留め、時間・安定性を優先
- `run-qa`: `ae-ci` ワークフローの `qa-bench` を PR で実行（既定は非実行）
- `run-spec`: 仕様 Fail-Fast を PR で有効化
- `run-drift`: Codegen Drift 検出を PR で有効化
 - `run-adapters`: Adapter Thresholds（a11y/perf/Lighthouse）をPRでレポート（report-only）。`adapter-thresholds.yml` が要約コメントを投稿
 - `enforce-perf`: perf スコアのしきい値を強制（`perf:<pct>` ラベルで上書き、既定は `vars.PERF_DEFAULT_THRESHOLD` または 75）
 - `enforce-lh`: Lighthouse performance スコアのしきい値を強制（`lh:<pct>` ラベルで上書き、既定は `vars.LH_DEFAULT_THRESHOLD` または 80）
- `run-hermetic`: Hermetic CI を PR で有効化
- `run-quality`: Parallel Test の quality 行を有効化
- `run-flake`: flake-detection を PR で有効化
- `run-e2e`: E2E テストを PR で有効化
- `coverage:<pct>`: coverage-check のしきい値を上書き（既定 80）。例: `coverage:75`

### パス条件
- 仕様関連の変更（`spec/**`, `.ae/**`）のみ Fail-Fast を発火
- 依存や大規模コード変更時のみ SBOM/Security を発火

### test:fast（高速CIスイート）
- 目的: Resilience/主要ユニットと軽量統合を即時検証。重い/環境依存テストは除外
- 主な除外: `examples/**`, `**/__e2e__/**`, `tests/examples/**`, `tests/docker/**`, `tests/a11y/**`, `tests/property/**`, `tests/traceability/**`, `tests/security/**`, `tests/contracts/**`, `tests/integration/**`, `tests/resilience/integration.test.ts`, `tests/conformance/**`, `tests/cegis/**`, `tests/cli/**`, `tests/commands/**`, `tests/api/**`, `tests/tdd-setup.test.ts`
- 再導入: 小PRでカテゴリ毎に緑化→除外解除。失敗時は即 revert 可能な粒度。第一弾として `tests/utils/**`、第二弾として `tests/traceability/**`（skip の軽量テストのみ）を再導入。

### QA CLI
- `ae qa --light`: 軽量 QA 実行（`vitest` の `test:fast` を実行）。`ae-ci` の QA ステップで使用。

### セキュリティ/コンプライアンス
- 既定では PR で非必須（`run-security` ラベル時のみ実行）。結果は artifacts に集約
- `run-security` ラベル時は、依存脆弱性のサマリと上位ライセンスの簡易サマリを PR コメントに自動投稿（非ブロッキング）

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
