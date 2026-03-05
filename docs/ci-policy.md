# CI Policy (Fast/Stable by Default) / CI ポリシー（デフォルトは高速・安定）

> 🌍 Language / 言語: English | 日本語

---

## English

This document defines CI policies to keep PR experience fast and stable while maintaining quality.

### Goals
- Block only lightweight, deterministic checks on PRs
- Heavy/unstable checks run opt-in via labels or path conditions
- Comprehensive checks run on main and scheduled jobs

### Document Boundary (Policy vs Operations)
- This document defines policy decisions (required checks, opt-in labels, dispatch rules).
- Operational procedures (daily checks / rerun / emergency stop) are maintained in `docs/ci/ci-operations-handbook.md`.
- Troubleshooting details are maintained in `docs/ci/ci-troubleshooting-guide.md`.
- Responsibility matrix: `docs/ci/ci-doc-boundary-matrix.md`.

### Required Checks (PR blocking)
- Verify Lite (`test:ci:lite`=types:check / lint / build / conformance)
- Docs Doctest (`docs-doctest.yml`): `README.md` + `docs/README.md` doctest, plus changed Markdown doctest for docs-touching PRs
- Quality Gates (development profile):
  - Lint baseline enforcement via `node scripts/quality/check-lint-summary.mjs`
  - TDD smoke validation via `node scripts/quality/tdd-smoke-check.mjs`
- Copilot Review Gate（Copilotレビューの存在と未解決スレッドなし）
- Lockfile reproducibility: required PR gates and their reusable workflow lane use `pnpm install --frozen-lockfile` (no `--no-frozen-lockfile` fallback)
- Optionally enable validate-artifacts-ajv / coverage-check as required

### Opt-in Labels
- `ci-non-blocking`: run selected jobs with continue-on-error (traceability, model-check, formal-contract checks, security, etc.)
- `run-security`: run heavy security jobs (Security Scanning, Dependency Audit, License Compliance, CodeQL)
- `run-ci-extended`: trigger CI Extended workflow (`test:int`, property harness, MBT smoke, Pact smoke, mutation auto diff)
- `run-integration`: request the integration subset of CI Extended (integration vitest + pact smoke)
- `run-property`: execute property harness smoke within CI Extended
- `run-mbt`: execute MBT smoke (`test:mbt:ci`) within CI Extended
- `run-mutation`: execute mutation auto diff (extended pipeline)
- Terminology note:
  - `pact` in CI Extended refers to **API/Integration contract verification**
  - `/enforce-contracts` refers to **formal/DbC-oriented contract enforcement**
  - See `docs/quality/contract-taxonomy.md` for the canonical split

CI Extended restores cached heavy test artifacts (`.cache/test-results`) when rerunning; the cache is refreshed at the end of each run via `node scripts/pipelines/sync-test-results.mjs --store`. Check or warm the cache locally with `--status` / `--restore` before dispatching reruns. Nightly runs use a stable cache key (`ci-heavy-${ runner.os }-schedule`) so the previous baseline is rehydrated before execution, call `node scripts/pipelines/compare-test-trends.mjs` to produce a Markdown diff (posted to the Step Summary), and persist both `reports/heavy-test-trends.json` and `reports/heavy-test-trends-history/<timestamp>.json` as artifacts (`heavy-test-trends`, `heavy-test-trends-history`).
- `qa --light`: run QA in light mode (vitest -> `test:fast`); QA bench (`ae-ci`, ci.yml から呼び出し) で使用
- Note: QA coverage thresholds are sourced from `policy/quality.json`. `config/ae.config.*` coverageThreshold is a local hint only and is ignored in CI. Local runs will emit a warning when it is present.
- `ae-benchmark run --ci --light --dry-run`: benchmark config validation only in PRs (fast & stable)
- `run-qa`: PR で QA bench を実行（ci.yml から `ae-ci` を呼び出し、既定は非実行）
- `run-spec`: enable spec fail-fast on PRs
- `run-drift`: enable codegen drift detection on PRs
- Quick when-to-use (opt-in labels)
  - `run-security`: trigger Security/SBOM on PRs when touching deps, crypto/security code, or before release; otherwise weekly cron covers the baseline
  - `run-hermetic`: trigger Hermetic CI on PRs when build determinism or network isolation must be validated
  - `run-qa`: run QA bench on PRs when behavior/perf regressions are suspected; otherwise cron/main covers it
- `run-quality`: enable quality matrix in parallel tests
- `run-flake`: enable flake-detection on PRs
- `run-e2e`: enable E2E tests on PRs
- `coverage:<pct>`: override coverage threshold for coverage-check (default 80). e.g., `coverage:75`
- `enforce-context-pack`: enable blocking mode for `context-pack-quality-gate.yml` on PRs
 - `qa-batch:commands` / `qa-batch:cli` / `qa-batch:property` / `qa-batch:agents`: run additional CI Fast batches for the specific categories (opt-in)
- `enforce-ts-inventory`: in Verify Lite, enforce no increase of `@ts-ignore` against `config/ts-inventory-baseline.json` (label-gated). `pnpm run inventory:ts` is always collected in non-docs-only runs (`artifacts/verify-lite/ts-inventory.json`).

### Comment formatting (Coverage/Adapters)
- Coverage / Adapters comments show:
  - Threshold (effective)
  - Derived: label > repo var > default（a11yは固定: critical=0, serious=0）
  - Policy / Policy source（enforced via label, or report-only）
  - Links to docs
  - (Dev toggles) AE_COVERAGE_DRY_RUN / AE_COVERAGE_SKIP_COMMENT / AE_COVERAGE_SUMMARY_PATH

### Slash Commands (Instant Dispatch / Labels)
- コメントで以下を投稿すると、対象ワークフローの即時起動やラベル付与ができます（main取り込み後有効）。
  - Dispatch（workflow_dispatch 直起動）
    - `/review [strict]` … Verify Lite + CI Fast を実行（`strict` 指定時は `enforce-coverage` を付与し coverage-check を併走）
    - `/verify-lite` … Verify Lite を実行
    - `/run-qa-dispatch` … ae-ci（QA light）を実行
    - `/run-security-dispatch` … sbom-generation（Security/SBOM）を実行
    - `/ci-fast-dispatch` … CI Fast を実行（バッチ系は対応ラベル付与時のみ稼働）
    - `/formal-verify-dispatch` … Formal Verify を実行（`run-formal` との併用推奨）
    - `/formal-aggregate-dispatch` … Formal Reports Aggregate を実行（`run-formal` 併用時に集約コメントを生成）
    - `/run-flake-dispatch` … flake-detect を実行
    - `/spec-validation-dispatch` … spec-validation を実行
  - 手動実行（Actions UI）
    - `Flake Stability Schedule`（`flake-detect.yml`）は workflow_dispatch で `mode=retry` と `workflow_file` / `eligibility_artifact` / `eligibility_path` / `dry_run` を指定可能
    - 詳細: docs/ci/flake-retry-dispatch.md
  - ラベル付与（Opt-in 実行/ポリシー切替）
    - `/run-qa` … `run-qa` を付与（ci.yml から QA bench を実行）
    - `/run-security` … `run-security` を付与（Security/SBOM 実行。PR要約も投稿）
    - `/run-hermetic` … `run-hermetic` を付与（Hermetic CI 実行）
    - `/run-spec` … `run-spec` を付与（Fail-Fast Spec 実行）
    - `/run-drift` … `run-drift` を付与（Codegen Drift 検出）
    - `/non-blocking` … `ci-non-blocking` を付与（一部ジョブを continue-on-error）
    - `/ready` … `do-not-merge` を除去（マージ待ちへ）
    - `/pr-digest` / `/pr-detailed` … PR要約モード切替
    - `/run-formal` / `/enforce-formal` / `/enforce-contracts` … フォーマル（DbC系）契約の実行/エンフォース切替
    - `/coverage <pct|clear>` … `coverage:<pct>` を設定/クリア（しきい値上書き）
    - `/enforce-typecov` … `enforce-typecov` を付与（型カバレッジ enforcement）
    - `/enforce-coverage` … `enforce-coverage` を付与（カバレッジ enforcement）
    - `/enforce-context-pack` … `enforce-context-pack` を付与（Context Pack gate strict）
  - 使い分け例（推奨）
    - 追加確認したいカテゴリのみラベル付与 → `/ci-fast-dispatch` で即時起動
    - Verify Lite のみを再実行 → `/verify-lite`
    - 基本ゲートをまとめて起動 → `/review`（必要なら `/review strict`）

### 参考ドキュメント
- Branch Protection運用（プリセット適用/復元）: docs/ci/branch-protection-operations.md
- Docs Doctest運用: docs/ci/docs-doctest-policy.md
- CI運用ハンドブック（日次オペレーション）: docs/ci/ci-operations-handbook.md
- CIトラブルシューティング: docs/ci/ci-troubleshooting-guide.md
- Copilot Review Gate運用: docs/ci/copilot-review-gate.md
- Copilot Auto Fix（suggestion 自動適用）: docs/ci/copilot-auto-fix.md
- Auto Merge（auto-merge 自動有効化）: docs/ci/auto-merge.md
- PR automation runbook: docs/ci/pr-automation.md
- Workflow role matrix: docs/ci/workflow-role-matrix.md
- Opt-in controls: docs/ci/OPT-IN-CONTROLS.md
- CI docs boundary matrix: docs/ci/ci-doc-boundary-matrix.md

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

### test:ci lite / extended
- `test:ci:lite`: entry point for Verify Lite locally. Runs types:check / lint / build / conformance report to mirror the PR blocking suite.
- `test:ci:extended`: runs Integration (`test:int`), property harness, `test:mbt:ci`, `pipelines:pact`, and finishes with `pipelines:mutation:quick` for local reproduction of the heavy suite.
- `.github/workflows/ci-extended.yml`: triggered automatically on `main` pushes / nightly schedule, and opt-in for PRs via `run-ci-extended`. Use `run-integration` / `run-property` / `run-mbt` / `run-mutation` for subset execution.
- Vitest-based stable profile remains available as `test:ci:stable` (used by Docker/Podman smoke images).
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

### 文書の責務境界（方針と運用）
- 本書は方針（Required checks / opt-in labels / dispatch規約）を定義する。
- 日次運用・再実行・停止復帰の手順は `docs/ci/ci-operations-handbook.md` を正とする。
- 障害時の詳細診断は `docs/ci/ci-troubleshooting-guide.md` を参照する。
- 責務一覧は `docs/ci/ci-doc-boundary-matrix.md` に集約する。

### 必須チェック（PR ブロッキング）
- Verify Lite（`test:ci:lite` = types:check / lint / build / conformance）
- Docs Doctest（`docs-doctest.yml`）: docs 変更PRで `README.md` + `docs/README.md` に加えて差分 Markdown の doctest を実行
- Quality Gates（development プロファイル）:
  - `node scripts/quality/check-lint-summary.mjs` による lint ベースライン差分チェック
  - `node scripts/quality/tdd-smoke-check.mjs` による TDD スモーク検証
- Copilot Review Gate（Copilotレビューの存在と未解決スレッドなし）
- lockfile 再現性: 必須ゲートおよびその reusable workflow 経路では `pnpm install --frozen-lockfile` を使用し、`--no-frozen-lockfile` へフォールバックしない
- 必要に応じて validate-artifacts-ajv / coverage-check を必須化可能
 - カバレッジ運用とRequired化の詳細は `docs/quality/coverage-policy.md` を参照（しきい値の由来、ラベル/変数、main運用）

### ラベル運用（Opt-in）
- `ci-non-blocking`: 一部ジョブ（traceability, model-check, formal系contract, security 等）を continue-on-error で実行し PR をブロックしない
- `run-security`: 重いセキュリティ系（Security Scanning, Dependency Audit, License Compliance, CodeQL 等）を PR で実行
- `run-ci-extended`: CI Extended ワークフローを起動（integration / property / MBT / pact / mutation auto diff のフルスイート）
- `run-integration`: CI Extended の統合テスト＋pact のみを実行
- `run-property`: CI Extended の property harness のみを実行
- `run-mbt`: CI Extended の `test:mbt:ci` のみを実行
- `run-mutation`: CI Extended の mutation auto diff のみを実行
- 用語注記:
  - `pact` は **API/Integration contract** 検証を指す
  - `/enforce-contracts` は **formal/DbC系 contract** のエンフォースを指す
  - 用語基準は `docs/quality/contract-taxonomy.md`

CI Extended 実行後は heavy テスト成果物を `.cache/test-results` に保存し、再実行時に自動復元します。必要に応じて `node scripts/pipelines/sync-test-results.mjs --status` / `--restore` でキャッシュの状態を確認・展開してから再実行できます。差分の確認は `node scripts/pipelines/compare-test-trends.mjs` を実行すると Markdown と JSON で出力され、Step Summary にも自動追記されます。
- `qa --light`: QA を軽量実行（vitest は `test:fast` 実行）。QA bench（`ae-ci`）に適用済み
- `ae-benchmark run --ci --light --dry-run`: ベンチは PR では構成検証のみに留め、時間・安定性を優先
- `run-qa`: PR で QA bench を実行（ci.yml から `ae-ci` を呼び出し、既定は非実行）
- `run-spec`: 仕様 Fail-Fast を PR で有効化
- `run-drift`: Codegen Drift 検出を PR で有効化
- 使い所（オプトイン ラベル）
  - `run-security`: 依存・暗号/セキュリティ関連変更やリリース前に Security/SBOM をPRで即時実行（通常は週次cronでベースライン実行）
  - `run-hermetic`: ビルド決定性やネットワーク隔離をPRで確認したい場合に Hermetic CI を実行
  - `run-qa`: 挙動/性能劣化が疑われるPRで QA bench を実行（通常は main/cron がカバー）
 - `run-adapters`: Adapter Thresholds（a11y/perf/Lighthouse）をPRでレポート（report-only）。`adapter-thresholds.yml` が要約コメントを投稿
 - `enforce-perf`: perf スコアのしきい値を強制（`perf:<pct>` ラベルで上書き、既定は `vars.PERF_DEFAULT_THRESHOLD` または 75）
 - `enforce-lh`: Lighthouse performance スコアのしきい値を強制（`lh:<pct>` ラベルで上書き、既定は `vars.LH_DEFAULT_THRESHOLD` または 80）
- `run-quality`: Parallel Test の quality 行を有効化
- `run-flake`: flake-detection を PR で有効化
- `run-e2e`: E2E テストを PR で有効化
- `coverage:<pct>`: coverage-check のしきい値を上書き（既定 80）。例: `coverage:75`
- `enforce-context-pack`: `context-pack-quality-gate.yml` を PR で blocking 化
- `enforce-ts-inventory`: Verify Lite で `config/ts-inventory-baseline.json` 基準の `@ts-ignore` 増加を禁止（ラベル付与時のみ強制）。docs-only 以外では `pnpm run inventory:ts` の結果を `artifacts/verify-lite/ts-inventory.json` に収集。

### 手動実行（Actions UI）
- `Flake Stability Schedule`（`flake-detect.yml`）は workflow_dispatch で `mode=retry` と `workflow_file` / `eligibility_artifact` / `eligibility_path` / `dry_run` を指定可能
  - 詳細: docs/ci/flake-retry-dispatch.md

### パス条件
- 仕様関連の変更（`spec/**`, `.ae/**`）のみ Fail-Fast を発火
- 依存や大規模コード変更時のみ SBOM/Security を発火

### test:fast（高速CIスイート）
- 目的: Resilience/主要ユニットと軽量統合を即時検証。重い/環境依存テストは除外
- 主な除外: `examples/**`, `**/__e2e__/**`, `tests/examples/**`, `tests/docker/**`, `tests/a11y/**`, `tests/property/**`, `tests/traceability/**`, `tests/security/**`, `tests/contracts/**`, `tests/integration/**`, `tests/resilience/integration.test.ts`, `tests/conformance/**`, `tests/cegis/**`, `tests/cli/**`, `tests/commands/**`, `tests/api/**`, `tests/tdd-setup.test.ts`
- 再導入: 小PRでカテゴリ毎に緑化→除外解除。失敗時は即 revert 可能な粒度。第一弾として `tests/utils/**`、第二弾として `tests/traceability/**`（skip の軽量テストのみ）を再導入。

### test:ci（ライト / 拡張）
- `test:ci:lite`: Verify Lite のローカル実行口。types:check / lint / build / conformance report をまとめて実行し、PR ブロッキングの最小セットを再現。
- `test:ci:extended`: Integration（`test:int`）/ property harness / `test:mbt:ci` / `pipelines:pact` を連続実行し、最後に `pipelines:mutation:quick` で mutation quick を叩くローカル向け統合スイート。
- 拡張スイートで生成される成果物は `.cache/test-results` にキャッシュされるため、再実行前に `node scripts/pipelines/sync-test-results.mjs --restore` を実行すると mutation survivors / MBT summary / property summary を再利用できます（ローカル実行後は `--store` で更新）。
- `.github/workflows/ci-extended.yml`: `run-ci-extended` で上記一式を PR から opt-in。`run-integration` / `run-property` / `run-mbt` / `run-mutation` で部分実行を選択でき、main push / schedule では常時稼働。
- Vitest ベースの安定プロファイルは従来通り `test:ci:stable`（Docker/Podman smoke イメージで利用）として提供。

### QA CLI
- `ae qa --light`: 軽量 QA 実行（`vitest` の `test:fast` を実行）。QA bench（`ae-ci`）で使用。
  - QA の coverage しきい値は `policy/quality.json` が単一情報源。`config/ae.config.*` の coverageThreshold はローカルヒント扱いで、CI では無視される。ローカル実行では設定検出時に警告を出す。

### セキュリティ/コンプライアンス
- 既定では PR で非必須（`run-security` ラベル時のみ実行）。結果は artifacts に集約
- `run-security` ラベル時は、依存脆弱性のサマリと上位ライセンスの簡易サマリを PR コメントに自動投稿（非ブロッキング）

### フォーマル（オプトイン）
- `run-formal` ラベル時のみ、Formal Verify（stub）と成果物の集約（Alloy/TLA/SMT/Apalache の要約）を実行（非ブロッキング）
- 集約結果は PR コメントにアップサート（重複を避けるためヘッダー識別）
- 必須化・閾値強化は段階導入（別Issueで合意のうえ切替）
- `enforce-formal` ラベル時は Apalache 実行結果（summary.ok）が `true` であることをチェック（非true で失敗）し、Formal Summary v1 のスキーマ検証も strict にします。

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


## ワークフロー正規化ツール（自動化）

反復的な修正を減らすため、正規化スクリプトを用意しています。

- 一覧表示: `node scripts/ci/normalize-workflows.mjs --list`
- concurrency 追加（dry-run）: `node scripts/ci/normalize-workflows.mjs --rule=concurrency`
- concurrency 追加（適用）: `node scripts/ci/normalize-workflows.mjs --rule=concurrency --apply`
- setup-node-pnpm 監査（report-only）: `node scripts/ci/normalize-workflows.mjs --rule=setup-node-pnpm`

※ `setup-node-pnpm` は現在 audit-only で、適用は手動PRで行います。

## 6. 参照

- `docs/ci/docs-doctest-policy.md`
- `docs/ci/ci-operations-handbook.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/pr-automation.md`
- `docs/ci/workflow-role-matrix.md`
- `docs/ci/OPT-IN-CONTROLS.md`
- `docs/ci/ci-doc-boundary-matrix.md`
