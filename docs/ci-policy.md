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

### Path Conditions
- Fire spec fail-fast only for changes under `spec/**`, `.ae/**`
- Trigger SBOM/Security only for dependency or major code changes

### test:fast (Fast CI suite)
- Purpose: verify resilience/core units and lightweight integration quickly; exclude heavy/env-dependent tests
- Current exclusions: `examples/**`, `**/__e2e__/**`, `tests/examples/**`, `tests/docker/**`, `tests/a11y/**`, `tests/property/**`, `tests/traceability/**`, `tests/security/**`, `tests/contracts/**`, `tests/utils/**`, `tests/integration/**`, `tests/resilience/integration.test.ts`, `tests/conformance/**`, `tests/cegis/**`, `tests/cli/**`, `tests/commands/**`, `tests/api/**`, `tests/tdd-setup.test.ts`
- Re‑enablement: green each category in small PRs and remove from exclusions; keep changes revertable

### Security/Compliance
- Default: not required on PRs; run under `run-security`, aggregate results as artifacts
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

### ラベル運用（Opt-in）
- `ci-non-blocking`: 一部ジョブ（traceability, model-check, contracts, security 等）を continue-on-error で実行し PR をブロックしない
- `run-security`: 重いセキュリティ系（Security Scanning, Dependency Audit, License Compliance, CodeQL 等）を PR で実行
- `qa --light`: QA を軽量実行（vitest は `test:fast` 実行）。`ae-ci` の QA ステップに適用済み
- `ae-benchmark run --ci --light --dry-run`: ベンチは PR では構成検証のみに留め、時間・安定性を優先
- `run-qa`: `ae-ci` ワークフローの `qa-bench` を PR で実行（既定は非実行）
- `run-spec`: 仕様 Fail-Fast を PR で有効化
- `run-drift`: Codegen Drift 検出を PR で有効化
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
- 主な除外: `examples/**`, `**/__e2e__/**`, `tests/examples/**`, `tests/docker/**`, `tests/a11y/**`, `tests/property/**`, `tests/traceability/**`, `tests/security/**`, `tests/contracts/**`, `tests/utils/**`, `tests/integration/**`, `tests/resilience/integration.test.ts`, `tests/conformance/**`, `tests/cegis/**`, `tests/cli/**`, `tests/commands/**`, `tests/api/**`, `tests/tdd-setup.test.ts`
- 再導入: 小PRでカテゴリ毎に緑化→除外解除。失敗時は即 revert 可能な粒度

### セキュリティ/コンプライアンス
- 既定では PR で非必須（`run-security` ラベル時のみ実行）。結果は artifacts に集約
- 必須化・閾値強化は段階導入（別Issueで合意のうえ切替）

### 運用メモ
- 緊急時は `ci-non-blocking` ラベルで PR をブロックしない運用に切替可能
- マージ後は main の包括的 CI（夜間/週次）でカバー
- 必須チェックは基本 Verify Lite を中心に、その他は非必須
