---
docRole: derived
canonicalSource:
- policy/risk-policy.yml
- policy/quality.json
lastVerified: '2026-04-06'
---
# Verification Gates Guide

> 🌍 Language / 言語: English | 日本語

---

## English

Verification gates standardize **verify-then-merge**. This document summarizes the current gate taxonomy, how heavier checks are enabled, how the word `contract` should be interpreted in gate names, and where operators should look for evidence.

### Gate categories

- Baseline gates: `types:check` / lint / build / conformance
- Additional gates: property / pact-contract (API) / mutation / MBT / perf / a11y / lighthouse / heavy (CI Extended)
- Formal gates: TLA+ / Alloy (report-only by default, opt-in for stricter execution)

### Enablement guidance (current operations)

- Daily PRs default to the lighter baseline in Verify Lite.
- Heavier gates are usually enabled through opt-in ラベルs.
- Adapter-threshold checks such as perf / lighthouse / a11y are usually enabled through `run-adapters`; `enforce-*` labels only switch those checks from report-only to blocking.

Related documents:
- `docs/ci/label-gating.md`
- `docs/ci/stable-profile.md`
- `docs/quality/adapter-thresholds.md`
- `docs/quality/comparator.md`

### Contract taxonomy in this guide

- See `docs/quality/contract-taxonomy.md` for the canonical meaning split.
- `pact-contract (API)` in this guide refers to **API/Integration contract verification** such as Pact.
- DbC (Design contract: preconditions / postconditions / invariants) is covered through property tests, runtime conformance, and integration assertions rather than a single gate name.
- Artifacts contract means required/optional artifact obligations and is separate from API contract verification.

### Representative gates and entry points

| Gate | How to enable | Primary output | Notes |
| --- | --- | --- | --- |
| property | label `run-property` | `artifacts/properties/` | Executed from CI Extended lanes |
| pact-contract (API) | label `run-integration` or `run-ci-extended` | pact test logs/artifacts (project-defined) | Consumer-driven API contract verification in CI; `pnpm run pipelines:pact` remains the local/manual entrypoint |
| mutation | label `run-mutation` | `reports/mutation/` | quick mode with `ignoreStatic` |
| MBT | label `run-mbt` | `artifacts/mbt/` | Executed from CI Extended lanes |
| perf / a11y / lh | label `run-adapters` (optionally `enforce-perf` / `enforce-a11y` / `enforce-lh` to make blocking) | `reports/perf-results.json`, `reports/a11y-results.json`, `reports/lighthouse-results.json` (or `reports/lh-results.json`) | Adapter-threshold jobs run when `run-adapters` is present; `enforce-*` switches them from report-only to blocking |
| heavy tests | label `run-ci-extended` | `reports/heavy-test-trends.json` | Aggregate for integration / property / MBT / mutation |

#### What `contract` means in gate names

- `contract` in this guide means **API/Integration contract tests** such as Pact.
- DbC concerns are enforced through multiple mechanisms rather than a standalone `contract` gate.

#### Minimal DbC -> verification mapping

| DbC condition | Representative verification method | Representative evidence |
| --- | --- | --- |
| Preconditions | request validation / negative tests / type guards | `artifacts/verify-lite/verify-lite-run-summary.json` (see `docs/quality/ARTIFACTS-CONTRACT.md`) |
| Postconditions | state assertions / event assertions / integration tests | `reports/quality-gates/quality-report-*.json`, `artifacts/hermetic-reports/conformance/summary.json` |
| Invariants | property tests / runtime conformance monitors / DB constraints | `artifacts/properties/summary.json`, `artifacts/hermetic-reports/conformance/summary.json` |

### PR レポート

- Existing template: `docs/quality/pr-summary-template.md`
- Implementation detail: `docs/quality/pr-summary-tool.md`
- Operational goal: summarize verification results in a form that a human reviewer can judge without reopening every raw artifact.

### Report metadata

Quality gate reports (`reports/quality-gates/quality-report-*.json`) include a `meta` object for run-level metadata. That object may contain `runId`, `commitSha`, `branch`, `createdAt`, `agent`, `model`, and `traceId`. Values are taken from CI/local environment variables when available; only `runId` and `createdAt` are always populated.

### Operational caution

- When AI produces code and tests together, blind spots can overlap.
- Spec Kit / Blueprint documents should record adversarial test intent explicitly.
- The baseline remains **CI green plus human approval**, not machine-only approval.

---

## 日本語

検証ゲートは **verify-then-merge** を標準化するための基準です。本ドキュメントでは、現在のゲート分類（current gate taxonomy）、重い検査（heavy check）の有効化方法、ゲート名（gate name）に含まれる `contract` の意味、オペレーター（operator）がどの証跡を見るべきかを整理します。

### ゲート種別

- 基本ゲート（Baseline gates）: `types:check` / lint / build / conformance
- 追加ゲート（Additional gates）: property / pact-contract (API) / mutation / MBT / perf / a11y / lighthouse / heavy (CI Extended)
- Formal ゲート（Formal gates）: TLA+ / Alloy（既定では report-only、必要に応じて stricter execution を opt-in）

### 有効化ガイド（現行運用）

- 日常的な PR は Verify Lite の軽量 baseline を既定とします。
- 重いゲート は通常 opt-in ラベル で有効化します。
- perf / lighthouse / a11y のような adapter-threshold check は通常 `run-adapters` で起動し、`enforce-*` label は report-only から blocking への切替だけを担います。

関連ドキュメント:
- `docs/ci/label-gating.md`
- `docs/ci/stable-profile.md`
- `docs/quality/adapter-thresholds.md`
- `docs/quality/comparator.md`

### 本ガイドにおける contract taxonomy

- 正式な意味分離は `docs/quality/contract-taxonomy.md` を参照してください。
- 本ガイドの `pact-contract (API)` は **API/Integration contract verification**（Pact など）を指します。
- DbC（Design contract: preconditions / postconditions / invariants）は、単一の gate 名ではなく、property test、runtime conformance、integration assertion などの組み合わせで担保します。
- Artifacts contract は required / optional artifact obligation を意味し、API contract verification とは別概念です。

### 代表的なゲートと入口

| Gate | How to enable | Primary output | Notes |
| --- | --- | --- | --- |
| property | label `run-property` | `artifacts/properties/` | CI Extended 側で実行 |
| pact-contract (API) | label `run-integration` または `run-ci-extended` | pact test logs/artifacts (project-defined) | CI 上の consumer-driven API contract verification。`pnpm run pipelines:pact` はローカル / 手動の入口 |
| mutation | label `run-mutation` | `reports/mutation/` | quick mode with `ignoreStatic` |
| MBT | label `run-mbt` | `artifacts/mbt/` | CI Extended 側で実行 |
| perf / a11y / lh | label `run-adapters`（必要に応じて `enforce-perf` / `enforce-a11y` / `enforce-lh` で blocking 化） | `reports/perf-results.json`, `reports/a11y-results.json`, `reports/lighthouse-results.json`（または `reports/lh-results.json`） | adapter-threshold jobs は `run-adapters` で起動し、`enforce-*` は report-only から blocking への切替 |
| heavy tests | label `run-ci-extended` | `reports/heavy-test-trends.json` | integration / property / MBT / mutation の集約 |

#### gate 名における `contract` の意味

- 本ガイドの `contract` は **Pact などの API/Integration contract test** を指します。
- DbC の関心事は、単独の `contract` gate ではなく複数の手段で検証します。

#### DbC -> verification の最小マッピング

| DbC 条件 | 代表的な検証手段 | 代表的な証跡 |
| --- | --- | --- |
| Preconditions | request validation / negative tests / type guards | `artifacts/verify-lite/verify-lite-run-summary.json`（詳細は `docs/quality/ARTIFACTS-CONTRACT.md`） |
| Postconditions | state assertions / event assertions / integration tests | `reports/quality-gates/quality-report-*.json`, `artifacts/hermetic-reports/conformance/summary.json` |
| Invariants | property tests / runtime conformance monitors / DB constraints | `artifacts/properties/summary.json`, `artifacts/hermetic-reports/conformance/summary.json` |

### PR レポート

- 既存テンプレート: `docs/quality/pr-summary-template.md`
- 実装詳細: `docs/quality/pr-summary-tool.md`
- 運用目的: 人間の reviewer が raw artifact をすべて開かなくても判断できる形で verification 結果を要約すること

### レポートメタデータ

quality gate report（`reports/quality-gates/quality-report-*.json`）には、run-level metadata を表す `meta` object が含まれます。代表項目は `runId`、`commitSha`、`branch`、`createdAt`、`agent`、`model`、`traceId` です。値は CI / local environment variable から取得できるものだけを使用し、`runId` と `createdAt` は常に設定されます。

### 運用上の注意

- AI がコードと test を同時に生成すると、盲点が重なる可能性があります。
- Spec Kit / Blueprint document には adversarial test intent を明示してください。
- baseline は machine-only approval ではなく、**CI green + human approval** です。
