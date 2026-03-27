---
docRole: ssot
lastVerified: '2026-03-28'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# OTel Artifacts / Gate Integration Plan (Issue #2380)

> Language / 言語: English | 日本語

---

## English

Last updated: 2026-03-02

### 1. Current state (as of 2026-03-02)

| Area | Current implementation | Confirmed gap |
| --- | --- | --- |
| OTel ingestion | `trace-conformance` in `.github/workflows/spec-generate-model.yml` fetches OTLP payloads with `scripts/trace/fetch-otlp-payload.mjs` and normalizes them to NDJSON with `scripts/trace/convert-otlp-kvonce.mjs` | Normalization rules are still biased toward `kvonce.event.*`; no cross-domain shared contract is documented from the `docs/ci` perspective |
| Artifact outputs | `trace-conformance` currently writes `artifacts/hermetic-reports/trace/**`, `artifacts/kvonce-trace-envelope.json`, and, when needed, `artifacts/kvonce-trace-summary.json`. `verify-lite` must emit `artifacts/verify-lite/verify-lite-run-summary.json` and `artifacts/report-envelope.json` | Naming and placement are split between `verify-lite` artifacts and `kvonce` artifacts; gate scope is not yet explicitly defined |
| Schema validation | `.github/workflows/validate-artifacts-ajv.yml` (`pnpm run artifacts:validate`) validates `schema/envelope.schema.json` and related schemas, and can be made strict via `enforce-artifacts` | Artifacts generated from `spec-generate-model` are not always covered by `validate-artifacts`, depending on the PR execution path |
| Validation / gating | `scripts/trace/run-kvonce-conformance.sh` exits `1` when `kvonce-validation.json` is invalid. `policy-gate` evaluates `enforce-artifacts -> validate-artifacts / validate` from `policy/risk-policy.yml` | `KvOnce Trace Validation` is not yet connected to `policy-gate`, and the `run-trace` label (legacy name: `run-conformance`) still does not trigger execution by itself |
| Required checks | The current `main` baseline in branch protection remains `verify-lite`, `policy-gate`, and `gate`. Dedicated OTel / trace checks are not required yet | No documented promotion criteria or operator path exists for making OTel / trace validation required |

### 2. Non-goals

- This design does not select a collector backend product such as Tempo, Jaeger, S3, or GCS.
- This does not redesign domain invariants beyond KvOnce, such as projector or validator business logic.
- This does not immediately add new Required checks to branch protection; rollout remains phased.

### 3. Design decisions

1. **Standardize through a three-layer split**
   Separate OTel payloads (input), normalized events (processing), and report envelopes plus validation results (output), and fix responsibilities per layer.
2. **Make the artifacts contract the foundation for gating**
   Avoid adding an entirely new gate. Instead, connect the existing `artifacts:validate`, `validate-report-envelope`, and `policy-gate` paths and harden them incrementally.
3. **Tighten gradually through label-driven rollout**
   Keep report-only behavior by default, use existing labels such as `enforce-artifacts` for strict mode, and only decide on Required promotion after stability is proven.
4. **Preserve compatibility for current paths**
   The target-state canonical path is `artifacts/trace/report-envelope.json`, but current workflow outputs such as `artifacts/kvonce-trace-envelope.json` and validation fallbacks remain supported until phased retirement.
5. **Limit gate authority to primary sources**
   Required versus optional decisions must be derived only from `policy/risk-policy.yml` and the branch-protection presets in `.github/branch-protection.main.*.json`.

### 4. Phased rollout plan

#### Phase 0: Fix the baseline
- Publish this document as the SSOT and add it to the CI-facing index.
- Pass docs consistency checks and freeze the baseline for later diffs.

#### Phase 1: Document the OTel normalization contract (report-only)
- Document how `kvonce.event.*` maps to shared event fields such as `traceId`, `timestamp`, `actor`, and `event`.
- Verify that OTLP and NDJSON paths in `spec-generate-model` both produce the same artifact set (events, projection, validation, envelope).
- Do not promote anything to Required at this stage.

#### Phase 2: Unify the artifact output contract
- Explicitly define the minimum gate-target artifacts: at least the trace envelope, trace validation, and verify-lite summary / report-envelope.
- Ensure `enforce-artifacts` in strict mode detects missing or malformed trace artifacts.

#### Phase 3: Connect validation and gating (label-gated blocking)
- Define a PR-context trigger path that reliably starts trace validation, using existing labels or dispatch paths.
- Extend `policy/risk-policy.yml` so `policy-gate` can evaluate trace-validation results.
- Make this blocking only for high-risk PRs with the required labels.

#### Phase 4: Decide on Required promotion
- Review operating data such as failure rate, recovery time, and reproducibility.
- If promotion is approved, update the branch-protection preset and define rollback conditions at the same time.

### 5. Acceptance criteria

- Running `trace-conformance` from `spec-generate-model` must produce `kvonce-validation.json` and `artifacts/kvonce-trace-envelope.json` for both OTLP and NDJSON inputs, and both must pass `schema/envelope.schema.json` validation.
- With `enforce-artifacts` enabled, `pnpm run artifacts:validate -- --strict=true` must detect schema violations in the target artifacts.
- When a high-risk PR has the required labels, `policy-gate` must evaluate the mapped trace gate checks and treat missing execution or failed execution as blocking errors.
- Until Phase 4 completes, Required checks must remain the current `main` baseline of `verify-lite`, `policy-gate`, and `gate`; no dedicated trace check is added yet.

### 6. Related files (primary sources)

#### Workflows
- `.github/workflows/spec-generate-model.yml`
- `.github/workflows/verify-lite.yml`
- `.github/workflows/spec-validation.yml`
- `.github/workflows/validate-artifacts-ajv.yml`
- `.github/workflows/policy-gate.yml`

#### Scripts
- `scripts/trace/fetch-otlp-payload.mjs`
- `scripts/trace/convert-otlp-kvonce.mjs`
- `scripts/trace/run-kvonce-conformance.sh`
- `scripts/trace/create-report-envelope.mjs`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `scripts/ci/policy-gate.mjs`

#### Policy / Schema / Docs
- `policy/risk-policy.yml`
- `schema/envelope.schema.json`
- `schema/trace-bundle.schema.json`
- `schema/trace-bundle-summary.schema.json`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/trace/kvonce-trace-schema.md`
- `docs/trace/otlp-collector-plan.md`

## 日本語

最終更新: 2026-03-02

### 1. 現状（2026-03-02 時点）

| 観点 | 現行実装 | 確認されたギャップ |
| --- | --- | --- |
| OTel 取り込み | `.github/workflows/spec-generate-model.yml` の `trace-conformance` ジョブが `scripts/trace/fetch-otlp-payload.mjs` で OTLP payload を取得し、`scripts/trace/convert-otlp-kvonce.mjs` で NDJSON へ正規化 | 正規化ルールが `kvonce.event.*` 前提で、ドメイン横断の共通契約が `docs/ci` 観点で未定義 |
| Artifacts 出力 | `trace-conformance` の current output は `artifacts/hermetic-reports/trace/**`、`artifacts/kvonce-trace-envelope.json`、必要に応じた `artifacts/kvonce-trace-summary.json`。`verify-lite` は `artifacts/verify-lite/verify-lite-run-summary.json` と `artifacts/report-envelope.json` を必須生成 | 観測系成果物の命名・配置が `verify-lite` 系と `kvonce` 系で分散し、どこまでを gate 対象にするかが未整理 |
| スキーマ検証 | `.github/workflows/validate-artifacts-ajv.yml`（`pnpm run artifacts:validate`）が `schema/envelope.schema.json` 等を検証し、`enforce-artifacts` で strict 化可能 | `spec-generate-model` で生成される成果物は、PR 実行経路によっては `validate-artifacts` の検証対象にならない |
| 検証/ゲート | `scripts/trace/run-kvonce-conformance.sh` は `kvonce-validation.json` が invalid の場合に exit 1。`policy-gate` は `policy/risk-policy.yml` の `enforce-artifacts -> validate-artifacts / validate` を評価 | `KvOnce Trace Validation` チェックは `policy-gate` の評価対象に未接続。`run-trace` ラベル（旧表記: `run-conformance`）は推奨表示のみで実行トリガー未実装 |
| Required checks | current main baseline は branch protection preset の `verify-lite` / `policy-gate` / `gate`。OTel/trace 専用 check はまだ Required に含めない | OTel/trace 検証を Required に昇格する判断基準と導線が未定義 |

### 2. 非ゴール

- 本設計では、Collector 基盤（Tempo/Jaeger/S3/GCS）のプロダクト選定は扱わない。
- KvOnce 以外のドメイン不変条件（projector/validator の業務ロジック）再設計は扱わない。
- 直ちに branch protection の Required checks を増やすことは行わない（段階導入前提）。

### 3. 設計判断

1. **3層分離で標準化する**  
   OTel payload（入力）/ 正規化イベント（処理）/ レポート封筒＋検証結果（出力）を分離し、各層に責務を固定する。
2. **Artifacts contract を gate の基礎に据える**  
   新規 gate 実装を増やさず、既存の `artifacts:validate` + `validate-report-envelope` + `policy-gate` を接続して段階的に強化する。
3. **ラベル駆動で段階的に厳格化する**  
   既定は report-only を維持し、`enforce-artifacts` など既存ラベルで strict 化し、安定後に Required 化判断へ進む。
4. **既存パス互換を維持する**  
   target-state canonical path は `artifacts/trace/report-envelope.json` としつつ、current workflow が出力する `artifacts/kvonce-trace-envelope.json` と validation rule 上の fallback path は段階的に縮退させる。
5. **ゲート判定の一次情報を限定する**  
   Required/optional の判定根拠は `policy/risk-policy.yml` と branch protection preset（`.github/branch-protection.main.*.json`）に統一する。

### 4. 段階導入計画（実装順序）

#### Phase 0: ベースライン固定（現状可視化）
- この運用設計を SSOT として作成し、CI 導線へ索引追加する。
- `docs` 整合チェックを通し、以後の差分検証基準を固定する。

#### Phase 1: OTel 正規化契約の明文化（report-only）
- `kvonce.event.*` と共通イベント項目（`traceId`, `timestamp`, `actor`, `event`）の対応規約を文書化する。
- `spec-generate-model` の OTLP/NDJSON 両経路で、同一の成果物セット（events/projection/validation/envelope）が出ることを確認する。
- この段階では Required 化しない。

#### Phase 2: Artifacts 出力契約の統合
- gate 対象成果物（最低: trace envelope、trace validation、verify-lite summary/report-envelope）を明示し、`artifacts:validate` の対象ルールへ反映する。
- `enforce-artifacts` 運用時に、trace 系成果物の欠損/破損が strict で検出される状態にする。

#### Phase 3: 検証/ゲート接続（label-gated blocking）
- trace 検証を PR 文脈で確実に起動できるトリガー（既存ラベル運用または dispatch 経路）を定義する。
- `policy-gate` が trace 検証結果を評価できるよう、`policy/risk-policy.yml` の gate mapping を追加する。
- 高リスクPRで対象ラベルが付与された場合のみ blocking とする。

#### Phase 4: Required 化判断と昇格
- 連続運用データ（失敗率/復旧時間/再現性）を確認し、Required check 昇格可否を判定する。
- 合意後に branch protection preset を更新し、ロールバック条件（解除手順）を同時定義する。

### 5. 受け入れ基準

- `spec-generate-model` の `trace-conformance` 実行で、OTLP/NDJSON の両ケースに `kvonce-validation.json` と `artifacts/kvonce-trace-envelope.json` が生成され、`schema/envelope.schema.json` 検証を通過する。
- `enforce-artifacts` 有効時、`pnpm run artifacts:validate -- --strict=true` で対象 artifacts のスキーマ違反を検出できる。
- 高リスクPRに必要ラベルが付与された場合、`policy-gate` が対応 gate check を評価し、未実行/失敗を blocking error として扱える。
- Required checks は Phase 4 完了まで current main baseline の `verify-lite` / `policy-gate` / `gate` を維持し、trace 専用 check は追加しない。

### 6. 関連ファイル（一次情報）

#### Workflow
- `.github/workflows/spec-generate-model.yml`
- `.github/workflows/verify-lite.yml`
- `.github/workflows/spec-validation.yml`
- `.github/workflows/validate-artifacts-ajv.yml`
- `.github/workflows/policy-gate.yml`

#### Scripts
- `scripts/trace/fetch-otlp-payload.mjs`
- `scripts/trace/convert-otlp-kvonce.mjs`
- `scripts/trace/run-kvonce-conformance.sh`
- `scripts/trace/create-report-envelope.mjs`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `scripts/ci/policy-gate.mjs`

#### Policy / Schema / Docs
- `policy/risk-policy.yml`
- `schema/envelope.schema.json`
- `schema/trace-bundle.schema.json`
- `schema/trace-bundle-summary.schema.json`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/trace/kvonce-trace-schema.md`
- `docs/trace/otlp-collector-plan.md`
