---
docRole: ssot
lastVerified: '2026-07-01'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Schema Governance (`$id` canonical URI policy)

> Language / 言語: English | 日本語

---

## English

This document defines URI governance for JSON Schema identifiers in `schema/*.schema.json`.

### 1. Canonical URI vs hosted URI

- Canonical schema identifier (`$id`): `https://ae-framework/schema/<file>`
- Hosted retrieval URL (GitHub Pages): `https://itdojp.github.io/ae-framework/schema/<file>`

Use `https://ae-framework/schema/<file>` as the canonical identifier for new or migrated schemas.  
Use `https://itdojp.github.io/ae-framework/schema/<file>` as the hosted access endpoint when a directly dereferenceable URL is required.

### 2. Current implementation snapshot (as-is)

Most schemas already use `https://ae-framework/schema/<file>`.  
The following schemas currently keep GitHub Pages-based `$id` for compatibility:

- `schema/codex-task-request.schema.json`
- `schema/codex-task-response.schema.json`
- `schema/quality-report.schema.json`
- `schema/verify-profile-summary.schema.json`

Current preview metric additions use the canonical URI policy. `schema/req2run-metrics.schema.json` identifies the report-only `req2run-metrics/v1` artifact for adoption-readiness evidence and is validated through `scripts/ci/validate-json.mjs`; it does not create a blocking policy-gate condition.

### 3. Contract lifecycle states

Use the following lifecycle states for assurance-related schema and artifact contracts. These states are documentation and release-governance labels; they do not by themselves change CI enforcement.

| State | Meaning | Producer / consumer rule | Promotion or removal condition |
| --- | --- | --- | --- |
| `stable` | Default contract for production or release evidence in its scope. | Producers may emit it by default; consumers may rely on it without opt-in flags. | Breaking changes require a new versioned contract, migration note, consumer-impact assessment, and compatibility window. |
| `preview` | Implemented for early adoption, report-only use, or dual-write validation. | Producers may emit it behind opt-in, dual-write, or documented preview commands; consumers must tolerate absence. | Promote only after fixture coverage, contract validation, summary rendering, and consumer-path tests are present. |
| `deprecated` | Supported but scheduled for replacement. | Producers and consumers may still read/write it during the deprecation window. New work should link to the replacement. | Remove only after replacement adoption evidence, rollback guidance, and a retirement issue are recorded. |
| `legacy-compatible` | Compatibility route retained because at least one workflow, script, document, or operator path can still consume it. | Keep validation or adapter behavior stable; clearly mark the canonical replacement. | Reclassify to `deprecated` or `removed` only after consumer-path tests prove the canonical route covers the behavior. |
| `removed` | Contract or route is no longer supported by current producers/consumers. | Do not emit new artifacts in this shape. Consumers should fail with explicit migration guidance when feasible. | Requires prior deprecation evidence or a documented security/correctness exception. |

Preview-to-stable promotion requires all of the following evidence in the same PR or linked issue:

- schema and fixture validation for the promoted contract;
- contract catalog and canonical-route updates;
- producer and consumer tests for the promoted route;
- PR/release summary behavior for non-green, waived, partial, or migration-relevant states when applicable;
- migration note and rollback guidance when replacing an existing route.

### 4. Anti-pattern (forbidden)

Do not use repository URLs directly in `$id` or `$ref`:

- `https://github.com/itdojp/ae-framework/.../schema/<file>`
- `https://raw.githubusercontent.com/itdojp/ae-framework/.../schema/<file>`

These URLs are branch/path-coupled and are not stable schema identifiers.

### 5. Why this policy

- Keep schema identity independent from hosting location.
- Preserve backward compatibility for already consumed legacy schema IDs.
- Prevent accidental dependence on mutable GitHub repository paths.

### 6. Operational rules

- Keep `<file>` in URI exactly equal to the schema filename under `schema/`.
- If changing `$id` of an already published schema, treat it as compatibility-impacting and follow `docs/project/RELEASE.md`.
- Every `schema/*.schema.json` file must define `$id`.

### 7. Review checklist

- `$id` follows canonical/legacy exception rules above.
- No `github.com` or `raw.githubusercontent.com` URL appears in `$id`/`$ref`.
- Compatibility impact is assessed when `$id` changes.
- Related docs and fixtures are updated.

### 8. CI checkpoints

- `schema/**` changes trigger `.github/workflows/spec-validation.yml`.
- Assurance contract governance markers can be checked locally with `pnpm -s run check:assurance-contract-governance`; this check is deterministic documentation/schema consistency support and does not prove code correctness.
- Schema/artifact validation is executed in:
  - `.github/workflows/validate-artifacts-ajv.yml`
  - `.github/workflows/verify-lite.yml`
  - `.github/workflows/minimal-pipeline.yml`
- Documentation consistency is checked by `pnpm docs:lint`.

### 9. Payload versioning (`schemaVersion` / `contractId`)

- `schemaVersion` is a payload compatibility marker; `$id` and `$schema` are schema-identifier metadata. Treat them separately.
- Allowed forms in current implementation:
  - semver (`1.0.0`) for schema families that already use semantic versioning.
  - contract-style (`<contract>/v1`) as a fixed `const` value for contract families managed by major line.
- `contractId` is a stable contract family identifier (example: `pr-state.v1`, `execution-plan.v1`) and should be fixed by schema `const` when present.
- New machine-readable artifacts should include at least one explicit compatibility key (`schemaVersion` or `contractId`); include both when the producer has long-lived consumers.
- Mixed version expression inside one contract family is forbidden. Choose one migration target and keep dual-read compatibility during transition.
- Release / migration notes must describe the boundary change in the contract family's own style. Do not force a contract-style family into semver just to satisfy release bookkeeping.

### 10. Dual-write / dual-validate migration rules

- When introducing breaking changes, do not overwrite the existing schema/artifact contract in place.
- Use migration phases:
  1. **Dual-write**: producer emits old and new payloads side by side.
  2. **Dual-validate**: CI validates both payloads against their corresponding schemas.
  3. **Cutover**: switch default consumer to new payload.
  4. **Retire**: remove old payload after deprecation window and evidence review.
- During dual period, define:
  - canonical payload (`new` or `old`)
  - start/end condition (issue-based)
  - rollback rule and flag strategy
  - required fixture/test updates

### 11. Breaking-change checklist (schema contracts)

- Breaking examples:
  - removing/renaming required fields
  - changing field type or narrowing enum/pattern in incompatible ways
  - changing semantic meaning without compatibility adapter
  - changing `$id`, `schemaVersion`, or `contractId` compatibility boundary
- Required in the same PR:
  - new schema file / new fixture updates
  - dual-read or migration adapter updates
  - CI validation update (`scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` as needed)
  - release note entry and migration note (`docs/project/RELEASE.md`)
  - contract catalog update (`docs/reference/CONTRACT-CATALOG.md`)

### 12. Migration note examples

Acceptable migration note:

> `claim-level-summary/v1` remains preview. This PR adds `contractMigrationNotes[]` to `change-package/v2` as an optional field. Existing v2 consumers continue to validate because the field is additive. Producers that include the field must also update PR summary rendering tests. Rollback: omit `contractMigrationNotes[]` and keep the previous v2 payload shape.

Unacceptable migration note:

> Updated the schema.

The unacceptable note does not identify the contract family, compatibility impact, consumer action, validation evidence, or rollback path.

---

## 日本語

本ドキュメントは、`schema/*.schema.json` における JSON Schema 識別子 URI の運用方針を定義します。

### 1. canonical URI と hosted URI の役割

- canonical なスキーマ識別子（`$id`）: `https://ae-framework/schema/<file>`
- 配布・参照用 hosted URL（GitHub Pages）: `https://itdojp.github.io/ae-framework/schema/<file>`

新規追加または移行対象のスキーマは、`$id` に `https://ae-framework/schema/<file>` を使用します。  
`https://itdojp.github.io/ae-framework/schema/<file>` は、直接取得可能な公開 URL が必要な場面で利用します。

### 2. 現状実装スナップショット（as-is）

大半のスキーマは `https://ae-framework/schema/<file>` を採用しています。  
以下は互換性維持のため、現時点で GitHub Pages ベースの `$id` を保持します。

- `schema/codex-task-request.schema.json`
- `schema/codex-task-response.schema.json`
- `schema/quality-report.schema.json`
- `schema/verify-profile-summary.schema.json`

現在の preview metric 追加も canonical URI 方針に従います。`schema/req2run-metrics.schema.json` は adoption-readiness evidence 向けの report-only `req2run-metrics/v1` artifact を識別し、`scripts/ci/validate-json.mjs` で検証します。blocking policy-gate 条件は追加しません。

### 3. 契約ライフサイクル状態

Assurance 関連の schema / artifact 契約は、次の lifecycle state で管理します。これらは documentation / release governance 上のラベルであり、それ自体は CI enforcement を変更しません。

| 状態 | 意味 | Producer / consumer ルール | 昇格または削除条件 |
| --- | --- | --- | --- |
| `stable` | 対象スコープで production / release evidence の既定契約。 | producer は既定で出力可能。consumer は opt-in flag なしで依存可能。 | 破壊的変更には、新しい versioned contract、migration note、consumer-impact assessment、互換期間が必要。 |
| `preview` | early adoption、report-only、dual-write validation 向けに実装済み。 | producer は opt-in、dual-write、または明示された preview command で出力可能。consumer は欠落を許容する。 | fixture coverage、contract validation、summary rendering、consumer-path test が揃った後にのみ stable 昇格可能。 |
| `deprecated` | replacement があり、互換期間中のみサポートする契約。 | producer / consumer は deprecation window 中は読み書き可能。新規作業は replacement へリンクする。 | replacement adoption evidence、rollback guidance、retirement issue が揃った後に削除可能。 |
| `legacy-compatible` | workflow、script、document、operator path のいずれかがまだ消費するため保持する互換導線。 | validation または adapter behavior を安定させ、canonical replacement を明記する。 | consumer-path test が canonical route で挙動を覆うことを証明した後にのみ `deprecated` / `removed` へ再分類可能。 |
| `removed` | 現行 producer / consumer でサポートしない契約または導線。 | 新規 artifact をこの形で出力しない。可能な場合、consumer は明示的な migration guidance とともに失敗する。 | 事前 deprecation evidence、または security / correctness 例外の文書化が必要。 |

Preview から stable への昇格には、同一 PR または linked issue で次の証跡が必要です。

- 昇格対象 contract の schema / fixture validation;
- contract catalog と canonical route の更新;
- 昇格 route の producer / consumer tests;
- non-green、waived、partial、migration 関連 state を持つ場合の PR/release summary behavior;
- 既存 route を置き換える場合の migration note と rollback guidance。

### 4. Anti-pattern（禁止）

`$id` / `$ref` に GitHub リポジトリ URL を直接使わないこと。

- `https://github.com/itdojp/ae-framework/.../schema/<file>`
- `https://raw.githubusercontent.com/itdojp/ae-framework/.../schema/<file>`

これらはブランチやパスに依存し、安定識別子として不適切です。

### 5. この方針の変更理由

- スキーマ識別子と配布基盤を分離し、運用変更に強くするため。
- 既存利用者が参照する legacy `$id` 互換性を維持するため。
- GitHub URL への暗黙依存を排除し、識別子の安定性を担保するため。

### 6. 運用ルール

- URI の `<file>` は `schema/` 配下の実ファイル名と一致させる。
- 公開済みスキーマの `$id` 変更は互換性影響ありとして扱い、`docs/project/RELEASE.md` の手順に従う。
- `schema/*.schema.json` は `$id` 定義を必須とする。

### 7. レビュー観点

- `$id` が canonical/例外ルールに準拠しているか。
- `$id` / `$ref` に `github.com` / `raw.githubusercontent.com` が混入していないか。
- `$id` 変更時に互換性評価が実施されているか。
- 関連ドキュメント・fixtures の更新が揃っているか。

### 8. CI観点

- `schema/**` の変更は `.github/workflows/spec-validation.yml` のトリガー対象。
- Assurance contract governance marker は `pnpm -s run check:assurance-contract-governance` でローカル確認できます。この check は決定的な documentation / schema consistency support であり、コード正しさの証明ではありません。
- スキーマ/成果物検証は次で実行される。
  - `.github/workflows/validate-artifacts-ajv.yml`
  - `.github/workflows/verify-lite.yml`
  - `.github/workflows/minimal-pipeline.yml`
- ドキュメント整合は `pnpm docs:lint` で確認する。

### 9. ペイロード版管理（`schemaVersion` / `contractId`）

- `schemaVersion` はペイロード互換性の識別子、`$id` / `$schema` はスキーマ識別子です。役割を分離して扱います。
- 現行実装で許容される形式:
  - semver（`1.0.0`）: 既存で semantic versioning を採用している契約系列
  - 契約識別子型（`<contract>/v1`）: major 系列を `const` で固定する契約系列
- `contractId` は契約系列の安定識別子（例: `pr-state.v1`, `execution-plan.v1`）であり、存在する場合は schema 側で `const` 固定します。
- 新規の機械可読成果物は、互換境界キー（`schemaVersion` または `contractId`）を最低1つ持つこと。長期消費される成果物は両方を持つことを推奨します。
- 同一契約系列内で版表現を混在させないこと。移行時は dual-read 互換期間を明示します。
- リリースノートや移行注記では、契約系列が採用している版表現で互換境界を説明します。release 手順のためだけに contract-style 系列を semver へ変換しないでください。

### 10. dual-write / dual-validate 運用ルール

- 互換性破壊を伴う変更では、既存契約を上書き変更しません。
- 移行は次の段階で実施します。
  1. **dual-write**: producer が旧/新ペイロードを並行出力
  2. **dual-validate**: CI で旧/新の両方を対応 schema で検証
  3. **cutover**: consumer の既定読取を新契約へ切替
  4. **retire**: 互換期間終了後に旧契約を廃止
- dual 期間では以下を必ず定義します。
  - canonical payload（旧/新どちらを正とするか）
  - 開始/終了条件（追跡Issue）
  - ロールバック手順と feature flag 戦略
  - 必須 fixture / test 更新

### 11. 互換性破壊チェックリスト（schema契約）

- 破壊的変更の例:
  - required フィールドの削除/改名
  - 型変更、enum/pattern の非互換な狭小化
  - 互換アダプタなしの意味変更
  - `$id` / `schemaVersion` / `contractId` の互換境界変更
- 同一PRで必須とする更新:
  - 新版 schema と fixture の追加更新
  - dual-read または移行アダプタの更新
  - CI検証更新（必要に応じて `scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`）
  - リリースノートと移行注記（`docs/project/RELEASE.md`）
  - 契約カタログ更新（`docs/reference/CONTRACT-CATALOG.md`）

### 12. 移行注記例

適切な migration note:

> `claim-level-summary/v1` は preview のまま維持します。この PR は `change-package/v2` に optional な `contractMigrationNotes[]` を追加します。追加フィールドなので既存 v2 consumer は引き続き validation 可能です。このフィールドを出力する producer は、PR summary rendering tests も更新する必要があります。Rollback: `contractMigrationNotes[]` を省略し、従来の v2 payload shape を維持します。

不適切な migration note:

> schema を更新しました。

不適切な例は、contract family、互換性影響、consumer action、validation evidence、rollback path を示していません。

### 13. Re-evaluation 3 quality baseline schema

`schema/quality-baseline.schema.json` uses the canonical `$id` form `https://ae-framework/schema/quality-baseline.schema.json`. It is an evidence contract for `artifacts/quality/code-quality-baseline.json` and remains report-only until a later policy change explicitly promotes any metric to enforcement.

### 14. Re-evaluation 3 variance report schema

`schema/variance-report.schema.json` uses the canonical `$id` form `https://ae-framework/schema/variance-report.schema.json`. It is an evidence contract for `artifacts/quality/variance-report.json`; findings remain report-only until a later policy change explicitly promotes a variance category to enforcement.

### 15. Spec Kit bridge report schema

`schema/spec-kit-bridge-report.schema.json` uses the canonical `$id` form `https://ae-framework/schema/spec-kit-bridge-report.schema.json`. It is an evidence contract for `artifacts/spec-kit/spec-kit-bridge-report.json`, produced by `scripts/spec-kit/import-feature.mjs`. Findings remain report-only; `warning` identifies missing or ambiguous Spec Kit mappings without failing ordinary usage.

### 16. Loop run input and summary schemas

`schema/loop-run-input.schema.json` uses the canonical `$id` form `https://ae-framework/schema/loop-run-input.schema.json`. It is the preview input contract for fixture-backed report-only loop runs and captures Issue intent, ExecPlan v2 references, Context Pack references, safety flags, validation commands, observed evidence links, findings, and per-iteration decisions.

`schema/loop-run-summary.schema.json` uses the canonical `$id` form `https://ae-framework/schema/loop-run-summary.schema.json`. It is a preview/report-only evidence contract for `artifacts/loop/loop-run-summary.json`, produced by `scripts/loop/run-report-only.mjs`. `stopReason` records operator-facing loop termination such as `success`, `blocked`, `max-iterations`, `validation-failed`, `unsafe-action`, or `human-required`; the contract does not grant merge, approval, push, or hosted-LLM authority. Current runner output includes policy, observability, and replay evidence, while the v1 schema keeps those sections optional so earlier stored v1 summaries can still validate during migration.

### 17. Loop policy schema

`schema/loop-policy.schema.json` uses the canonical `$id` form `https://ae-framework/schema/loop-policy.schema.json`. It is the preview/report-only policy contract for loop safety budgets and stop rules. The contract captures iteration / wall-clock / modified-file budgets, command and path allow/deny lists, required evidence IDs, high-risk approval thresholds, repeated-failure limits, and redaction posture. Policy findings remain report-only in this slice; no blocking policy-gate rule is added unless a future promotion issue explicitly changes that behavior.

### 18. Domain assurance preset schema

`schema/domain-assurance-preset.schema.json` uses the canonical `$id` form `https://ae-framework/schema/domain-assurance-preset.schema.json`. It is the report-only template contract for `templates/domain-presets/*/preset.json`. Presets select product-archetype inputs, starting commands, expected artifacts, evidence surfaces, and escalation rules, but they do not approve PRs, bypass Context Pack / ExecPlan, or add policy-gate enforcement.

`schema/domain-assurance-preset-report.schema.json` uses the canonical `$id` form `https://ae-framework/schema/domain-assurance-preset-report.schema.json`. It validates deterministic rendered examples under `fixtures/domain-presets/*/expected/`, produced by `scripts/domain-presets/render-preset.mjs`, so preset onboarding evidence can be reviewed without live external API calls.
