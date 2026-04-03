---
docRole: derived
canonicalSource:
- docs/quality/ASSURANCE-MODEL.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-04-04'
---
# Assurance Lanes

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document fixes the meaning of `requiredLanes` from `assurance-profile/v1` across implementation, CI, and artifacts.

It defines:
- canonical validation lanes
- the minimum independence rule
- provenance minimum expectations
- the counterexample linkage convention

Detailed achieved-level judgement remains a later phase. Default operation stays report-only. The strict assurance enforcement step becomes active only when the `enforce-assurance` label is present.

### 2. Canonical validation lanes

| lane | Primary question | Representative producer | Representative artifact / report |
| --- | --- | --- | --- |
| `spec` | Is the specification itself structurally sound? | `scripts/context-pack/validate.mjs`, `scripts/context-pack/verify-functor.mjs`, `scripts/context-pack/verify-natural-transformation.mjs`, `scripts/context-pack/verify-product-coproduct.mjs`, `scripts/context-pack/verify-phase5-templates.mjs` | `artifacts/context-pack/*.json` |
| `behavior` | Does the implementation exhibit the expected behavior? | unit / integration / property / MBT harness | test summary, property result, MBT result |
| `adversarial` | Does the claim survive counterexamples or destructive conditions? | mutation, fuzz, differential, counterexample replay | mutation summary, counterexample artifacts |
| `model` | Is the system still coherent from a state-machine / model / rule-system viewpoint? | conformance, TLA, Alloy, SMT, CSP, SPIN | `formal-summary`, conformance report |
| `proof` | Has the system reached machine-checked proof or equivalence? | Lean, Kani, equivalence proof | `formal-summary` proof entries |
| `runtime` | Can runtime guards, monitors, and alerts contain residual risk? | runtime conformance, rollout guard, monitor/alert config | runtime conformance summary, runtime control manifests |

### 3. Independence rule

### 3.1 Minimum rule

The Phase 1/2 minimum independence rule uses coarse source categories instead of full lineage proof.

- `spec-derived`
- `source-derived`
- `model-derived`
- `runtime-derived`
- `manual`

`minIndependentSources` per claim is evaluated by counting observed evidence `sourceKind` categories.

### 3.2 Default values

- If `claims[].minIndependentSources` is explicitly set, that value wins.
- Otherwise:
  - `critical` / `high`: `2`
  - `medium` / `low`: `1`

### 3.3 Initial warnings

`verify:assurance` currently treats at least the following as warnings:

- `all-evidence-derived-from-source`
- `same-generator-lineage`
- `missing-spec-derived-evidence`
- `unresolved-critical-counterexample`
- `insufficient-independent-lanes`

### 4. Provenance minimum

The current artifact metadata contract is defined in `schema/artifact-metadata.schema.json`.

Currently enforced baseline fields:
- `generatedAtUtc`
- `generatedAtLocal`
- `timezoneOffset`
- `gitCommit`
- `branch`
- `runner`
- `toolVersions`

The assurance aggregation model is expected to grow additional provenance detail later, including:
- which inputs an artifact was derived from
- whether it is `source-derived`, `spec-derived`, `model-derived`, or `runtime-derived`
- lineage such as model, prompt, seed, or replay command

Those remain documentation rules for now. Schema enforcement is deferred.

### 5. Counterexample linkage convention

`schema/counterexample.schema.json` keeps its core shape and can include optional fields used by assurance linkage.

- `claimIds`
- `morphismIds`
- `triageStatus`
- `replayCommand`
- `suggestedContextChanges`

Meaning:
- `claimIds`: which claim the counterexample broke
- `morphismIds`: which Context Pack morphism is involved
- `triageStatus`: `open | resolved | accepted-risk`
- `replayCommand`: command used for local replay
- `suggestedContextChanges`: return path to Context Pack / docs / patch hints

`change-package-v2` already contains `counterexamples[].claimIds`, so it currently serves as the bridge for counterexample linkage.

### 6. Current implementation boundary

Implemented on `main`:
- `assurance-profile/v1`
- optional `assurance.profile` / `claim_refs` in Context Pack
- claim / counterexample linkage in `change-package-v2`
- report-only `verify:assurance` summary generation
- report-only assurance aggregation and artifact upload in `verify-lite.yml`
- strict assurance enforcement under the `enforce-assurance` label
- assurance display in PR summary, release summary, and post-deploy summary

Deferred or incomplete:
- automatic claim-level linkage resolution for every producer
- rigorous lineage proof

### 7. Related references

- `docs/quality/ASSURANCE-MODEL.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-operations-runbook.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/guides/COUNTEREXAMPLE-SCHEMA.md`
- `docs/spec/context-pack.md`
- `docs/reference/CONTRACT-CATALOG.md`

---


## 日本語

### 1. 目的

`assurance-profile/v1` が要求する `requiredLanes` を、実装・CI・成果物の間で同じ意味に固定するための基準文書です。

この文書では次を定義します。
- 正規の検証レーン
- 最小の独立性ルール
- provenance の最小期待値
- 反例リンク規約

詳細な達成レベル（achieved level）判定は後続フェーズで追加します。既定運用は報告専用（report-only）ですが、`enforce-assurance` ラベル時は strict assurance enforcement ステップを有効化します。

### 2. 正規の検証レーン

| レーン | 主な問い | 代表的な生成主体 | 代表的な成果物 / レポート |
| --- | --- | --- | --- |
| `spec` | 仕様記述そのものが壊れていないか | `scripts/context-pack/validate.mjs`, `scripts/context-pack/verify-functor.mjs`, `scripts/context-pack/verify-natural-transformation.mjs`, `scripts/context-pack/verify-product-coproduct.mjs`, `scripts/context-pack/verify-phase5-templates.mjs` | `artifacts/context-pack/*.json` |
| `behavior` | 実装が期待した振る舞いを示すか | unit / integration / property / MBT harness | test summary, property result, MBT result |
| `adversarial` | 反例探索や破壊的条件でクレーム（claim）が崩れないか | mutation, fuzz, differential, counterexample replay | mutation summary, counterexample artifacts |
| `model` | 状態機械・モデル・規則系の観点で矛盾しないか | conformance, TLA, Alloy, SMT, CSP, SPIN | `formal-summary`, conformance report |
| `proof` | 機械的 proof / equivalence まで到達しているか | Lean, Kani, equivalence proof | `formal-summary` proof entries |
| `runtime` | 運用中の guard / monitor / alert で残余リスクを抑制できるか | runtime conformance, rollout guard, monitor/alert config | runtime conformance summary, runtime control manifests |

### 3. 独立性ルール

### 3.1 最小ルール

Phase 1/2 の最小独立性ルールは、完全な lineage 証明ではなく、次の粗い分類を用います。

- `spec-derived`
- `source-derived`
- `model-derived`
- `runtime-derived`
- `manual`

クレーム（claim）ごとの `minIndependentSources` は、観測された証跡（evidence）の `sourceKind` 種別数で判定します。

### 3.2 既定値

- `claims[].minIndependentSources` が明示されていればその値を優先
- 未指定の場合:
  - `critical` / `high`: `2`
  - `medium` / `low`: `1`

### 3.3 初期 warning

`verify:assurance` は少なくとも次を warning として扱います。

- `all-evidence-derived-from-source`
- `same-generator-lineage`
- `missing-spec-derived-evidence`
- `unresolved-critical-counterexample`
- `insufficient-independent-lanes`

### 4. Provenance の最小期待値

現行の成果物メタデータ契約は `schema/artifact-metadata.schema.json` で定義されています。

現在 enforcement 対象の主項目:
- `generatedAtUtc`
- `generatedAtLocal`
- `timezoneOffset`
- `gitCommit`
- `branch`
- `runner`
- `toolVersions`

assurance aggregation では、これに加えて次の provenance を将来拡張対象として扱います。

- どの入力から導出されたか
- `source-derived` / `spec-derived` / `model-derived` / `runtime-derived`
- model / prompt / seed / replay command などの lineage

これらは現時点では文書上のルールであり、schema enforcement は後続です。

### 5. 反例リンク規約

`schema/counterexample.schema.json` は基本 shape を維持しつつ、assurance linkage 用の任意 field を持てます。

- `claimIds`
- `morphismIds`
- `triageStatus`
- `replayCommand`
- `suggestedContextChanges`

意味:
- `claimIds`: どのクレーム（claim）を崩した反例か
- `morphismIds`: どの Context Pack morphism に関係するか
- `triageStatus`: `open | resolved | accepted-risk`
- `replayCommand`: 再実行コマンド
- `suggestedContextChanges`: Context Pack / docs / patch hint への戻し先

`change-package-v2` は既に `counterexamples[].claimIds` を持つため、当面の運用では counterexample linkage の橋渡しとして利用できます。

### 6. 現在の実装境界

main で実装済み:
- `assurance-profile/v1`
- Context Pack の optional `assurance.profile` / `claim_refs`
- `change-package-v2` の claim/counterexample linkage
- report-only `verify:assurance` summary 生成
- `verify-lite.yml` での report-only assurance summary 集約と artifact upload
- `enforce-assurance` ラベル時の strict assurance enforcement
- PR summary / release summary / post-deploy summary への assurance 表示

未実装または後続:
- 全 producer の claim-level linkage 自動解決
- lineage の厳密証明

### 7. 関連資料

- `docs/quality/ASSURANCE-MODEL.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-operations-runbook.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/guides/COUNTEREXAMPLE-SCHEMA.md`
- `docs/spec/context-pack.md`
- `docs/reference/CONTRACT-CATALOG.md`
