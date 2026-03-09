# Assurance Lanes

> Language / 言語: English | 日本語

---

## English (Summary)

This document defines the canonical validation lanes for assurance claims in ae-framework.

Current scope:
- taxonomy of six lanes
- minimum independence rule
- minimum provenance rule
- counterexample linkage convention

CI enforcement remains report-only by default. `enforce-assurance` enables the strict assurance enforcement step for assurance-aware PRs.

---

## 日本語

## 1. 目的

`assurance-profile/v1` が要求する `requiredLanes` を、実装・CI・成果物の間で同じ意味に固定するための基準文書です。

この文書では次を定義します。
- canonical validation lanes
- 最小 independence rule
- provenance minimum
- counterexample linkage convention

詳細な achieved level 判定は後続フェーズで追加します。既定運用は report-only ですが、`enforce-assurance` ラベル時は assurance enforcement の strict 判定を有効化します。

## 2. Canonical validation lanes

| lane | 主な問い | 代表 producer | 代表 artifact / report |
| --- | --- | --- | --- |
| `spec` | 仕様記述そのものが壊れていないか | `scripts/context-pack/validate.mjs`, `verify-functor.mjs`, `verify-natural-transformation.mjs`, `verify-product-coproduct.mjs`, `verify-phase5-templates.mjs` | `artifacts/context-pack/*.json` |
| `behavior` | 実装が期待した振る舞いを示すか | unit / integration / property / MBT harness | test summary, property result, MBT result |
| `adversarial` | 反例探索や破壊的条件で claim が崩れないか | mutation, fuzz, differential, counterexample replay | mutation summary, counterexample artifacts |
| `model` | 状態機械・モデル・規則系の観点で矛盾しないか | conformance, TLA, Alloy, SMT, CSP, SPIN | `formal-summary`, conformance report |
| `proof` | 機械的 proof / equivalence まで到達しているか | Lean, Kani, equivalence proof | `formal-summary` proof entries |
| `runtime` | 運用中の guard / monitor / alert で残余リスクを抑制できるか | runtime conformance, rollout guard, monitor/alert config | runtime conformance summary, runtime control manifests |

## 3. Independence rule

### 3.1 最小ルール

Phase 1/2 の最小 independence rule は、完全な lineage 証明ではなく、次の粗い分類を用います。

- `spec-derived`
- `source-derived`
- `model-derived`
- `runtime-derived`
- `manual`

claim ごとの `minIndependentSources` は、観測された evidence の `sourceKind` 種別数で判定します。

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

## 4. Provenance minimum

現行の成果物メタデータ契約は `schema/artifact-metadata.schema.json` で定義されています。

現在 enforce している主項目:
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

これらは現時点では docs rule であり、schema enforcement は後続です。

## 5. Counterexample linkage convention

`schema/counterexample.schema.json` は core shape を維持しつつ、assurance linkage 用の optional field を持てます。

- `claimIds`
- `morphismIds`
- `triageStatus`
- `replayCommand`
- `suggestedContextChanges`

意味:
- `claimIds`: どの claim を崩した反例か
- `morphismIds`: どの Context Pack morphism に関係するか
- `triageStatus`: `open | resolved | accepted-risk`
- `replayCommand`: 再実行コマンド
- `suggestedContextChanges`: Context Pack / docs / patch hint への戻し先

`change-package-v2` は既に `counterexamples[].claimIds` を持つため、当面の運用では counterexample linkage の橋渡しとして利用できます。

## 6. Current implementation boundary

main 実装済み:
- `assurance-profile/v1`
- Context Pack の optional `assurance.profile` / `claim_refs`
- `change-package-v2` の claim/counterexample linkage
- report-only `verify:assurance` summary generation
- `verify-lite.yml` での report-only assurance summary 集約と artifact upload
- `enforce-assurance` ラベル時の strict assurance enforcement
- PR summary / release summary への assurance 表示

未実装または後続:
- 全 producer の claim-level linkage 自動解決
- lineage の厳密証明

## 7. 関連資料

- `docs/quality/ASSURANCE-MODEL.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-operations-runbook.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/guides/COUNTEREXAMPLE-SCHEMA.md`
- `docs/spec/context-pack.md`
- `docs/reference/CONTRACT-CATALOG.md`
