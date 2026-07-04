---
docRole: derived
canonicalSource:
- schema/assurance-profile.schema.json
- docs/quality/ASSURANCE-MODEL.md
lastVerified: '2026-07-04'
---
# Assurance Profile v1

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

`assurance-profile/v1` is the input contract that binds business claims to machine-readable assurance requirements.

It records:
- target assurance level
- required validation lanes
- required evidence kinds
- Context Pack references for objects, morphisms, diagrams, and acceptance tests

Current implementation covers schema validation, documentation, `verify:assurance` summary generation, Verify Lite collection of assurance summary artifacts, and strict assurance enforcement when the `enforce-assurance` label is present. Default PR behavior remains report-only. Strict mode is label-gated.

### 2. Schema

- Schema: `schema/assurance-profile.schema.json`
- Sample fixture: `fixtures/assurance/sample.assurance-profile.json`
- Context Pack reference point: optional `assurance` section in `schema/context-pack-v1.schema.json`
- Deploy-time profile contracts: `profiles/minimal.yaml`, `profiles/standard.yaml`, and
  `profiles/full.yaml`

Minimal shape:

```json
{
  "schemaVersion": "assurance-profile/v1",
  "profileId": "inventory-baseline-v1",
  "scope": {
    "contextPackSources": ["spec/context-pack/**/*.{yml,yaml,json}"],
    "componentGlobs": ["src/domain/inventory/**"]
  },
  "claims": [
    {
      "id": "no-negative-stock",
      "statement": "Inventory stock never becomes negative after an accepted reservation.",
      "kind": "safety",
      "criticality": "high",
      "targetLevel": "A2",
      "minIndependentSources": 2,
      "requiredLanes": ["spec", "behavior", "model"],
      "requiredEvidenceKinds": ["property", "product-coproduct", "counterexample-closed"]
    }
  ]
}
```

### 2.1 Deploy-time adoption profile metadata

Issue #3598 introduces deploy-time adoption profiles without changing current CI
behavior. The existing `assurance-profile/v1` contract now accepts an optional
`deployment` object so repository-level profiles can be used as a single source
of truth by later CLI and GitHub Action work.

The checked-in profile contracts are:

| File | README profile | Intent |
| --- | --- | --- |
| `profiles/minimal.yaml` | Baseline | Artifact schema validation, assurance summary aggregation, declarative YAML policy gate, and PR review surface. |
| `profiles/standard.yaml` | Structured assurance | `minimal` plus Context Pack, property/MBT/conformance, and traceability lanes. |
| `profiles/full.yaml` | High-assurance critical core | `standard` plus formal/model/proof lanes, mutation, and heavy-test trend signals. |

Each deploy-time profile declares:

- `deployment.artifactSchemas`: required artifact schemas for the profile.
- `deployment.activeLanes`: active validation or review lanes.
- `deployment.gatePolicy`: policy evaluator and source policy file.
- `deployment.requiredChecks`: CI check contexts expected for that profile. Phase 0
  validates these against the current branch-protection baseline: `verify-lite`,
  `policy-gate`, and `gate`.

Custom profiles use the same schema with `deployment.tier: custom`.

Validate the contracts with:

```bash
pnpm run profiles:validate
```

Phase 0 is contract-only. It does not switch existing workflows to profile-driven
execution; later phases consume these files from `@ae-framework/core`, the
composite action, and internal dogfooding paths.

### 3. Provisional assurance level semantics

| Level | Meaning | Typical evidence |
| --- | --- | --- |
| `A0` | Minimum integrity where contract, lint, and build still hold | schema, lint, type, build |
| `A1` | Sample-level confirmation through unit/integration/property checks | unit, integration, property |
| `A2` | Structural specification validation is in place | product-coproduct, natural-transformation, conformance |
| `A3` | Critical claims are closed through counterexample search or model checking | model-check, counterexample-closed |
| `A4` | Proof-carrying assurance is available | proof |

This table is still the Phase 1/2 provisional definition. `verify:assurance` aggregates lanes, evidence, and warnings, but does not make a strict certification decision.
`claim-evidence-manifest/v1` adds a report-only achieved-level summary for PR review: explicit `change-package/v2.assurance.achievedLevel` is used as an input when available, but the displayed achieved level may still be conservatively adjusted for consistency with claim `status` and `targetLevel`. For assurance-summary-only claims, the generator uses a conservative display mapping (`satisfied` => `targetLevel`; non-satisfied statuses => one level below `targetLevel`, capped at `A0`). This mapping is not a strict policy gate.

### 4. Claim design guidance

1. A claim should describe business correctness, not an implementation tactic.
2. `criticality` is recorded as one of `low`, `medium`, `high`, or `critical`.
3. `requiredLanes` should represent independent viewpoints rather than multiple tests of the same kind.
4. `requiredEvidenceKinds` should make explicit what evidence is needed to explain the claim.
5. `scopeRefs` should stay linked to Context Pack IDs so the contract keeps traceability to specification fragments.

### 4.1 `requiredLanes` and `minIndependentSources`

- `requiredLanes` is about independence of viewpoints, not test count.
- `minIndependentSources` is the minimum independence rule consumed by `verify:assurance`.
- Default when omitted:
  - `critical` / `high`: `2`
  - `medium` / `low`: `1`

Examples:
- A claim requiring `spec + behavior + model` expects at least two distinct evidence lineages across specification, implementation, and model viewpoints.
- Adding more `behavior` evidence alone does not clear the independence warning if every artifact is still `source-derived`.

### 5. Coupling with Context Pack v1

Context Pack can include an optional `assurance` section.

```yaml
assurance:
  profile: inventory-baseline-v1
  claim_refs:
    - no-negative-stock
```

Purpose:
- declare which assurance profile a Context Pack refers to
- indirectly link morphisms, diagrams, and acceptance tests to claims
- preserve existing behavior in repositories that do not adopt assurance yet by omitting the section

### 6. Current non-goals

- writing `achievedLevel` back into `verify-lite-run-summary`
- letting `policy-gate` directly interpret assurance artifacts for blocking decisions
- adding assurance judgements into `policy-input` / `policy-decision`
- formal proof coverage for every claim
- blocking PRs by default when no assurance profile is configured

Notes:
- The strict step is `Enforce assurance summary (strict; label-gated)` in `verify-lite.yml`.
- Standard PRs without the `enforce-assurance` label keep assurance summary in report-only mode.

### 7. Change management notes

- If you add a new claim kind or evidence kind, update `schema/assurance-profile.schema.json` and this document in the same PR.
- If a new schema is introduced, update `docs/reference/CONTRACT-CATALOG.md` in the same change.
- If the sample fixture changes, update `tests/contracts/assurance-profile-contract.test.ts`.
- Lane taxonomy remains SSOT in `docs/quality/assurance-lanes.md`; this document only describes how the input contract connects to that taxonomy.
- For execution flow and strict/report-only operations, follow `docs/quality/assurance-operations-runbook.md`.

---


## 日本語

### 1. 目的

`assurance-profile/v1` は、業務上のクレーム（claim）を次の要素に機械可読で結び付けるための入力契約です。

- 目標保証レベル（target assurance level）
- 必要な検証レーン（required validation lanes）
- 必要な証跡種別（required evidence kinds）
- Context Pack 上の object / morphism / diagram / acceptance test 参照

現時点では、**schema とドキュメント整備、`verify:assurance` による summary 生成、Verify Lite での assurance summary artifact 収集、および `enforce-assurance` ラベル時の strict assurance enforcement** までを実装済みとします。通常 PR は報告専用（report-only）のまま維持し、厳格化はラベル制御（label-gated）時のみ有効化します。

### 2. スキーマ

- スキーマ: `schema/assurance-profile.schema.json`
- サンプル fixture: `fixtures/assurance/sample.assurance-profile.json`
- Context Pack 側の参照先: `schema/context-pack-v1.schema.json` の optional `assurance`
- deploy-time profile contract: `profiles/minimal.yaml`、`profiles/standard.yaml`、`profiles/full.yaml`

最小構造:

```json
{
  "schemaVersion": "assurance-profile/v1",
  "profileId": "inventory-baseline-v1",
  "scope": {
    "contextPackSources": ["spec/context-pack/**/*.{yml,yaml,json}"],
    "componentGlobs": ["src/domain/inventory/**"]
  },
  "claims": [
    {
      "id": "no-negative-stock",
      "statement": "Inventory stock never becomes negative after an accepted reservation.",
      "kind": "safety",
      "criticality": "high",
      "targetLevel": "A2",
      "minIndependentSources": 2,
      "requiredLanes": ["spec", "behavior", "model"],
      "requiredEvidenceKinds": ["property", "product-coproduct", "counterexample-closed"]
    }
  ]
}
```

### 2.1 deploy-time adoption profile metadata

Issue #3598 では、現在の CI 挙動を変更せずに deploy-time adoption profile を導入します。
既存の `assurance-profile/v1` 契約に optional `deployment` object を追加し、
後続の CLI / GitHub Action が参照する単一の情報源として利用できるようにします。

チェックイン済みの profile contract は次の通りです。

| File | README profile | 目的 |
| --- | --- | --- |
| `profiles/minimal.yaml` | Baseline | artifact schema validation、assurance summary aggregation、declarative YAML policy gate、PR review surface。 |
| `profiles/standard.yaml` | Structured assurance | `minimal` に Context Pack、property/MBT/conformance、traceability lane を追加。 |
| `profiles/full.yaml` | High-assurance critical core | `standard` に formal/model/proof lane、mutation、heavy-test trend signal を追加。 |

各 deploy-time profile は次を宣言します。

- `deployment.artifactSchemas`: profile が要求する artifact schema。
- `deployment.activeLanes`: 有効化する validation / review lane。
- `deployment.gatePolicy`: policy evaluator と policy source。
- `deployment.requiredChecks`: profile が期待する CI check context。Phase 0 では現行の
  branch-protection baseline である `verify-lite`、`policy-gate`、`gate` と一致することを検証します。

Custom profile も同じ schema を使い、`deployment.tier: custom` として表現します。

Contract は次の command で検証します。

```bash
pnpm run profiles:validate
```

Phase 0 は contract-only です。既存 workflow を profile-driven 実行へ切り替えるものではありません。
後続 phase で `@ae-framework/core`、composite action、内部 dogfooding path がこれらの file を参照します。

### 3. assurance level の暫定的な意味

| Level | 意味 | 典型的な証跡（evidence） |
| --- | --- | --- |
| `A0` | 契約・lint・build が成立している最低限の整合性 | schema, lint, type, build |
| `A1` | unit/integration/property によりサンプル的に確認済み | unit, integration, property |
| `A2` | 構造的な仕様検証まで到達 | product-coproduct, natural-transformation, conformance |
| `A3` | 反例探索やモデル検査で critical claim を閉じている | model-check, counterexample-closed |
| `A4` | proof-carrying な厳密保証を持つ | proof |

この表は Phase 1/2 の暫定定義です。`verify:assurance` は lane / evidence / warning を集約しますが、厳密な certification 判定は行いません。
`claim-evidence-manifest/v1` は PR review 用の report-only な achieved-level summary を追加します。明示された `change-package/v2.assurance.achievedLevel` がある場合はそれを入力として優先的に利用しますが、最終的な表示値は `status` と `targetLevel` の整合性のため generator 側で必要に応じて保守的に調整されることがあります。assurance-summary のみの claim では、表示用の保守的な mapping（`satisfied` は `targetLevel`、非 satisfied status は `targetLevel` から 1 段階下げ、下限は `A0`）を使います。この mapping は strict policy gate ではありません。

### 4. クレーム（claim）の設計指針

1. クレーム（claim）は実装方針ではなく、業務上の正しさを述べる
2. `criticality` は low/medium/high/critical の 4 段階で記録する
3. `requiredLanes` は同じ誤解を共有しない観点で複数レーンを選ぶ
4. `requiredEvidenceKinds` は「何を集めればクレーム（claim）が説明できるか」を明示する
5. `scopeRefs` は Context Pack の ID にひも付け、仕様断片との対応を残す

### 4.1 `requiredLanes` と `minIndependentSources`

- `requiredLanes` は「何本テストがあるか」ではなく、「異なる観点からクレーム（claim）を叩いているか」を表します。
- `minIndependentSources` は `verify:assurance` が使う最小独立性ルール（independence rule）です。
- 未指定時の既定値:
  - `critical` / `high`: `2`
  - `medium` / `low`: `1`

例:
- `spec + behavior + model` を要求するクレーム（claim）は、仕様・実装・モデルの少なくとも 2 系統以上が観測されることを期待する
- `behavior` だけを増やしても、すべて `source-derived` なら independence warning は解消しない

### 5. Context Pack v1 との結合

Context Pack には任意の `assurance` セクションを追加できます。

```yaml
assurance:
  profile: inventory-baseline-v1
  claim_refs:
    - no-negative-stock
```

用途:
- どの Context Pack がどの assurance profile を参照するかを明示する
- morphism / diagram / acceptance test とクレーム（claim）を間接的に結ぶ
- assurance 未導入リポジトリでは、このセクションを省略して既存挙動を維持する

### 6. 現時点の非目標

- `verify-lite-run-summary` 自体へ achieved level を書き戻すこと
- `policy-gate` が assurance artifact 自体を直接解釈してブロッキング判定すること
- `policy-input` / `policy-decision` への assurance 判定追加
- 全クレーム（claim）の formal proof
- assurance 未設定 PR を既定でブロッキングにすること

補足:
- strict 化されるのは `verify-lite.yml` の `Enforce assurance summary (strict; label-gated)` ステップです。
- `enforce-assurance` ラベルを付けない通常 PR では、assurance summary は報告専用（report-only）のまま扱います。

### 7. 変更時の注意

- 新しい claim kind や evidence kind を追加する場合は、`schema/assurance-profile.schema.json` と本ドキュメントを同一 PR で更新する
- 新しい schema を追加した場合は、`docs/reference/CONTRACT-CATALOG.md` を同時に更新する
- sample fixture を変更する場合は `tests/contracts/assurance-profile-contract.test.ts` を更新する
- lane taxonomy は `docs/quality/assurance-lanes.md` を SSOT とし、本書では入力契約への接続だけを記述する
- 実行手順と strict / report-only の使い分けは `docs/quality/assurance-operations-runbook.md` を正とする
