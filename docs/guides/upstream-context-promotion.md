---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/spec/discovery-pack.md
- docs/quality/assurance-profile.md
- docs/quality/issue-requirements-traceability.md
lastVerified: '2026-03-18'
---
# Upstream Context Promotion Guide

> Language / 言語: English | 日本語

---

## 日本語

このガイドは、Discovery Pack v1 を upstream input contract として整理し、Context Pack v1 を設計 SSOT として維持したまま、昇格規律を generic に固定するための実行ガイドです。

### 目的
- upstream input を `fixtures/discovery-pack/` で generic に整理する
- `approved` のみを compile / promotion の既定対象にする
- Context Pack 上で upstream trace を失わずに保持する
- As-Is / To-Be の差分を `natural transformation` / `product-coproduct` / `boundary map` で証跡化する
- assurance summary と issue traceability strict validate まで接続する

### 前提
- Node.js: `>=20.11 <23`
- pnpm: repository pinned version `10.0.0` (`packageManager`)
- 実行場所: repository root
- Discovery Pack は upstream input contract、Context Pack は design SSOT とする

### 1. 役割分担
- Discovery Pack
  - upstream source の整理
  - actor / goal / requirement / business use case / flow / decision の棚卸し
  - compile の既定対象は `approved` のみ
- Context Pack
  - authoritative な design SSOT
  - `upstream.discovery_pack` と `upstream_refs` で upstream trace を残す
  - `reviewed` / `hypothesis` / `deferred` は explicit override なしに authoritative promotion しない

### 2. upstream trace の書き方
Context Pack では pack-level と element-level の両方で Discovery Pack との対応を固定します。

```yaml
upstream:
  discovery_pack:
    path: fixtures/discovery-pack/upstream-context-promotion-minimal.yaml
    profile: rdra-lite

morphisms:
  - id: MOR-NORMALIZE
    upstream_refs:
      goal_ids:
        - GOL-CANONICALIZE-INPUT
      requirement_ids:
        - DRQ-NORMALIZE-INPUT
      business_use_case_ids:
        - BUC-PROMOTE-APPROVED
      decision_ids:
        - DEC-NORMALIZE-TO-CANONICAL
```

### 3. map の使い分け
- `natural transformation`
  - As-Is / To-Be 間で意味保存を表現する
  - 変更後も期待振る舞いが壊れていないことを扱う
- `product-coproduct`
  - 複数 input variant を canonical representation に統合する
  - 入力キーの完全被覆と failure variant 被覆を扱う
- `boundary map`
  - actor / reviewer / system boundary / promotion authority を分離する
  - promotion 権限と input 提供権限が別境界であることを扱う

### 4. assurance と traceability への接続
- `assurance.profile` と `assurance.claim_refs` で、昇格規律に必要な claim を Context Pack に結び付ける
- `aggregate-lanes` は Context Pack claim refs と verify-lite / supplemental evidence を用いて assurance summary を生成する
- issue traceability は `REQ-UCP-*` を issue 本文から抽出し、Context Pack / Discovery Pack / tests / code を matrix に集約したうえで `ae validate --traceability --strict` まで実行する

### 5. generic minimal fixture の位置付け
`upstream-context-promotion-minimal` fixture 群は domain example ではありません。contract 実行確認用の最小構成です。

- Discovery Pack: `fixtures/discovery-pack/upstream-context-promotion-minimal.yaml`
- Context Pack: `fixtures/context-pack/upstream-context-promotion-minimal.yaml`
- map 群:
  - `fixtures/context-pack/upstream-context-promotion-minimal-natural-transformation.json`
  - `fixtures/context-pack/upstream-context-promotion-minimal-product-coproduct.json`
  - `fixtures/context-pack/upstream-context-promotion-minimal-boundary-map.json`
- assurance profile: `spec/assurance-profile/upstream-context-promotion-v1.json`

### 6. 実行手順
#### 6.1 Discovery Pack validate
```bash
pnpm exec ae discovery validate \
  --sources "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml" \
  --strict-approved
```

#### 6.2 Discovery Pack compile
```bash
pnpm exec ae discovery compile \
  --target plan-spec \
  --sources "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"

pnpm exec ae discovery compile \
  --target context-pack-scaffold \
  --sources "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.3 Context Pack validate
```bash
node scripts/context-pack/validate.mjs \
  --sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml" \
  --schema schema/context-pack-v1.schema.json \
  --discovery-pack "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"
```

Context Pack validate で確認する代表的な分岐:
- warning:
  - `upstream-refs-missing`
    - upstream validation 対象の `morphisms` / `acceptance_tests` に `upstream_refs` が無い
  - `discovery-pack-profile-mismatch`
    - `upstream.discovery_pack.profile` と Discovery Pack 実ファイルの `profile` が一致しない
  - `unmapped-approved-requirement`
  - `unmapped-approved-business-use-case`
- error:
  - `discovery-pack-source-missing`
    - `--discovery-pack` 未指定、または candidate path が解決できない
  - `discovery-pack-source-ambiguous`
    - `--discovery-pack` が複数ファイルに一致して 1 件へ特定できない
  - `upstream-ref-missing`
    - `upstream_refs` が Discovery Pack 内に存在しない ID を参照している

確認ファイル:
- `artifacts/context-pack/context-pack-validate-report.json`
- `artifacts/context-pack/context-pack-validate-report.md`

#### 6.4 Natural transformation verify
```bash
node scripts/context-pack/verify-natural-transformation.mjs \
  --map fixtures/context-pack/upstream-context-promotion-minimal-natural-transformation.json \
  --schema schema/context-pack-natural-transformation.schema.json \
  --context-pack-sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.5 Product / Coproduct verify
```bash
node scripts/context-pack/verify-product-coproduct.mjs \
  --map fixtures/context-pack/upstream-context-promotion-minimal-product-coproduct.json \
  --schema schema/context-pack-product-coproduct.schema.json \
  --context-pack-sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.6 Boundary map verify
```bash
node scripts/context-pack/verify-boundary-map.mjs \
  --map fixtures/context-pack/upstream-context-promotion-minimal-boundary-map.json \
  --schema schema/context-pack-boundary-map.schema.json \
  --context-pack-sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.7 Assurance aggregate
最小 aggregate は以下で生成できます。

```bash
node scripts/assurance/aggregate-lanes.mjs \
  --assurance-profile spec/assurance-profile/upstream-context-promotion-v1.json \
  --context-pack fixtures/context-pack/upstream-context-promotion-minimal.yaml \
  --output-json artifacts/assurance/upstream-context-promotion-minimal-summary.json \
  --output-md artifacts/assurance/upstream-context-promotion-minimal-summary.md
```

自然変換 / product-coproduct / boundary map を claim evidence として揃える場合は、verify-lite summary または evidence manifest を追加します。

```bash
node scripts/assurance/aggregate-lanes.mjs \
  --assurance-profile spec/assurance-profile/upstream-context-promotion-v1.json \
  --context-pack fixtures/context-pack/upstream-context-promotion-minimal.yaml \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --evidence-manifest fixtures/assurance/sample.assurance-evidence-manifest.json \
  --output-json artifacts/assurance/upstream-context-promotion-minimal-summary.json \
  --output-md artifacts/assurance/upstream-context-promotion-minimal-summary.md
```

#### 6.8 Issue traceability strict validate
```bash
ae traceability extract-ids \
  --issue "https://github.com/itdojp/ae-framework/issues/2732" \
  --pattern "REQ-UCP-[0-9]{3}" \
  --output docs/specs/upstream-context-promotion-issue-traceability-map.json

ae traceability matrix \
  --map docs/specs/upstream-context-promotion-issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --context-pack "fixtures/context-pack/upstream-context-promotion-minimal.yaml" \
  --discovery-pack "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml" \
  --format json \
  --output docs/specs/upstream-context-promotion-issue-traceability-matrix.json

ae validate --traceability --strict \
  --sources docs/specs/upstream-context-promotion-issue-traceability-matrix.json
```

### 7. current implementation の注意点
- `Context Pack validate` は upstream ref の存在整合を検証し、approved requirement / business use case の未マップを warning に集計します
- `Discovery Pack compile` の既定 include-status は `approved` のみです
- `verify-lite` では `artifacts/verify-lite/verify-lite-run-summary.json` の top-level `discoveryPack` に以下が集約されます
  - `mode`, `reason`, `validateStatus`, `compileStatus`
  - `blockingOpenQuestions`
  - `orphanApprovedRequirements`
  - `orphanApprovedBusinessUseCases`
  - `compileSelectedCount`
  - `compileExcludedByStatusCount`
  - `compileSkippedByTargetCount`
- report-only 既定では warning/error を観測しつつ PR を block しません。`enforce-discovery` ラベル時のみ strict 判定に昇格します
- `formal/summary.json` は legacy compatibility path であり、このガイドの主対象ではありません

### 8. 参照
- `docs/spec/discovery-pack.md`
- `docs/spec/context-pack.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/issue-requirements-traceability.md`


## English

This guide explains how to keep Discovery Pack v1 as the upstream input contract while preserving Context Pack v1 as the design SSOT and making promotion discipline generic.

### Purpose
- organize upstream input generically under `fixtures/discovery-pack/`
- promote only `approved` entries by default during compile / promotion
- retain upstream trace on the Context Pack side
- record As-Is / To-Be deltas through `natural transformation`, `product-coproduct`, and `boundary map`
- connect the result to assurance summary generation and issue traceability strict validation

### Preconditions
- Node.js: `>=20.11 <23`
- pnpm: repository pinned version `10.0.0` (`packageManager`)
- run from the repository root
- treat Discovery Pack as the upstream input contract and Context Pack as the design SSOT

### 1. Responsibility split
- Discovery Pack
  - organizes upstream source material
  - inventories actors / goals / requirements / business use cases / flows / decisions
  - compiles only `approved` entries by default
- Context Pack
  - remains the authoritative design SSOT
  - keeps upstream trace through `upstream.discovery_pack` and `upstream_refs`
  - does not promote `reviewed` / `hypothesis` / `deferred` into authoritative design without an explicit override

### 2. Writing upstream trace
Keep the Discovery Pack linkage at both the pack level and the element level.

```yaml
upstream:
  discovery_pack:
    path: fixtures/discovery-pack/upstream-context-promotion-minimal.yaml
    profile: rdra-lite

morphisms:
  - id: MOR-NORMALIZE
    upstream_refs:
      goal_ids:
        - GOL-CANONICALIZE-INPUT
      requirement_ids:
        - DRQ-NORMALIZE-INPUT
      business_use_case_ids:
        - BUC-PROMOTE-APPROVED
      decision_ids:
        - DEC-NORMALIZE-TO-CANONICAL
```

### 3. Choosing the right map
- `natural transformation`
  - represents semantics preservation between As-Is and To-Be
  - answers whether expected behavior still holds after the change
- `product-coproduct`
  - merges multiple input variants into a canonical representation
  - covers complete input-key coverage and failure-variant coverage
- `boundary map`
  - separates actor / reviewer / system boundary / promotion authority
  - proves that promotion authority and input-authoring authority are separated

### 4. Connecting to assurance and traceability
- use `assurance.profile` and `assurance.claim_refs` to bind promotion-discipline claims to the Context Pack
- `aggregate-lanes` reads Context Pack claim refs together with verify-lite / supplemental evidence to generate assurance summary artifacts
- issue traceability extracts `REQ-UCP-*` from the issue body, aggregates Context Pack / Discovery Pack / tests / code into a matrix, and then runs `ae validate --traceability --strict`

### 5. Role of the generic minimal fixture
The `upstream-context-promotion-minimal` fixture set is not a domain example. It is the minimum contract fixture for execution confirmation.

- Discovery Pack: `fixtures/discovery-pack/upstream-context-promotion-minimal.yaml`
- Context Pack: `fixtures/context-pack/upstream-context-promotion-minimal.yaml`
- map set:
  - `fixtures/context-pack/upstream-context-promotion-minimal-natural-transformation.json`
  - `fixtures/context-pack/upstream-context-promotion-minimal-product-coproduct.json`
  - `fixtures/context-pack/upstream-context-promotion-minimal-boundary-map.json`
- assurance profile: `spec/assurance-profile/upstream-context-promotion-v1.json`

### 6. Execution flow
#### 6.1 Discovery Pack validate
```bash
pnpm exec ae discovery validate   --sources "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"   --strict-approved
```

#### 6.2 Discovery Pack compile
```bash
pnpm exec ae discovery compile   --target plan-spec   --sources "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"

pnpm exec ae discovery compile   --target context-pack-scaffold   --sources "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.3 Context Pack validate
```bash
node scripts/context-pack/validate.mjs   --sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml"   --schema schema/context-pack-v1.schema.json   --discovery-pack "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"
```

Representative branches to watch in Context Pack validate:
- warning:
  - `upstream-refs-missing`
  - `discovery-pack-profile-mismatch`
  - `unmapped-approved-requirement`
  - `unmapped-approved-business-use-case`
- error:
  - `discovery-pack-source-missing`
  - `discovery-pack-source-ambiguous`
  - `upstream-ref-missing`

Primary reports:
- `artifacts/context-pack/context-pack-validate-report.json`
- `artifacts/context-pack/context-pack-validate-report.md`

#### 6.4 Natural transformation verify
```bash
node scripts/context-pack/verify-natural-transformation.mjs   --map fixtures/context-pack/upstream-context-promotion-minimal-natural-transformation.json   --schema schema/context-pack-natural-transformation.schema.json   --context-pack-sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.5 Product / Coproduct verify
```bash
node scripts/context-pack/verify-product-coproduct.mjs   --map fixtures/context-pack/upstream-context-promotion-minimal-product-coproduct.json   --schema schema/context-pack-product-coproduct.schema.json   --context-pack-sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.6 Boundary map verify
```bash
node scripts/context-pack/verify-boundary-map.mjs   --map fixtures/context-pack/upstream-context-promotion-minimal-boundary-map.json   --schema schema/context-pack-boundary-map.schema.json   --context-pack-sources "fixtures/context-pack/upstream-context-promotion-minimal.yaml"
```

#### 6.7 Assurance aggregate
The smallest aggregate can be produced with:

```bash
node scripts/assurance/aggregate-lanes.mjs   --assurance-profile spec/assurance-profile/upstream-context-promotion-v1.json   --context-pack fixtures/context-pack/upstream-context-promotion-minimal.yaml   --output-json artifacts/assurance/upstream-context-promotion-minimal-summary.json   --output-md artifacts/assurance/upstream-context-promotion-minimal-summary.md
```

If you want natural transformation / product-coproduct / boundary map to participate as claim evidence, add verify-lite summary or an evidence manifest:

```bash
node scripts/assurance/aggregate-lanes.mjs   --assurance-profile spec/assurance-profile/upstream-context-promotion-v1.json   --context-pack fixtures/context-pack/upstream-context-promotion-minimal.yaml   --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json   --evidence-manifest fixtures/assurance/sample.assurance-evidence-manifest.json   --output-json artifacts/assurance/upstream-context-promotion-minimal-summary.json   --output-md artifacts/assurance/upstream-context-promotion-minimal-summary.md
```

#### 6.8 Issue traceability strict validate
```bash
ae traceability extract-ids   --issue "https://github.com/itdojp/ae-framework/issues/2732"   --pattern "REQ-UCP-[0-9]{3}"   --output docs/specs/upstream-context-promotion-issue-traceability-map.json

ae traceability matrix   --map docs/specs/upstream-context-promotion-issue-traceability-map.json   --tests "tests/**/*"   --code "src/**/*"   --context-pack "fixtures/context-pack/upstream-context-promotion-minimal.yaml"   --discovery-pack "fixtures/discovery-pack/upstream-context-promotion-minimal.yaml"   --format json   --output docs/specs/upstream-context-promotion-issue-traceability-matrix.json

ae validate --traceability --strict   --sources docs/specs/upstream-context-promotion-issue-traceability-matrix.json
```

### 7. Current implementation notes
- `Context Pack validate` checks upstream ref existence and aggregates unmapped approved requirements / business use cases as warnings
- `Discovery Pack compile` includes only `approved` entries by default
- `verify-lite` aggregates the following under top-level `discoveryPack` in `artifacts/verify-lite/verify-lite-run-summary.json`
  - `mode`, `reason`, `validateStatus`, `compileStatus`
  - `blockingOpenQuestions`
  - `orphanApprovedRequirements`
  - `orphanApprovedBusinessUseCases`
  - `compileSelectedCount`
  - `compileExcludedByStatusCount`
  - `compileSkippedByTargetCount`
- in report-only mode, warning/error conditions are observed but do not block the PR; strict behavior is enabled only with the `enforce-discovery` label
- `formal/summary.json` is a legacy compatibility path and is not the main target of this guide

### 8. References
- `docs/spec/discovery-pack.md`
- `docs/spec/context-pack.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/issue-requirements-traceability.md`
