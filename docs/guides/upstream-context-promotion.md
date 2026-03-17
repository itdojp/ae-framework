---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/spec/discovery-pack.md
- docs/quality/assurance-profile.md
- docs/quality/issue-requirements-traceability.md
lastVerified: '2026-03-17'
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
- `formal/summary.json` は legacy compatibility path であり、このガイドの主対象ではありません

### 8. 参照
- `docs/spec/discovery-pack.md`
- `docs/spec/context-pack.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/issue-requirements-traceability.md`
