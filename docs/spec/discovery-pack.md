---
docRole: ssot
lastVerified: '2026-03-16'
owner: discovery-pack-ops
verificationCommand: pnpm -s run check:doc-consistency
---
# Discovery Pack v1

> Language / 言語: English | 日本語

---

## 日本語

Discovery Pack v1 は、要求分析を repo 内で構造化し、後続の Context Pack / traceability / CI に渡すための upstream input contract です。

### 位置づけ
- Discovery Pack は設計 SSOT ではありません
- Discovery Pack は要求分析の構造化入力契約です
- Context Pack は設計 SSOT のまま維持します
- Discovery Pack から生成される Markdown / scaffold は non-authoritative artifact として扱います

### 初期 profile
- 初期 profile は `rdra-lite` です
- これは core 実装に方法論名を固定するためではなく、最小 profile を明示するための起点です
- profile 固有の運用判断は docs と fixture で段階追加します

### status の意味
- `hypothesis`: 仮説。compile 既定対象外
- `reviewed`: 人間レビュー済みだが未承認。compile 既定対象外
- `approved`: compile 既定対象
- `rejected`: 却下済み。compile 既定対象外
- `deferred`: 保留。compile 既定対象外

### compile 方針
- compile の既定対象は `approved` のみです
- `reviewed` / `hypothesis` を混在させる場合は、後続 CLI 側で明示フラグを要求します
- Discovery Pack から Context Pack を直接 authoritative に上書きしません

### default source layout
```text
spec/discovery-pack/index.yaml
spec/discovery-pack/flows/*.mmd
spec/discovery-pack/sources/*
```

### v1 の最小要素
- `version`
- `profile`
- `sources`
- `actors`
- `external_systems`
- `goals`
- `requirements`
- `business_use_cases`
- `flows`
- `decisions`
- `assumptions`
- `open_questions`

### 共通フィールド
以下の要素は共通フィールドを持ちます。
- `actors`
- `external_systems`
- `goals`
- `requirements`
- `business_use_cases`
- `flows`
- `decisions`
- `assumptions`
- `open_questions`

共通フィールド
- `id`
- `status`
- `source_refs`
- `traces_to`
- `detail_path`（任意）

### source / trace の扱い
- `sources[].id` は根拠資料の参照元です
- `source_refs` は `sources[].id` を参照します
- `traces_to` は Discovery Pack 内の他要素 ID を参照します
- `flows` は Mermaid の意味解釈自体を schema では扱わず、`mermaid_path` を契約として持ちます

### rdra-lite sample
最小 sample は `fixtures/discovery-pack/minimal.yaml`、rdra-lite profile の sample は `fixtures/discovery-pack/rdra-lite-sample.yaml` を参照してください。

### 現時点の実装範囲
- schema
- fixtures
- Contract Catalog 登録

以下は follow-up issue で追加します。
- `ae discovery validate`
- `ae discovery compile`
- Context Pack への `upstream` / `upstream_refs`
- `verify:lite` への staged rollout

### 関連
- Context Pack v1: `docs/spec/context-pack.md`
- Spec registry: `docs/spec/registry.md`
- Contract Catalog: `docs/reference/CONTRACT-CATALOG.md`

## English (Summary)

- Discovery Pack v1 is an upstream input contract for structured requirements discovery before Context Pack.
- It is not the design SSOT.
- Default compile scope is `approved` only.
- Initial profile is `rdra-lite`.
- Default source layout is `spec/discovery-pack/` with Mermaid flow files under `flows/`.
