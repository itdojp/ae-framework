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
- `ae discovery validate`
- `pnpm run discovery-pack:validate`
- `ae discovery compile`
- `pnpm run discovery-pack:compile`
- `verify-lite` での report-only 観測
- `enforce-discovery` ラベルによる strict rollout

### validate コマンド
```bash
# 既定レイアウトを検証
pnpm run discovery-pack:validate

# CLI namespace から実行
pnpm exec ae discovery validate \
  --sources "spec/discovery-pack/**/*.{yml,yaml,json}"

# blocking open question を fail 条件に昇格
pnpm exec ae discovery validate \
  --sources "spec/discovery-pack/**/*.{yml,yaml,json}" \
  --fail-on blocking-open-questions

# approved 要素が non-approved 要素へ依存していないかを strict に確認
pnpm exec ae discovery validate \
  --sources "spec/discovery-pack/**/*.{yml,yaml,json}" \
  --strict-approved
```

出力先:
- `artifacts/discovery-pack/discovery-pack-validate-report.json`
- `artifacts/discovery-pack/discovery-pack-validate-report.md`

### compile コマンド
```bash
# approved のみで plan-to-spec 正規化 Markdown を生成
pnpm exec ae discovery compile \
  --target plan-spec \
  --sources "spec/discovery-pack/**/*.{yml,yaml,json}"

# context-pack 手編集用の scaffold を生成
pnpm exec ae discovery compile \
  --target context-pack-scaffold \
  --sources "spec/discovery-pack/**/*.{yml,yaml,json}"

# reviewed も明示的に含める
pnpm run discovery-pack:compile -- \
  --target plan-spec \
  --sources "spec/discovery-pack/**/*.{yml,yaml,json}" \
  --include-status approved,reviewed
```

出力先:
- `artifacts/discovery-pack/plan-to-spec-normalized.md`
- `artifacts/discovery-pack/context-pack-scaffold.yaml`
- `artifacts/discovery-pack/discovery-pack-compile-report.json`
- `artifacts/discovery-pack/discovery-pack-compile-report.md`

compile ルール:
- 既定の compile status は `approved` のみです
- `--include-status` を明示した場合のみ `reviewed` / `hypothesis` などを混在させます
- `plan-to-spec` は `ae tests:scaffold --input ...` に渡せる acceptance section を生成します
- `context-pack-scaffold` は non-authoritative な下書きであり、Context Pack SSOT を直接上書きしません
- `as-is` flow は Context Pack `diagrams` に自動昇格しません

### verify-lite staged rollout
- Discovery Pack source がある PR では、`verify-lite` が validate を report-only で観測します
- 既定の report-only では、validate が `warn` / `fail` でも PR を block しません
- strict 化したい場合は PR に `enforce-discovery` ラベルを付与します
- strict 時は以下を有効化します
  - `ae discovery validate --strict-approved`
  - `--fail-on blocking-open-questions`
  - `--fail-on orphan-approved-requirements`
  - `--fail-on orphan-approved-business-use-cases`
  - `ae discovery compile --target plan-spec`

### verify-lite / strict の見方
- summary artifact:
  - `artifacts/verify-lite/verify-lite-run-summary.json`
- Discovery Pack validate report:
  - `artifacts/discovery-pack/discovery-pack-validate-report.json`
  - `artifacts/discovery-pack/discovery-pack-validate-report.md`
- strict 時の compile dry-run:
  - `artifacts/discovery-pack/plan-to-spec-normalized.md`
  - `artifacts/discovery-pack/discovery-pack-compile-report.json`
  - `artifacts/discovery-pack/discovery-pack-compile-report.md`
- PR summary / CI summary では以下を確認します
  - validate status
  - blocking open questions 数
  - orphan approved requirements 数
  - orphan approved business use cases 数
  - strict / report-only の判定理由

### どの変更で strict を使うか
- 新しい業務境界を導入する変更
- 複数アクターをまたぐ業務フローを変更する変更
- 外部システム連携 / 承認 / 通知 / system-of-record の関係を変える変更
- high-risk 扱いで upstream 要求分析の明示を残したい変更

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
