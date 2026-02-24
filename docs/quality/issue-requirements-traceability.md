# Issue Requirements Traceability (LG-*/REQ-*)

Issue本文を一次ソースとして、要件ID抽出 → matrix 生成 → strict validate までを標準CLIで実行する手順です。

## 1) Issue本文から要件ID抽出

```bash
ae traceability extract-ids \
  --issue "https://github.com/<org>/<repo>/issues/1" \
  --pattern "(?:LG|REQ)-[A-Z0-9_-]+" \
  --output docs/specs/issue-traceability-map.json
```

- `--issue` は GitHub Issue URL または issue number を指定可能
- issue number の場合は `--repo <owner/repo>` か `GITHUB_REPOSITORY` が必要
- private repository では `GH_TOKEN` または `GITHUB_TOKEN` の設定を推奨

## 2) map から matrix 生成（md/json）

```bash
# JSON
ae traceability matrix \
  --map docs/specs/issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --context-pack "spec/context-pack/**/*.{yml,yaml,json}" \
  --format json \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# Markdown
ae traceability matrix \
  --map docs/specs/issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --context-pack "spec/context-pack/**/*.{yml,yaml,json}" \
  --format md \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.md
```

`linked=true` の条件は「当該 requirement ID が tests と code の両方に存在すること」です。

`--context-pack` を指定した場合は Context Pack の `diagrams[].id` / `morphisms[].id` / `acceptance_tests[].id` も matrix の列に出力されます。

### タグ付け規約（Phase 1）

- `tests` と `src` の両方に requirement ID（`LG-*` / `REQ-*`）を残す
- 同じファイル内に、関連する Context Pack ID（`diagramId`/`morphismId`/`acceptanceTestId`）をコメントやメタデータで残す
- 例:

```ts
// LG-CHECKOUT-01 DGM-CHECKOUT-COMMUTE MOR-CALC-TOTAL AT-CHECKOUT-SUCCESS
```

## 3) strict validate

```bash
ae validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json
```

- strict では以下のいずれかが1件でもあると非0終了
  - tests/code 未リンク
  - （matrix に Context Pack 列が存在する場合）diagram/morphism/acceptance test ID 欠落
- CIゲート用途では matrix(JSON) を `--sources` に渡す運用を推奨

## 失敗時の見方

- `ae validate --traceability --strict` の Missing Trace Links で、`reason` に欠落種別（`no diagram ID link` など）が出る
- matrix `summary.rowsMissingContextPackLinks` が、Context Pack 観点で不足している要件行数
- `summary.missingDiagramLinks` / `summary.missingMorphismLinks` / `summary.missingAcceptanceTestLinks` で不足件数を内訳確認できる

## 出力スキーマ

- map: `schema/issue-traceability-map.schema.json`
- matrix: `schema/issue-traceability-matrix.schema.json`
