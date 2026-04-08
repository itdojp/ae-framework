---
docRole: derived
canonicalSource:
- docs/quality/verify-first-implementation-runbook.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-04-08'
---
# Issue Requirements Traceability (LG-*/REQ-*)

> Language / 言語: English | 日本語

---

## English

This guide standardizes the CLI flow from extracting requirement IDs out of an issue body, to generating a traceability matrix, to running strict validation against the generated matrix.

### 1) Extract requirement IDs from the issue body

```bash
ae traceability extract-ids \
  --issue "https://github.com/<org>/<repo>/issues/1" \
  --pattern "(?:LG|REQ)-[A-Z0-9_-]+" \
  --output docs/specs/issue-traceability-map.json
```

- `--issue` accepts either a GitHub Issue URL or an issue number.
- When an issue number is used, either `--repo <owner/repo>` or `GITHUB_REPOSITORY` is required.
- In private repositories, configure `GH_TOKEN` or `GITHUB_TOKEN`.

### 2) Generate the matrix from the map (`md` / `json`)

```bash
# JSON
ae traceability matrix \
  --map docs/specs/issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --context-pack "spec/context-pack/**/*.{yml,yaml,json}" \
  --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}" \
  --format json \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# Markdown
ae traceability matrix \
  --map docs/specs/issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --context-pack "spec/context-pack/**/*.{yml,yaml,json}" \
  --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}" \
  --format md \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.md
```

The condition for `linked=true` is that the target requirement ID is present in both tests and code.

When Context Pack IDs are discovered in the inputs (for example via `--context-pack`, which by default matches `spec/context-pack/**/*.{yml,yaml,json}`), Context Pack fields such as `diagrams[].id`, `morphisms[].id`, and `acceptance_tests[].id` are also emitted as matrix columns.

When `--discovery-pack` is combined, the matrix starts from Context Pack `upstream_refs` and aggregates Discovery Pack `goal_ids`, `requirement_ids`, `business_use_case_ids`, and `decision_ids` per row. The summary adds:

- `mappedDiscovery*`: count of Discovery Pack IDs actually referenced from the Context Pack
- `unmappedApprovedDiscoveryRequirements` / `unmappedApprovedDiscoveryBusinessUseCases`: count of approved Discovery Pack elements not mapped into the Context Pack
- `unresolvedDiscovery*Refs`: count of Context Pack `upstream_refs` that cannot be resolved inside the Discovery Pack
- `rowsMissingDiscoveryLinks`: count of `linked=true` requirement rows that still have no Discovery Pack upstream links

### Tagging Convention (Phase 1)

- Keep requirement IDs such as `LG-*` / `REQ-*` in both `tests` and `src`.
- In the same file, keep related Context Pack IDs such as `diagramId`, `morphismId`, or `acceptanceTestId` in comments or metadata.
- Example:

```text
// LG-CHECKOUT-01 DGM-CHECKOUT-COMMUTE MOR-CALC-TOTAL AT-CHECKOUT-SUCCESS
```

### 3) Strict validate

```bash
ae validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json
```

- Under strict mode, any of the following causes a non-zero exit:
  - missing test/code linkage
  - missing diagram / morphism / acceptance test IDs when the matrix contains Context Pack columns
- For CI gate usage, pass the generated matrix JSON through `--sources`.

### How to read failures

- In `ae validate --traceability --strict`, the Missing Trace Links report uses `reason` to show the missing linkage class, such as `no diagram ID link`
- `summary.rowsMissingContextPackLinks` shows how many requirement rows are incomplete from the Context Pack perspective
- `summary.missingDiagramLinks`, `summary.missingMorphismLinks`, and `summary.missingAcceptanceTestLinks` break down the missing counts
- `summary.unmappedApprovedDiscoveryRequirements` and `summary.unmappedApprovedDiscoveryBusinessUseCases` indicate approved Discovery Pack elements that never land in the Context Pack
- `summary.unresolvedDiscovery*Refs` indicates broken Context Pack `upstream_refs`

### Output schema

- map: `schema/issue-traceability-map.schema.json`
- matrix: `schema/issue-traceability-matrix.schema.json`

## 日本語

Issue 本文を一次ソースとして、要件 ID 抽出 → matrix 生成 → strict validate までを標準 CLI で実行する手順です。

### 1) Issue 本文から要件 ID を抽出

```bash
ae traceability extract-ids \
  --issue "https://github.com/<org>/<repo>/issues/1" \
  --pattern "(?:LG|REQ)-[A-Z0-9_-]+" \
  --output docs/specs/issue-traceability-map.json
```

- `--issue` は GitHub Issue URL または issue 番号を指定できます
- issue 番号の場合は `--repo <owner/repo>` か `GITHUB_REPOSITORY` が必要です
- private repository では `GH_TOKEN` または `GITHUB_TOKEN` の設定を推奨

### 2) map から matrix を生成（md/json）

```bash
# JSON
ae traceability matrix \
  --map docs/specs/issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --context-pack "spec/context-pack/**/*.{yml,yaml,json}" \
  --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}" \
  --format json \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# Markdown
ae traceability matrix \
  --map docs/specs/issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --context-pack "spec/context-pack/**/*.{yml,yaml,json}" \
  --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}" \
  --format md \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.md
```

`linked=true` の条件は「当該 requirement ID が tests と code の両方に存在すること」です。

入力から Context Pack ID が検出された場合（たとえば `--context-pack`。既定値は `spec/context-pack/**/*.{yml,yaml,json}`）は、Context Pack の `diagrams[].id` / `morphisms[].id` / `acceptance_tests[].id` も matrix の列に出力されます。

`--discovery-pack` を併用した場合は、Context Pack の `upstream_refs` を起点に Discovery Pack の `goal_ids` / `requirement_ids` / `business_use_case_ids` / `decision_ids` を行ごとに集約します。summary には以下が追加されます。

- `mappedDiscovery*`: Context Pack から実際に参照された Discovery Pack ID 数
- `unmappedApprovedDiscoveryRequirements` / `unmappedApprovedDiscoveryBusinessUseCases`: approved だが Context Pack へ未マップの数
- `unresolvedDiscovery*Refs`: Context Pack の `upstream_refs` が Discovery Pack 上で解決できない参照数
- `rowsMissingDiscoveryLinks`: `linked=true` の requirement 行のうち、Discovery Pack upstream が 1 つも付かない行数

### タグ付け規約（Phase 1）

- `tests` と `src` の両方に requirement ID（`LG-*` / `REQ-*`）を残す
- 同じファイル内に、関連する Context Pack ID（`diagramId` / `morphismId` / `acceptanceTestId`）を comment や metadata で残す
- 例:

```text
// LG-CHECKOUT-01 DGM-CHECKOUT-COMMUTE MOR-CALC-TOTAL AT-CHECKOUT-SUCCESS
```

### 3) strict validate を実行

```bash
ae validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json
```

- strict モードでは以下のいずれかが 1 件でもあると非 0 終了になります
  - tests/code 未リンク
  - （matrix に Context Pack 列が存在する場合）diagram / morphism / acceptance test ID 欠落
- CI ゲート用途では matrix（JSON）を `--sources` に渡す運用を推奨します

### 失敗時の見方

- `ae validate --traceability --strict` の Missing Trace Links で、`reason` に欠落種別（`no diagram ID link` など）が出る
- `summary.rowsMissingContextPackLinks` が、Context Pack 観点で不足している要件行数
- `summary.missingDiagramLinks` / `summary.missingMorphismLinks` / `summary.missingAcceptanceTestLinks` で不足件数を内訳確認できる
- `summary.unmappedApprovedDiscoveryRequirements` / `summary.unmappedApprovedDiscoveryBusinessUseCases` は、Discovery Pack 起点で Context Pack に着地していない approved 要素
- `summary.unresolvedDiscovery*Refs` は、Context Pack `upstream_refs` の参照切れ

### 出力スキーマ

- map: `schema/issue-traceability-map.schema.json`
- matrix: `schema/issue-traceability-matrix.schema.json`
