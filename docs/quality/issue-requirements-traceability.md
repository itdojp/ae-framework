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
  --format json \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# Markdown
ae traceability matrix \
  --map docs/specs/issue-traceability-map.json \
  --tests "tests/**/*" \
  --code "src/**/*" \
  --format md \
  --output docs/specs/ISSUE-TRACEABILITY-MATRIX.md
```

`linked=true` の条件は「当該 requirement ID が tests と code の両方に存在すること」です。

## 3) strict validate

```bash
ae validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json
```

- strict では未リンク要件が1件でもあると非0終了
- CIゲート用途では matrix(JSON) を `--sources` に渡す運用を推奨

## 出力スキーマ

- map: `schema/issue-traceability-map.schema.json`
- matrix: `schema/issue-traceability-matrix.schema.json`
