---
docRole: derived
canonicalSource:
- schema/context-bundle.schema.json
- docs/spec/context-pack.md
lastVerified: '2026-03-23'
---
# Context Bundle Guide

> 🌍 Language / 言語: English | 日本語

---

## English

### Purpose

Context Bundle is a **structured input artifact** for LLM/agent work. It reduces ambiguity by recording intent, constraints, dependencies, and evidence in a machine-validatable format.

Operational goals:
- prevent the fragmented-input failure mode often called Context Vacuum
- leave traceable responsibility for assumptions, open questions, and referenced artifacts
- make the handoff schema-valid through `schema/context-bundle.schema.json`

### Recommended fields

- `taskIntent`: what the operator wants to achieve
- `systemConstraints`: language / environment / compatibility / prohibitions
- `artifacts`: code, docs, logs, or configs that must be consulted
- `roles`: role labels such as controller / service / domain / helper / test
- `assumptions`: explicit provisional assumptions
- `contracts`: structured DbC expectations (preconditions / postconditions / invariants)
- `openQuestions`: unresolved information that must be answered or carried forward
- `contextVacuum`: the checklist result for missing context

### Optional `contracts` field

`contracts` is an optional backward-compatible field used to record DbC expectations in a structured way.

- `contracts.preconditions`: input constraints and prerequisite state
- `contracts.postconditions`: observable results and side effects
- `contracts.invariants`: constraints that must remain true throughout the operation

Each item may use either of the following shapes:
- simple form: a string
- extended form: `{ id?, statement, scope?, severity?, source?, notes? }`

### Context Vacuum check (minimum)

If any of the following is missing, add it either as an **open question** or an explicit **assumption**.

- dependency relationships (callers / callees)
- data structures (input/output types or formats)
- execution context (CLI / CI / HTTP and similar entry points)
- expected failure patterns (error vocabulary)
- missing DbC conditions (preconditions / postconditions / invariants)

### Workflow integration notes

- use Context Bundle when issue text or copied snippets do not preserve dependency flow, contracts, or execution context
- keep `taskIntent`, `artifacts`, `assumptions`, and `openQuestions` aligned with the current operator request before handing off to an agent
- if `contextVacuum.status` is `missing`, either fill the missing items or carry them forward explicitly as `openQuestions`
- validate new bundles against `schema/context-bundle.schema.json` before handing them to an agent
- use `scripts/ci/validate-json.mjs` only for the committed sample fixture and other repository fixtures

### Example 1: Feature addition

```json
{
  "schemaVersion": "0.1.0",
  "taskIntent": "Add a retry policy for verify-lite upload failures",
  "systemConstraints": ["Node.js 20", "No breaking changes"],
  "roles": ["cli", "infra"],
  "artifacts": [
    {"type": "script", "path": "scripts/ci/run-verify-lite-local.sh", "role": "cli"},
    {"type": "script", "path": "scripts/ci/write-verify-lite-summary.mjs", "role": "infra"},
    {"type": "doc", "path": "docs/agents/recipes/verify-lite.md", "role": "spec"}
  ],
  "assumptions": ["Retry count defaults to 3"],
  "contracts": {
    "preconditions": ["Retry target endpoint is reachable"],
    "postconditions": ["Retry attempts are logged with final status"],
    "invariants": [
      {"id": "INV-RETRY-001", "statement": "Retry attempts never exceed configured max", "severity": "high"}
    ]
  },
  "openQuestions": ["Should retry be exponential or fixed?"],
  "contextVacuum": {"status": "missing", "missing": ["error taxonomy"]}
}
```

### Example 2: Bug fix

```json
{
  "schemaVersion": "0.1.0",
  "taskIntent": "Fix missing envelope error handling in post-envelope-comment",
  "systemConstraints": ["TypeScript", "No new deps"],
  "roles": ["cli", "tests"],
  "artifacts": [
    {"type": "source", "path": "scripts/trace/post-envelope-comment.mjs", "role": "cli"},
    {"type": "test", "path": "tests/unit/trace/post-envelope-comment.test.ts", "role": "tests"}
  ],
  "assumptions": ["Exit code is 1 on fatal error"],
  "contracts": {
    "preconditions": [{"id": "PRE-CLI-001", "statement": "Input file is valid JSON", "severity": "high"}],
    "postconditions": ["CLI exits with code 1 when envelope is missing"],
    "invariants": ["traceCorrelation fields remain schema-compliant"]
  },
  "openQuestions": ["Should stderr be asserted strictly?"],
  "contextVacuum": {"status": "ok", "missing": []}
}
```

### Related files

- schema: `schema/context-bundle.schema.json`
- sample fixture: `fixtures/context-bundle/sample.context-bundle.json`
- sample-fixture validation entry point: `scripts/ci/validate-json.mjs`

---

## 日本語（詳細）

### 目的

Context Bundle は、LLM/エージェントに渡すコンテキストを **構造化**し、誤解や推測を減らすための成果物です。

- 断片コード貼り付けの「Context Vacuum」を防止する
- 依存関係・データ構造・呼び出し文脈を明示し、説明責任を残す
- `schema/context-bundle.schema.json` で検証可能にする

### 推奨フィールド

- `taskIntent`: 何を達成したいか（目的）
- `systemConstraints`: 言語/環境/互換性/禁止事項
- `artifacts`: 参照すべき仕様/コード/ログ/設定
- `roles`: 役割ラベル（controller/service/domain/helper/test など）
- `assumptions`: 不明点を仮定として明示
- `contracts`: DbC（pre/post/invariant）を構造化して記録
- `openQuestions`: 不足情報を質問として列挙
- `contextVacuum`: 不足情報のチェック結果

### `contracts` フィールド（任意）

`contracts` は後方互換を保った任意フィールドです。DbCの3条件を明示し、テスト/ゲートへの接続を明確にします。

- `contracts.preconditions`: 事前条件（入力制約、前提状態）
- `contracts.postconditions`: 事後条件（観測可能な結果、副作用）
- `contracts.invariants`: 不変条件（常に守る制約）

各要素は次の2形式を許容します。
- 簡易形式: 文字列
- 拡張形式: `{ id?, statement, scope?, severity?, source?, notes? }`

### Context Vacuum チェック（簡易）

以下が欠けている場合は **質問 or 仮定** を追加する。

- 依存関係（呼び出し元/被呼び出し元）
- データ構造（入出力の型/フォーマット）
- 実行文脈（CLI/CI/HTTP などの入口）
- 期待される失敗パターン（エラー語彙）
- DbC 3条件（pre/post/invariant）の不足

### ワークフロー統合メモ

- issue本文や断片コードだけでは依存関係、契約、実行文脈が欠ける場合に Context Bundle を使う
- handoff 前に `taskIntent`、`artifacts`、`assumptions`、`openQuestions` を最新の依頼内容へ揃える
- `contextVacuum.status` が `missing` のときは、不足項目を埋めるか、`openQuestions` として明示的に持ち越す
- 新しい bundle は `schema/context-bundle.schema.json` に対して検証してから渡す
- `scripts/ci/validate-json.mjs` は repository にコミットされた sample fixture 向けの検証であり、新規 bundle の汎用 validator ではない

---

## 例1: Feature 追加

```json
{
  "schemaVersion": "0.1.0",
  "taskIntent": "Add a retry policy for verify-lite upload failures",
  "systemConstraints": ["Node.js 20", "No breaking changes"],
  "roles": ["cli", "infra"],
  "artifacts": [
    {"type": "script", "path": "scripts/ci/run-verify-lite-local.sh", "role": "cli"},
    {"type": "script", "path": "scripts/ci/write-verify-lite-summary.mjs", "role": "infra"},
    {"type": "doc", "path": "docs/agents/recipes/verify-lite.md", "role": "spec"}
  ],
  "assumptions": ["Retry count defaults to 3"],
  "contracts": {
    "preconditions": ["Retry target endpoint is reachable"],
    "postconditions": ["Retry attempts are logged with final status"],
    "invariants": [
      {"id": "INV-RETRY-001", "statement": "Retry attempts never exceed configured max", "severity": "high"}
    ]
  },
  "openQuestions": ["Should retry be exponential or fixed?"],
  "contextVacuum": {"status": "missing", "missing": ["error taxonomy"]}
}
```

## 例2: Bug 修正

```json
{
  "schemaVersion": "0.1.0",
  "taskIntent": "Fix missing envelope error handling in post-envelope-comment",
  "systemConstraints": ["TypeScript", "No new deps"],
  "roles": ["cli", "tests"],
  "artifacts": [
    {"type": "source", "path": "scripts/trace/post-envelope-comment.mjs", "role": "cli"},
    {"type": "test", "path": "tests/unit/trace/post-envelope-comment.test.ts", "role": "tests"}
  ],
  "assumptions": ["Exit code is 1 on fatal error"],
  "contracts": {
    "preconditions": [{"id": "PRE-CLI-001", "statement": "Input file is valid JSON", "severity": "high"}],
    "postconditions": ["CLI exits with code 1 when envelope is missing"],
    "invariants": ["traceCorrelation fields remain schema-compliant"]
  },
  "openQuestions": ["Should stderr be asserted strictly?"],
  "contextVacuum": {"status": "ok", "missing": []}
}
```

---

## 関連ファイル

- スキーマ: `schema/context-bundle.schema.json`
- 検証用サンプル: `fixtures/context-bundle/sample.context-bundle.json`
- サンプル fixture の検証スクリプト: `scripts/ci/validate-json.mjs`
