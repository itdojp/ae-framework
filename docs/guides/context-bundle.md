# Context Bundle Guide

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

- Context Bundle is a **structured input** for LLM/agent work.
- It prevents context vacuum by requiring intent, constraints, and artifacts.
- Use the schema in `schema/context-bundle.schema.json` and validate in CI.

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
- `openQuestions`: 不足情報を質問として列挙
- `contextVacuum`: 不足情報のチェック結果

### Context Vacuum チェック（簡易）

以下が欠けている場合は **質問 or 仮定** を追加する。

- 依存関係（呼び出し元/被呼び出し元）
- データ構造（入出力の型/フォーマット）
- 実行文脈（CLI/CI/HTTP などの入口）
- 期待される失敗パターン（エラー語彙）

---

## 例1: Feature 追加

```json
{
  "schemaVersion": "0.1.0",
  "taskIntent": "Add a retry policy for verify-lite upload failures",
  "systemConstraints": ["Node.js 20", "No breaking changes"],
  "roles": ["cli", "infra"],
  "artifacts": [
    {"type": "source", "path": "src/cli/verify-lite.ts", "role": "cli"},
    {"type": "doc", "path": "docs/verify/verify-lite.md", "role": "spec"}
  ],
  "assumptions": ["Retry count defaults to 3"],
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
    {"type": "source", "path": "src/trace/post-envelope-comment.ts", "role": "cli"},
    {"type": "test", "path": "tests/unit/trace/post-envelope-comment.test.ts", "role": "tests"}
  ],
  "assumptions": ["Exit code is 1 on fatal error"],
  "openQuestions": ["Should stderr be asserted strictly?"],
  "contextVacuum": {"status": "ok", "missing": []}
}
```

---

## 関連ファイル

- スキーマ: `schema/context-bundle.schema.json`
- 検証用サンプル: `fixtures/context-bundle/sample.context-bundle.json`
- 検証スクリプト: `scripts/ci/validate-json.mjs`
