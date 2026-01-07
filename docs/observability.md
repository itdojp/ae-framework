# Observability Logging (JSONL) & Trace Correlation

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

- Use JSON Lines (JSONL) for pipeline and agent logs: **one JSON object per line**.
- Always include a **stable runId** to correlate all events in a single pipeline run.
- Use **traceId** to connect artifacts, tests, and verification results end-to-end.
- Keep logs compact; store large payloads as artifacts and reference by path.

---

## 日本語（詳細）

### 目的

Agent/CI の実行ログを **JSONL** で統一し、`runId` と `traceId` で全段階のイベントを相関できるようにする。

### JSONL フォーマット

- **1行1JSON**（改行で分割可能なことが前提）
- 文字列は UTF-8 を想定
- 大きなデータはログに埋め込まず **artifact へ保存**し、パスを参照する

#### 必須フィールド

| フィールド | 型 | 目的 |
| --- | --- | --- |
| `timestamp` | string (ISO 8601) | 事象発生時刻 |
| `level` | string | `debug` / `info` / `warn` / `error` |
| `event` | string | イベント種別（例: `node.started`） |
| `message` | string | 人間向け短文 |
| `runId` | string | パイプライン全体の相関キー |

#### 推奨フィールド

| フィールド | 型 | 目的 |
| --- | --- | --- |
| `traceId` | string | 仕様→テスト→実装→検証の横断相関 |
| `stage` | string | `intent2formal` / `formal2tests` など |
| `nodeId` | string | flow ノード ID |
| `commit` | string | Git SHA |
| `branch` | string | ブランチ名 |
| `artifactPaths` | string[] | 関連成果物のパス |
| `context` | object | 追加情報（小さく保つ） |

### 相関ルール

- **runId は必須**（1回の実行単位で固定）
- **traceId は可能な限り全段階で維持**（NL → BDD → Formal → Tests → Code → Artifacts）
- `runId/commit/branch/traceIds` は `schema/envelope.schema.json` の `traceCorrelation` と整合させる

### 推奨出力先

- `artifacts/observability/ae-run-<runId>.jsonl`
- 既存の CI で集約する場合は `artifacts/observability/run.jsonl` でも可

### JSONL 例

```json
{"timestamp":"2026-01-07T12:00:00.000Z","level":"info","event":"node.started","message":"intent2formal start","runId":"run-20260107-001","traceId":"inv-001","stage":"intent2formal","nodeId":"n1","commit":"HEAD","branch":"main"}
{"timestamp":"2026-01-07T12:00:03.000Z","level":"info","event":"artifact.written","message":"formal spec generated","runId":"run-20260107-001","traceId":"inv-001","stage":"intent2formal","artifactPaths":["artifacts/spec/formal.json"]}
{"timestamp":"2026-01-07T12:00:05.000Z","level":"error","event":"node.failed","message":"tests2code failed","runId":"run-20260107-001","traceId":"inv-001","stage":"tests2code","context":{"reason":"compile error"}}
```

### 関連ドキュメント

- `docs/guides/trace-id.md`
- `docs/trace/REPORT_ENVELOPE.md`
- `schema/envelope.schema.json`
- `schema/flow.schema.json`
