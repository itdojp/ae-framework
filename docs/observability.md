# Observability Logging (JSONL) & Trace Correlation

> 🌍 Language / 言語: English | 日本語

---

## English

### Purpose
Standardize agent and CI execution logs as JSON Lines (JSONL) so every stage can be correlated with `runId` and `traceId`. Use this when you need end-to-end visibility across intent, specification, tests, implementation, and verification artifacts.

### JSONL format
- Use **one JSON object per line**.
- Assume UTF-8 encoding.
- Do not embed large payloads directly in the log. Store them as artifacts and reference the paths.

#### Required fields

| Field | Type | Purpose |
| --- | --- | --- |
| `timestamp` | string (ISO 8601) | Event time |
| `level` | string | `debug` / `info` / `warn` / `error` |
| `event` | string | Event kind, for example `node.started` |
| `message` | string | Human-readable short message |
| `runId` | string | Correlation key for the full pipeline run |
| `traceId` | string | Cross-stage correlation key; also required when the NDJSON is ingested by `ae conformance ingest` |
| `actor` | string | Event producer or operator identity; required for `ae conformance ingest` |

#### Recommended fields

| Field | Type | Purpose |
| --- | --- | --- |
| `stage` | string | Stage name such as `intent2formal` or `formal2tests` |
| `nodeId` | string | Flow node identifier |
| `commit` | string | Git SHA (use the resolved SHA, not a symbolic ref such as `HEAD`) |
| `branch` | string | Branch name |
| `artifactPaths` | string[] | Related artifact locations |
| `context` | object | Small, bounded supplemental data |

### Correlation rules
- `runId` is mandatory and must remain stable for a single execution.
- Preserve `traceId` across as many stages as possible (`NL -> BDD -> Formal -> Tests -> Code -> Artifacts`).
- When wrapping JSONL lines in an envelope, include each per-line `traceId` value in `traceCorrelation.traceIds[]`.
- Keep `runId`, `commit`, `branch`, and `traceCorrelation.traceIds` aligned with the JSONL `traceId` values and other correlation fields defined in `schema/envelope.schema.json`.

### Recommended output locations
- `artifacts/observability/ae-run-<runId>.jsonl`
- `artifacts/observability/run.jsonl` when CI already aggregates per-run logs

### Example JSONL

```text
{"timestamp":"2026-01-07T12:00:00.000Z","level":"info","event":"node.started","message":"intent2formal start","runId":"run-20260107-001","traceId":"inv-001","stage":"intent2formal","nodeId":"n1","commit":"550933b2","branch":"main"}
{"timestamp":"2026-01-07T12:00:03.000Z","level":"info","event":"artifact.written","message":"formal spec generated","runId":"run-20260107-001","traceId":"inv-001","stage":"intent2formal","artifactPaths":["artifacts/spec/formal.json"]}
{"timestamp":"2026-01-07T12:00:05.000Z","level":"error","event":"node.failed","message":"tests2code failed","runId":"run-20260107-001","traceId":"inv-001","stage":"tests2code","context":{"reason":"compile error"}}
```

### Related documents
- `docs/guides/trace-id.md`
- `docs/trace/REPORT_ENVELOPE.md`
- `schema/envelope.schema.json`
- `schema/flow.schema.json`

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

```text
{"timestamp":"2026-01-07T12:00:00.000Z","level":"info","event":"node.started","message":"intent2formal start","runId":"run-20260107-001","traceId":"inv-001","stage":"intent2formal","nodeId":"n1","commit":"550933b2","branch":"main"}
{"timestamp":"2026-01-07T12:00:03.000Z","level":"info","event":"artifact.written","message":"formal spec generated","runId":"run-20260107-001","traceId":"inv-001","stage":"intent2formal","artifactPaths":["artifacts/spec/formal.json"]}
{"timestamp":"2026-01-07T12:00:05.000Z","level":"error","event":"node.failed","message":"tests2code failed","runId":"run-20260107-001","traceId":"inv-001","stage":"tests2code","context":{"reason":"compile error"}}
```

### 関連ドキュメント

- `docs/guides/trace-id.md`
- `docs/trace/REPORT_ENVELOPE.md`
- `schema/envelope.schema.json`
- `schema/flow.schema.json`
