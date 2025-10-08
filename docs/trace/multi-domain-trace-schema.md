# Multi-domain Trace Summary & Envelope Design

Issue refs: #1011 / #1038 / #997

## 背景
KvOnce のトレース・エンベロープでは単一ドメイン（KvOnce）の Projection／Validation 結果のみを `summary.trace` に格納している。今後 Inventory / Reservation / Evidence など複数ドメインのトレースを同一ランで処理するため、Envelope・Step Summary・Grafana で再利用できる共通スキーマを定義する。

## スキーマ方針

```
summary.trace = {
  status: "valid" | "invalid" | "error",
  domains: [
    {
      key: "inventory",
      label: "Inventory",
      status: "valid",
      issues: 0,
      traceIds: ["trace-123"],
      tempoLinks: ["https://tempo.example.com/explore?traceId=..."],
      artifacts: {
        validationPath: "hermetic-reports/trace/inventory/validation.json",
        projectionPath: "...",
        stateSequencePath: "..."
      },
      metrics: {
        eventCount: 42,
        replayStatus: "ran"
      }
    },
    ...
  ],
  aggregate: {
    traceIds: ["trace-123", "trace-456"],
    tempoLinks: [...],
    issues: 0
  }
}
```

- `domains[]` は各ドメインの Projection / Validation サマリを格納する配列。`key` はマシンリーダブルな識別子、`label` は表示用。
- `artifacts` キーでダウンロードリンクを参照できるようにする。既存の KvOnce 用キー（`validationPath` 等）をそのまま再利用。
- `metrics` はドメイン固有指標（イベント件数、リプレイステータス等）を格納するプレースホルダ。
- `aggregate` には全ドメインを通した Trace IDs / Tempo Links / Issue 数を格納し、Step Summary や GitHub コメントでまとめて表示しやすくする。

## Step Summary 表示案

```
## Verify Conformance
- events: 123
- invariant violations: 0
- trace:
  - status: valid
  - ids: trace-123, trace-456
  - domains:
    - inventory: status=valid issues=0 (validation ✅ / projection ✅)
    - reservation: status=invalid issues=2 (validation ⚠️ / projection ✅)
```

- `scripts/formal/verify-conformance.mjs` の `appendStepSummary` に `summary.trace.domains[]` が存在する場合の描画ロジックを追加し、箇条書きで各ドメインのステータスを表示。
- Tempo Links は Step Summary の末尾にリンク一覧として表示し、Slack / GitHub コメントでも流用可能にする。

## Envelope 生成タスク

1. `scripts/trace/build-kvonce-envelope-summary.mjs` をリファクタし、共通ユーティリティで `domains[]` を構築できるようにする。
2. Inventory / Reservation などドメイン別スクリプトが増えた場合でも `buildDomainEntry(domainKey, summary)` のような関数でまとめられるようにする。
3. `scripts/trace/create-report-envelope.mjs` では `summary.trace.domains[].traceIds` をマージし、既存の `tempo-link-utils` を用いて Tempo Links を生成。

## Grafana / Tempo 連携

- `scripts/trace/generate-grafana-variables.mjs` を拡張し、`variables.domains` として `{ value: "inventory", text: "Inventory" }` を出力。テンプレート変数でドメイン切り替えが可能になる。
- Tempo 側 span 属性に `trace.domain=inventory` を付与し、Grafana ダッシュボードで `kvonce_domain` などのタグを使ってフィルタリング。

## TODO

- [ ] Inventory サンプル NDJSON を用意し、`pipelines:trace` で `summary.trace.domains[]` に追加するスクリプトを実装。
- [ ] `scripts/formal/verify-conformance.mjs` の Step Summary 出力を multi-domain 対応させる。
- [ ] Grafana ダッシュボード JSON をドメイン別にエクスポートし、テンプレート変数から切り替えられるようにする。
- [ ] GitHub コメント CLI (`post-envelope-comment.mjs`) で `### Trace Cases` セクションにドメイン名を含める。
