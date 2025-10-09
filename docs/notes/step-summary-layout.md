# Step Summary Layout (Spec / Verify Lite / Trace)

Issue refs: #1097 / #1096 / #1038

## 目的
- GitHub Actions の Step Summary を統一し、Spec → Verify Lite → Trace の結果を 1 つのカードとして俯瞰できるようにする。
- Envelope / pipelines:trace が出力するメタデータを利用し、失敗時に必要なリンク（Artifact, Tempo Explore）へすぐ遷移できるようにする。

## 標準レイアウト
```
## Verify Conformance
- events: <number>
- schema errors: <number>
- invariant violations: <number>
- trace:
  - status: <valid|invalid|failed>
  - validation: valid=<bool> issues=<number>
  - replay: <ran|failed|skipped>
```

- **Spec セクション**: `verify:conformance` が TLC 実行時に `hermetic-reports/formal/tla-summary.json` のステータスを要約する（ツールが未導入の場合は `status: tool_not_available` を表示）。
- **Verify Lite セクション**: `pipelines:full` で `reports/verify-lite/verify-lite-run-summary.json` を Envelope に詰めたうえで、lint / mutation quick / property の結果を `summary.steps.*` から抜粋する。
  - Lint Baseline Diff や Mutation HTML レポートは Step Summary の “Artifacts” セクションに `Lint Baseline Diff` / `Mutation HTML Report` として表示し、GitHub Artifacts への Data Link を添付する。
- **Trace セクション**: `verify:conformance` または `verify:conformance --from-envelope` の `summary.trace` を描画し、Projection/Validation/TLC の結果と issues 数を列挙する。`REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE` を設定しておくと Tempo Explore へのリンクも自動生成できる。
  - `traceIds` や `artifacts` 情報（projection/validation/state sequence/replay）を付与しておくと、Step Summary から GitHub Artifacts へジャンプできる。
  - Multi-domain 対応時は `summary.trace.domains[]` を検出し、下記フォーマットでドメインごとの結果を箇条書きする：

```
  - domains:
    - inventory: status=valid issues=0 (traceIds: trace-inventory-1)
    - reservation: status=invalid issues=2 (traceIds: trace-resv-8)
```

  - Tempo Links は `summary.trace.domains[].tempoLinks` および `summary.tempoLinks` をマージし、Step Summary の末尾にリンク一覧を表示する。

## 実装メモ (2025-10-09)
- `scripts/ci/step-summary.mjs` が `appendSection` などの共通ユーティリティを提供し、`verify-conformance`・`pipelines:trace`・CI スクリプトから同じ Markdown フォーマットで出力できる。
- `scripts/formal/verify-conformance.mjs` は `--from-envelope` オプションに対応し、既存の report-envelope から Step Summary を再掲できる（PR #1102）。
- `pipelines:trace` は conformance summary と report envelope を生成し、CI 以外の環境でも Envelope → Step Summary を再利用できるようになった（PR #1103）。
- Verify Lite 側の Step Summary も Envelope 経由で統合済み（PR #1093）。
- Tempo / Grafana へリンクを貼る場合は `docs/trace/grafana/tempo-dashboard.md` のプレイブックに沿って Data Link を設定する。

## TODO
- [x] Verify Lite ワークフローの Step Summary に mutation report / lint baseline diff へのリンクを追加する。
- [ ] Trace Envelope の `artifacts[]` から Tempo / S3 への Data Link を生成し、Step Summary から直接遷移できるようにする。
- [ ] Multi-domain Trace が実装されたら `summary.trace.domains[]` をサポートする。
- [ ] Step Summary 再利用手順（`--from-envelope`）を CI ガイドラインに反映し、手動トラブルシュート手順を整備する。
