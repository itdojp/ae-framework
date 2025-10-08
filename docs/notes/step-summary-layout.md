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

- **Spec セクション**: `verify:conformance` が TLC 実行時に `hermetic-reports/formal/tla-summary.json` のステータスを要約する。
- **Verify Lite セクション**: `pipelines:full` で `reports/verify-lite/verify-lite-run-summary.json` を Envelope に詰めたうえで、lint / mutation quick / property の結果を `summary.steps.*` から抜粋する。
- **Trace セクション**: `pipelines:trace` が生成した Projection/Validation/TLC summary を `summary.trace` として配置し、問題の key があれば `notes` に列挙する。

## 実装メモ
- `scripts/formal/verify-conformance.mjs` が Step Summary 出力に対応済み。Trace 部分は Envelope から `summary.trace` を参照する。
- `pipelines:full` は Verify Lite の Step Summary を呼び出し、mutation quick のスコアを同伴する。（PR #1093）
- 追加のジョブが同じテンプレートを利用できるよう、共通関数を `scripts/ci/step-summary.mjs`（今後実装）に切り出す予定。

## TODO
- [ ] `scripts/ci/step-summary.mjs` を作成し、Spec/Verify Lite/Trace の Markdown 生成を関数化する。
- [ ] Verify Lite ワークフローで Step Summary にリンクを追加（mutation report / lint baseline diff など）。
- [ ] Multi-domain Trace が実装されたら `summary.trace.domains[]` を Step Summary に展開する。
