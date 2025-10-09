# Full Pipeline Prep Plan

Issue refs: #1038 / #1097

## 現状
- Verify Lite / Trace / Envelope / Tempo / Grafana / GitHub コメントまでのフローは個別 CLI で整備済み。
- Slack / S3 自動化 (`publish-envelope.mjs`) や multi-domain trace, Grafana CI の設計が進行中。

## フルパイプライン実行までに整備したい項目
1. **環境変数整理**
   - AWS: `AWS_REGION`, `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY`
   - Slack: `ENVELOPE_PUBLISH_SLACK_WEBHOOK`, `ENVELOPE_PUBLISH_SLACK_CHANNEL`
   - Grafana: `GRAFANA_BASE_URL`, `GRAFANA_API_TOKEN`
2. **ワークフロー順序**
   1. `pnpm pipelines:full`
   2. `node scripts/trace/publish-envelope.mjs --bucket ... --dry-run` → Slack リンク確認
   3. `node scripts/trace/generate-grafana-variables.mjs`
   4. `node scripts/trace/post-envelope-comment.mjs --dry-run`
   5. `node scripts/trace/publish-envelope.mjs`（本番実行）
3. **TODO**
   - [ ] GitHub Actions で `pipelines:full` を nightly 実行し、失敗時は Slack に通知。
   - [ ] `publish-envelope.mjs --dry-run` と `post-envelope-comment.mjs --dry-run` を Step Summary に出力するジョブを追加。
   - [ ] Grafana CI workflow を手動実行し、テンプレ変数更新を確認する手順をドキュメント化。
