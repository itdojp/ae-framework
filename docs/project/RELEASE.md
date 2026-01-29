# Release Guide (Quality Artifacts) / リリース手順（品質エビデンス）

> 🌍 Language / 言語: English | 日本語

---

## English

When publishing a release, the workflow `release-quality-artifacts` bundles quality evidence:
- `artifacts/` (normalized adapter summaries, domain events, etc.)
- `formal/summary.json` (if present)
- `coverage/coverage-summary.json` (if present)
- `artifacts/summary/PR_SUMMARY.md`
- `artifacts/summary/combined.json` (if present)

Tips
- Ensure CI ran `testing-ddd-scripts` and `coverage-check` before tagging.
- Use labels to temporarily enforce gates on PRs: see `docs/ci/label-gating.md`.

---

## 日本語

リリース公開時、ワークフロー `release-quality-artifacts` は以下の品質エビデンスを同梱します：
- `artifacts/`（正規化されたアダプター要約、ドメインイベント等）
- `formal/summary.json`（存在する場合）
- `coverage/coverage-summary.json`（存在する場合）
- `artifacts/summary/PR_SUMMARY.md`
- `artifacts/summary/combined.json`（存在する場合）

ヒント
- タグ付け前に `testing-ddd-scripts` と `coverage-check` が CI で実行済みであることを確認してください。
- 一時的にゲートを厳格化するには PR ラベルを使用できます。詳細は `docs/ci/label-gating.md` を参照してください。
