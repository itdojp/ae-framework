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

### Breaking schema changes (required)
When changing machine-readable outputs (for example `schema/*.schema.json` consumers), follow this procedure in the same PR:
1. Bump the schema version marker (for example `schemaVersion` major for backward-incompatible changes).
2. Update contract tests and schema validation scripts so CI fails on old payloads and passes on new payloads.
3. Add a compatibility note in release notes with:
   - affected command/artifact
   - old vs new schema/version
   - migration guidance
4. Link the tracking issue/PR in the release note entry.

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

### 互換性破壊を伴うスキーマ変更（必須手順）
機械可読出力（例: `schema/*.schema.json` の利用対象）を変更する場合は、同一PRで次を実施します。
1. スキーマのバージョン識別子を更新する（後方互換性を破る場合は `schemaVersion` の major を更新）。
2. 契約テストとスキーマ検証スクリプトを更新し、旧ペイロードをCIで検出できる状態にする。
3. リリースノートに互換性注記を追加する。
   - 影響コマンド/成果物
   - 旧/新スキーマまたはバージョン
   - 移行手順
4. リリースノート項目に追跡 Issue/PR を紐付ける。
