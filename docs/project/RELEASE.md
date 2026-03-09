# Release Guide (Quality Artifacts) / リリース手順（品質エビデンス）

> 🌍 Language / 言語: English | 日本語

---

## English

When publishing a release, the workflow `release-quality-artifacts` bundles quality evidence:
- `artifacts/` (normalized adapter summaries, domain events, etc.)
- `formal/summary.json` (if present)
- `coverage/coverage-summary.json` (if present)
- `artifacts/assurance/assurance-summary.json` / `.md` (if present)
- `artifacts/summary/PR_SUMMARY.md`
- `artifacts/summary/combined.json` (if present)

Tips
- Ensure CI ran `testing-ddd-scripts` and `coverage-check` before tagging.
- Use labels to temporarily enforce gates on PRs: see `docs/ci/label-gating.md`.
- `post-deploy-verify.yml` appends `artifacts/assurance/assurance-summary.md` to the Step Summary when the artifact is available. This summary is optional and report-only; it does not change the release verify gate result.
- When running `post-deploy-verify.yml` manually, set `release_tag` to download `quality-artifacts.tgz` from the target release if local assurance artifacts are not already present.
- `release-quality-artifacts` run via `workflow_dispatch` uploads an Actions artifact named `quality-artifacts`; it does not publish a GitHub Release asset. `release_tag` works only with a published release asset `quality-artifacts.tgz`.

### Breaking schema changes (required)
When changing machine-readable outputs (for example `schema/*.schema.json` consumers), follow this procedure in the same PR:
1. Bump the schema version marker (for example `schemaVersion` major for backward-incompatible changes).
2. Apply `dual-write + dual-validate` during migration when consumers exist on both old and new contracts.
3. Update contract tests and schema validation scripts so CI fails on invalid payloads and passes on expected payloads.
4. Add a compatibility note in release notes with:
   - affected command/artifact
   - old vs new schema/version
   - migration guidance
5. Update the contract inventory documents:
   - `docs/reference/CONTRACT-CATALOG.md`
   - `docs/reference/SCHEMA-GOVERNANCE.md`
6. Link the tracking issue/PR in the release note entry.

---

## 日本語

リリース公開時、ワークフロー `release-quality-artifacts` は以下の品質エビデンスを同梱します：
- `artifacts/`（正規化されたアダプター要約、ドメインイベント等）
- `formal/summary.json`（存在する場合）
- `coverage/coverage-summary.json`（存在する場合）
- `artifacts/assurance/assurance-summary.json` / `.md`（存在する場合）
- `artifacts/summary/PR_SUMMARY.md`
- `artifacts/summary/combined.json`（存在する場合）

ヒント
- タグ付け前に `testing-ddd-scripts` と `coverage-check` が CI で実行済みであることを確認してください。
- 一時的にゲートを厳格化するには PR ラベルを使用できます。詳細は `docs/ci/label-gating.md` を参照してください。
- `post-deploy-verify.yml` は assurance artifact が存在する場合、`artifacts/assurance/assurance-summary.md` を Step Summary に追記します。これは optional / report-only であり、release verify の gate 判定には使いません。
- `post-deploy-verify.yml` を手動実行する際にローカルの assurance artifact がない場合は、対象 release の `quality-artifacts.tgz` を取得するため `release_tag` を指定してください。
- `release-quality-artifacts` を `workflow_dispatch` で手動実行した場合は Actions artifact `quality-artifacts` が生成されるだけで、GitHub Release asset は作成されません。`release_tag` が参照できるのは公開済み release asset `quality-artifacts.tgz` のみです。

### 互換性破壊を伴うスキーマ変更（必須手順）
機械可読出力（例: `schema/*.schema.json` の利用対象）を変更する場合は、同一PRで次を実施します。
1. スキーマのバージョン識別子を更新する（後方互換性を破る場合は `schemaVersion` の major を更新）。
2. 旧/新の利用者が併存する期間は `dual-write + dual-validate` を運用する。
3. 契約テストとスキーマ検証スクリプトを更新し、想定外ペイロードをCIで検出できる状態にする。
4. リリースノートに互換性注記を追加する。
   - 影響コマンド/成果物
   - 旧/新スキーマまたはバージョン
   - 移行手順
5. 契約棚卸しドキュメントを更新する。
   - `docs/reference/CONTRACT-CATALOG.md`
   - `docs/reference/SCHEMA-GOVERNANCE.md`
6. リリースノート項目に追跡 Issue/PR を紐付ける。
