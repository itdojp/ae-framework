# Coverage Required — 運用ガイド（ブランチ保護）

目的
- PRでは非ブロッキングでカバレッジを可視化し、mainに対しては必要に応じてしきい値を強制する。

手順（推奨）
- リポジトリ変数の設定（Settings → Variables → Repository variables）
  - `COVERAGE_ENFORCE_MAIN=1`（main への push を強制対象に）
  - `COVERAGE_DEFAULT_THRESHOLD`（例: 80）
- ブランチ保護（Settings → Branches → Branch protection rules）
  - `Require status checks to pass before merging` を有効化
  - ステータスチェックに `coverage-check` を追加（必要に応じて `coverage-check (push)` / `(pull_request)` を選択）
  - （任意）`Require branches to be up to date before merging` を一時的に無効化して段階導入を容易に（運用安定後に有効化を検討）
  - 例: `coverage-check` と `verify-lite` を必須チェックとして追加（段階導入時は `ci-non-blocking` を活用）
- 運用
  - PRではコメントに `Coverage (lines):` と `Threshold (effective):` を表示（`/coverage <pct>` で上書き可能）
  - main への push 時は `COVERAGE_ENFORCE_MAIN=1` で強制。違反時は失敗。

コメント表示（整形）
- Threshold (effective)
- Derived: label > repo var > default（`coverage:<pct>` ラベルが最優先）
- Policy / Policy source（`enforce-coverage` ラベルまたは main+変数で強制）
- Docs: 本ページへのリンク

Tips
- PRで強制したい場合は `/enforce-coverage` ラベルを付与。
- しきい値の一時上書き: `/coverage <pct>`（例: 72）。クリア: `/coverage clear`。
- 詳細は `docs/quality/coverage-policy.md` も参照。

Glossary（表示用語の統一）
- Derived: `label > repo var > default`（しきい値の導出順）
- Policy: `enforced | report-only`
- Policy source: `enforced via label: enforce-coverage | enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)`

クイックチェックリスト（導入時）
- [ ] 変数 `COVERAGE_ENFORCE_MAIN` / `COVERAGE_DEFAULT_THRESHOLD` を設定
- [ ] Branch protection のステータスチェックに `coverage-check` を登録
- [ ] PRコメントに `Derived: label > repo var > default` と `Policy`/`Policy source` が表示されることを確認
- [ ] 観測期間を設け、Required化の閾値/対象を最終決定

備考
- しきい値の決定は「ラベル > リポジトリ変数 > 既定(80)」の順で導出。
- main Required 化は一度運用して観測した上で合意のもと有効化することを推奨。
