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
- 運用
  - PRではコメントに `Coverage (lines):` と `Threshold (effective):` を表示（`/coverage <pct>` で上書き可能）
  - main への push 時は `COVERAGE_ENFORCE_MAIN=1` で強制。違反時は失敗。

Tips
- PRで強制したい場合は `/enforce-coverage` ラベルを付与。
- しきい値の一時上書き: `/coverage <pct>`（例: 72）。クリア: `/coverage clear`。
- 詳細は `docs/quality/coverage-policy.md` も参照。

備考
- しきい値の決定は「ラベル > リポジトリ変数 > 既定(80)」の順で導出。
- main Required 化は一度運用して観測した上で合意のもと有効化することを推奨。

