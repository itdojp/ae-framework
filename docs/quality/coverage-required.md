# Coverage Required — Enabling on main

This note explains how to enable coverage enforcement on `main` with minimal friction.

Prereqs
- Workflow: `.github/workflows/coverage-check.yml` (already present)
- Variables: repository variables are used to derive policy and threshold

Steps
1) Settings → Variables → Repository variables に以下を設定
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`（例: `80`）
2) Branch protection で Required checks に `coverage-check / gate` や `coverage-check / coverage` を追加（運用ポリシーに応じて）
3) 一定期間、Note/PRコメントのみで観測してから Required を有効化（推奨）

Derivation (recap)
- Effective threshold は以下の優先順で決まります
  1. ラベル `coverage:<pct>`（例: `coverage:75`）
  2. 変数 `COVERAGE_DEFAULT_THRESHOLD`
  3. 既定 `80`

FAQ
- Q: PRで失敗することはある？
  - A: 既定は report-only。`/enforce-coverage` ラベル、または `main` への push かつ `COVERAGE_ENFORCE_MAIN=1` 設定時のみブロッキングになります。
- Q: どのチェックを Required にすべき？
  - A: `coverage-check / gate` （方針導出）と `coverage-check / coverage`（実測値）を推奨。運用に合わせて選択してください。

See also
- `docs/quality/coverage-policy.md`（ポリシー詳細、表示例）

