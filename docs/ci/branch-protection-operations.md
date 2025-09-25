# Branch Protection Operations (One-person + AI friendly)

このリポジトリでは、運用状況に応じて main ブランチの保護設定を JSON プリセットで切替できるよう、次の仕組みを用意しています。

## 目的
- 「At least 1 approving review is required」を不要にし、1人 + AI のワークフローでも詰まらないようにする
- レビュー必須を外しても、軽量で決定的な Required checks を維持して品質を担保する

## プリセット一覧（.github/ 配下）
- `branch-protection.main.restore.json` … 既定（レビュー必須: 1、`PR Verify / verify` required）
- `branch-protection.main.relax.json` … 軽く緩和（レビュー1件維持・他条件緩め）
- `branch-protection.main.relax2.json` … レビュー要件なし（required_pull_request_reviews: null）
- `branch-protection.main.require-verify-lite.json` … `Verify Lite / verify-lite` を Required に（レビュー1件あり）
- `branch-protection.main.verify-lite-noreview.json` … `Verify Lite / verify-lite` Required、レビュー要件なし（推奨）
  - さらに `Copilot Review Gate / gate` も Required に含め、Copilot指摘の存在と解決を強制

## 切替方法（推奨: GitHub Actions 手動ディスパッチ）
1. リポジトリに `ADMIN_TOKEN`（repo admin scope の PAT）を登録
   - Settings → Secrets and variables → Actions → New repository secret → Name: `ADMIN_TOKEN`
2. Actions → 「Admin — Apply Branch Protection Preset」→ Run workflow
   - preset: `branch-protection.main.verify-lite-noreview.json`（推奨）
   - branch: `main`

実行ログに、更新前/更新後の `required_pull_request_reviews` と `required_status_checks` が表示されます。

## ローカルからの適用（Node スクリプト）
```bash
cd ae-framework
ADMIN_TOKEN=ghp_xxx REPO=itdojp/ae-framework BRANCH=main \
  node scripts/admin/apply-branch-protection.mjs .github/branch-protection.main.verify-lite-noreview.json
```

## 運用指針（レビューを外す代替ガード）
- Branch protection: Required checks を維持（`Verify Lite / verify-lite` + `Copilot Review Gate / gate` を推奨）
- Auto-merge を許可（Checks が緑になれば自動マージ）
- ラベルで強制ゲートを任意化（`enforce-coverage`, `enforce-typecov` など）

## 参考
- 必要になれば Auto-Approve のワークフローも導入可能（PAT が必要）。レビュー要件を残したまま、特定ラベルや特定作者の PR を自動承認する運用にできます。
