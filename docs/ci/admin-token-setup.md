# ADMIN_TOKEN Setup Guide (Fine‑grained PAT)

このドキュメントは、Branch Protection のプリセット適用ワークフローで使用する `ADMIN_TOKEN` の作成・登録手順をまとめたものです。通常のCIやPR作成では使用しません。

## 目的
- GitHub API でブランチ保護設定（GET/PUT）を行うために、最小権限のアクセストークンを準備する
- 設定はコード化されたプリセット（`.github/branch-protection.*.json`）で管理し、ワークフローから適用できるようにする

## 方式（推奨）
- Fine‑grained personal access token（FG‑PAT）を使用
  - 対象リポジトリ: `ae-framework` のみに限定（Only select repositories）
  - 権限: Repository permissions → Administration → Read and write
  - 期限: 短め（定期ローテーション推奨）

## 作成手順（FG‑PAT）
1. GitHub → Settings → Developer settings → Fine‑grained personal access tokens → Generate new token
2. Resource owner: 当該組織（例: <organization-name>）
3. Repository access: Only select repositories → `<organization-name>/ae-framework` を選択
4. Repository permissions: Administration → Read and write を有効化
5. Token name/expiry を設定し、発行
6. （組織がSSO運用の場合）SSO承認を実施

## リポジトリへの登録（Actions Secret）
1. リポジトリ → Settings → Secrets and variables → Actions → New repository secret
2. Name: `ADMIN_TOKEN`
3. Value: 先ほど発行した FG‑PAT の値

## 使用箇所
- `.github/workflows/branch-protection-apply.yml`
  - 手動実行で `ADMIN_TOKEN` を `GH_TOKEN` として `gh api` に渡し、プリセットを適用
- `scripts/admin/apply-branch-protection.mjs`
  - ローカルから適用する場合、環境変数 `ADMIN_TOKEN`（または `GITHUB_TOKEN`）を参照

## よくある質問（FAQ）
- Q. このトークンはPR作成やCI全体で使われますか？
  - A. いいえ。ブランチ保護の適用にのみ使用します。通常のCI/PRは従来どおりの権限で動作します。
- Q. 複数のトークンを使い分けたい
  - A. Secretsに `ADMIN_TOKEN_2` などを追加し、ワークフロー側でフォールバック実装が可能です。必要であればテンプレートを追加します。
- Q. PATではなくGitHub Appを使えますか？
  - A. 可能です。Repository administration: write を付与したAppのInstallation Tokenでも適用できます（大規模運用ではApp推奨）。

## セキュリティ運用
- 最小権限・最小範囲（単一リポ）・短期有効期限・定期ローテーション
- ワークフローの実行者を限定（必要なら Environment 保護で承認フロー）

