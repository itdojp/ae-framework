---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# ADMIN_TOKEN Setup Guide (Fine-grained PAT)

このドキュメントは、Branch Protection のプリセット適用ワークフローで使用する `ADMIN_TOKEN` の作成・登録手順をまとめたものです。通常のCIやPR作成では使用しません。

> Language / 言語: English | 日本語

## English

This guide defines how to create and register `ADMIN_TOKEN` for the Branch Protection preset-apply workflow. It is not used for normal CI, PR creation, or day-to-day development automation.

### Purpose

- prepare the minimum-permission token required to read and update branch protection settings through the GitHub API
- keep branch protection changes codified in preset files such as `.github/branch-protection.*.json` and apply them through a controlled workflow

### Recommended method

- use a Fine-grained personal access token (FG-PAT)
  - repository scope: limit access to the single target repository (`Only select repositories`)
  - permission: `Repository permissions -> Administration -> Read and write`
  - expiration: keep it short and rotate regularly

### FG-PAT creation steps

1. GitHub -> `Settings` -> `Developer settings` -> `Fine-grained personal access tokens` -> `Generate new token`
2. Set `Resource owner` to the target organization (for example, `<organization-name>`)
3. Under `Repository access`, select `Only select repositories`, then choose `<organization-name>/<repository-name>`
4. Under `Repository permissions`, enable `Administration -> Read and write`
5. Set the token name and expiry, then generate the token
6. If the organization uses SSO, complete the SSO authorization step

### Register it as an Actions secret

1. Repository -> `Settings` -> `Secrets and variables` -> `Actions` -> `New repository secret`
2. Name: `ADMIN_TOKEN`
3. Value: the FG-PAT generated in the previous section

### Where the token is used

- `.github/workflows/branch-protection-apply.yml`
  - passes `ADMIN_TOKEN` to `gh api` as `GH_TOKEN` when an operator applies a branch protection preset manually
- `scripts/admin/apply-branch-protection.mjs`
  - reads `ADMIN_TOKEN` (or `GITHUB_TOKEN`) for local admin fallback operations

Boundary:
- do not reuse this token for normal PR checks, merge automation, or routine CI jobs
- keep the token limited to branch protection administration only

### FAQ

- Q. Is this token used for PR creation or normal CI?
  - A. No. It is reserved for branch protection administration. Normal CI and PR operations continue to use the existing repository and workflow permissions.
- Q. Can I keep multiple admin tokens?
  - A. Yes. You can register additional secrets such as `ADMIN_TOKEN_2` and add fallback handling in the workflow if that operating model is required.
- Q. Can we use a GitHub App instead of a PAT?
  - A. Yes. An installation token from a GitHub App with repository administration write permission can also apply the presets. That is often preferable for larger organizations.

### Security operation notes

- keep the scope minimal: one repository, one administrative purpose
- use the shortest practical expiry and rotate on a fixed schedule
- limit who can trigger the preset-apply workflow
- if stronger change control is needed, add Environment protection or a separate approval step for the workflow

## 日本語

## 目的
- GitHub API でブランチ保護設定（GET/PUT）を行うために、最小権限のアクセストークンを準備する
- 設定はコード化されたプリセット（`.github/branch-protection.*.json`）で管理し、ワークフローから適用できるようにする

## 方式（推奨）
- Fine-grained personal access token（FG-PAT）を使用
  - 対象リポジトリ: `<repository-name>` のみに限定（Only select repositories）
  - 権限: Repository permissions → Administration → Read and write
  - 期限: 短め（定期ローテーション推奨）

## 作成手順（FG-PAT）
1. GitHub → Settings → Developer settings → Fine-grained personal access tokens → Generate new token
2. Resource owner: 当該組織（例: `<organization-name>`）
3. Repository access: Only select repositories → `<organization-name>/<repository-name>` を選択
4. Repository permissions: Administration → Read and write を有効化
5. Token name/expiry を設定し、発行
6. （組織がSSO運用の場合）SSO承認を実施

## リポジトリへの登録（Actions Secret）
1. リポジトリ → Settings → Secrets and variables → Actions → New repository secret
2. Name: `ADMIN_TOKEN`
3. Value: 先ほど発行した FG-PAT の値

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
