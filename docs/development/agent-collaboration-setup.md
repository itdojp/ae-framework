# エージェント連携セットアップ手順（GitHub駆動・人手介在ゼロ）

本ドキュメントは、複数エージェント（PM/設計/実装）がGitHub上のシグナルのみで、計画→実装→レビュー→マージ→レポートまで自律連携するためのセットアップ手順です。前提として、各エージェントは同一PC（WSL上のUbuntu）で別ワークスペースとして稼働します。

## 前提
- リポジトリ管理者権限（Settings/Actions/Branch protection）
- gh CLI, git, Node.js/pnpm
- 各エージェントごとのワークスペース（例: `~/ws/pm-high`, `~/ws/arch-high`, `~/ws/impl-1` など）

## 1) GitHub 側セットアップ

### ラベル（役割/状態/スプリント/エピック）
作成例（gh CLI）:

```bash
gh label create "role:PM-HIGH" --color C2F5FF || true
gh label create "role:ARCH-HIGH" --color C2F5FF || true
gh label create "role:IMPL-MED-1" --color C2F5FF || true
gh label create "role:IMPL-MED-2" --color C2F5FF || true
gh label create "role:IMPL-MED-3" --color C2F5FF || true

gh label create "status:ready" --color D4F8D4 || true
gh label create "status:in-progress" --color FFE8A3 || true
gh label create "status:review" --color A3D8FF || true
gh label create "status:blocked" --color FFBCBC || true
gh label create "status:done" --color CCCCCC || true

gh label create "sprint:0" --color EAEAEA || true
gh label create "sprint:1" --color EAEAEA || true
gh label create "sprint:2" --color EAEAEA || true
gh label create "sprint:3" --color EAEAEA || true

# 必要に応じて epic ラベル（省略可。Issue本文内で参照でも可）
gh label create "epic:#898" --color EAEAEA || true
gh label create "epic:#701" --color EAEAEA || true
gh label create "epic:#786" --color EAEAEA || true
gh label create "epic:#879" --color EAEAEA || true
```

### マイルストーン（スプリント）
```bash
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 0' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 1' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 2' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 3' -f state='open' || true
```

### ブランチ保護（main）
- 必須チェック: quality/DoD/CODEOWNERS 承認
- Settings → Branches → Branch protection rules で設定

### CODEOWNERS（レビュー経路）
`.github/CODEOWNERS`（例）:
```
policy/**            @org/arch-team
quality/**           @org/arch-team
packages/spec-compiler/** @org/arch-team
docs/**              @org/pm-team
```

### PRテンプレート
`.github/pull_request_template.md` に目的/スコープ/AC/影響/リスク/FF/関連Issue のチェック欄を用意

### GitHub Actions（最小）
- triage.yml（issue_labeled/edited）: 役割→自動アサイン、状態ラベル遷移、Projects列移動
- slash-commands.yml（issue_comment）: `/start`, `/ready-for-review`, `/block` などを解釈
- pr-quality.yml（pull_request）: `pnpm i` → `ae quality run` → 要約コメント + 必須チェック
（aggregator/model-eval 導入後に progress-summary.yml / model-eval.yml を追加）

> 注意: Actions の権限を Settings → Actions → General で "Read and write permissions" に設定してください。

## 2) レポジトリ構成（推奨最小）
- `.github/CODEOWNERS`
- `.github/pull_request_template.md`
- `.github/workflows/triage.yml`
- `.github/workflows/slash-commands.yml`
- `.github/workflows/pr-quality.yml`
- `policy/quality.json`（DoD 合成ゲートを段階導入: warn → block）

## 3) 各エージェントのワークスペース準備（WSL）

共通セットアップ:
```bash
mkdir -p ~/ws/{pm-high,arch-high,impl-1,impl-2,impl-3}
cd ~/ws/impl-1 && gh repo clone itdojp/ae-framework
git config user.name "agent-impl-1"
git config user.email "agent-impl-1@example.invalid"
gh auth login   # repo/workflow scope

export GH_REPO=itdojp/ae-framework
export AGENT_ROLE="role:IMPL-MED-1"
# 必要に応じて
export AE_FEATURE_RECONCILE=1
```

役割と主担当:
- PM-HIGH（gpt-5 high）: 優先度/スプリント/承認、#898へ週次サマリ
- ARCH-HIGH（gpt-5 high）: 設計/RFC/IF定義、難所レビュー/承認
- IMPL-MED-1/2/3（gpt-5 medium）: 子Issue実装/テスト/CI/Docs/相互レビュー

## 4) スラッシュコマンド運用（自動連携）
- `/start` → status:in-progress + Draft PR 作成 + assignee 設定
- `/plan` → PR本文にチェックリスト挿入
- `/ready-for-review` → status:review + CODEOWNERS 呼び出し
- `/approve-arch` `/approve-pm` → 承認揃えばマージキュー
- `/block <reason>` `/unblock` → Blocked/解除

## 5) ローカルウォッチャー（任意）
各エージェントが自分のキューを自動取得するシンプルなポーラ例:
```bash
#!/usr/bin/env bash
set -euo pipefail
while true; do
  gh issue list --repo "$GH_REPO" \
    --label "$AGENT_ROLE" --label status:ready \
    --json number,title,url | jq -r '.[] | .number' | while read -r N; do
      gh issue comment "$N" --body "/start"
      # ブランチ作成/Draft PRはActions側で行う前提。必要ならここでgh pr createも可能。
    done
  sleep 60
done
```

## 6) ガードレール/ベストプラクティス
- ブランチ: `feat/<issue>-<slug>`、PRは ≤300行程度で小さく刻む
- コミット: Conventional Commits + `Refs #<issue>`
- DoD: policy の合成ゲートを必須（初期は warn 運用→安定後 block）
- 衝突回避: 新規ファイル追加 + 最小フック。安定後に内蔵

## 7) 動作確認（クイック）
1. ラベル/マイルストーン作成
2. 子Issueに `status:ready` + 役割ラベルを付与
3. `/start` → Draft PR → `pr-quality.yml` が走りPRに要約
4. `/ready-for-review` → CODEOWNERSレビュー → 承認 → マージ → Issue Close

## 8) トラブルシュート
- Actions 権限不足 → Repository Settings → Actions → General → "Read and write permissions"
- CODEOWNERS 無効 → パス/チーム名の確認、ブランチ保護の必須レビュー設定
- PRチェック未付与 → `pr-quality.yml` の存在/トリガ、workflow permissions

