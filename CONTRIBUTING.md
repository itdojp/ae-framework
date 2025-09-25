# Contributing Guide / コントリビューションガイド

> 🌍 Language / 言語: English | 日本語

---

## English

### CI/PR Labels — Quick Reference
| Label | Effect | Example |
|---|---|---|
| enforce-artifacts | Artifacts validation becomes blocking | enforce-artifacts |
| enforce-testing | Property/Replay/BDD lint become blocking | enforce-testing |
| enforce-coverage | Coverage threshold becomes blocking | enforce-coverage |
| coverage:<pct> | Set coverage threshold (%) | coverage:85 |
| trace:<id> | Focus property/replay runs | trace:inv-001 |
| pr-summary:detailed | Show detailed PR summary | pr-summary:detailed |
| lang:ja / lang:en | PR summary language | lang:ja |

### How to Contribute
1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Submit a pull request

### Code Standards
- Follow existing code style
- Add tests for new features
- Update documentation
 - CI workflow snippets: when appending to GitHub special files, use printf with quoted targets (policy enforced in CI):
   - `printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"`
   - `printf "%s\n" "NAME=value" >> "$GITHUB_ENV"`
   - Grouped appends are allowed:
     ```bash
     {
       printf "%s\n" "one=1"
       printf "%s\n" "two=2"
     } >> "$GITHUB_OUTPUT"
     ```
   - See docs/ci-policy.md for details

### Package Manager Policy (pnpm)
- Node.js: 20.x (per `package.json#engines`)
- Install: `pnpm install`
- Development: run scripts with `pnpm` (e.g., `pnpm dev`)
- npm lockfile generation is disabled (`.npmrc` `package-lock=false`); do not commit `package-lock.json`.

pnpm setup:
```bash
# Recommended: use Corepack
corepack enable
corepack prepare pnpm@latest --activate

# Or install globally
npm i -g pnpm
```

This is a monorepo; prefer `pnpm --filter` for workspace commands (e.g., `pnpm --filter @ae-framework/ui build`).

---

## 日本語

### CI/PR ラベル — 早見表
| ラベル | 効果 | 例 |
|---|---|---|
| enforce-artifacts | アーティファクト検証をブロッキングに | enforce-artifacts |
| enforce-testing | Property/Replay/BDD Lint をブロッキングに | enforce-testing |
| enforce-coverage | カバレッジ閾値をブロッキングに | enforce-coverage |
| coverage:<pct> | カバレッジ閾値（%）を設定 | coverage:85 |
| trace:<id> | Property/Replay 実行を特定トレースに集中 | trace:inv-001 |
| pr-summary:detailed | 詳細な PR サマリを表示 | pr-summary:detailed |
| lang:ja / lang:en | PR サマリの言語指定 | lang:ja |

### 貢献方法
1. リポジトリをフォーク
2. フィーチャーブランチを作成
3. 変更を実装
4. プルリクエストを送信

### コーディング標準
- 既存のコードスタイルに従う
- 新機能にはテストを追加
- ドキュメントを更新
 - CI ワークフローのスニペット: `$GITHUB_OUTPUT` や `$GITHUB_ENV` に追記する際は `printf` と引用付きリダイレクトを使用（CI でポリシーを強制）
   - `printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"`
   - `printf "%s\n" "NAME=value" >> "$GITHUB_ENV"`
   - まとまった追記は以下のようにグループ化可能:
     ```bash
     {
       printf "%s\n" "one=1"
       printf "%s\n" "two=2"
     } >> "$GITHUB_OUTPUT"
     ```
   - 詳細は docs/ci-policy.md を参照

### パッケージマネージャ方針（pnpm）
- Node.js: 20.x 系（`package.json#engines` 準拠）
- インストール: `pnpm install`
- 開発: スクリプトは `pnpm` で実行（例: `pnpm dev`）
- npm の lockfile 生成は無効（`.npmrc` の `package-lock=false`）。`package-lock.json` はコミットしないでください。

pnpm の導入:
```bash
# 推奨: Corepack を使用
corepack enable
corepack prepare pnpm@latest --activate

# もしくはグローバルインストール
npm i -g pnpm
```

モノレポ構成のため、ワークスペースコマンドは `pnpm --filter` を活用してください（例: `pnpm --filter @ae-framework/ui build`）。
