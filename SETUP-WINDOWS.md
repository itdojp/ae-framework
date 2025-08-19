# Windows環境セットアップガイド

> ae-frameworkをWindows環境でセットアップする手順

## ⚠️ 重要

**ae-frameworkはpnpm workspacesを使用したmonorepo構成です。** 
npmではworkspace依存関係を解決できないため、**pnpmの使用が必須**です。

## 🚀 セットアップ手順

### 1. Node.js環境準備

#### Option A: fnm (推奨)
```powershell
# fnm インストール
winget install Schniz.fnm

# シェル再起動後
fnm install 20.19.4
fnm use 20.19.4
```

#### Option B: 公式インストーラー
- [Node.js v20.19.4+](https://nodejs.org/)をダウンロードしてインストール

### 2. pnpm インストール

```powershell
# corepack有効化（Node.js 16.13+）
corepack enable

# pnpm インストール確認
pnpm --version
```

または

```powershell
# 直接インストール
npm install -g pnpm@8.15.1
```

### 3. プロジェクトクローン

```powershell
git clone https://github.com/itdojp/ae-framework.git
cd ae-framework
```

### 4. 依存関係インストール

```powershell
# ✅ 正しい方法（pnpm使用）
pnpm install

# ❌ エラーが発生する方法（npm使用）
# npm install  # workspace:* エラーが発生
```

### 5. プロジェクトビルド

```powershell
# TypeScript ビルド
pnpm run build

# フロントエンドビルド
pnpm run build:frontend
```

### 6. 開発サーバー起動確認

```powershell
# メインCLI確認
pnpm ae-framework --help

# Web開発サーバー
pnpm run dev:web

# Storybookサーバー
pnpm run dev:storybook
```

## 🐞 よくある問題とトラブルシューティング

### 問題1: npm EUNSUPPORTEDPROTOCOL エラー

```
npm error Unsupported URL Type "workspace:": workspace:*
```

**解決方法**: npmの代わりにpnpmを使用
```powershell
# npm install ではなく
pnpm install
```

### 問題2: PowerShell実行ポリシーエラー

```
cannot be loaded because running scripts is disabled
```

**解決方法**: 実行ポリシーを一時的に変更
```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

### 問題3: パス長制限エラー

```
ENAMETOOLONG: name too long
```

**解決方法**: 
1. プロジェクトをC:ドライブルート近くに配置
2. LongPathsを有効化（Windows 10 Build 14352+）

### 問題4: ファイル監視制限

**解決方法**: ファイルシステム監視制限を増加
```powershell
# .npmrc または .yarnrc.yml に追加
max_old_space_size=8192
```

## 🔧 開発時の推奨設定

### VSCode設定 (.vscode/settings.json)

```json
{
  "typescript.preferences.includePackageJsonAutoImports": "on",
  "typescript.workspaceSymbols.scope": "currentProject",
  "npm.packageManager": "pnpm",
  "terminal.integrated.shell.windows": "pwsh.exe",
  "files.eol": "\\n",
  "git.autocrlf": false
}
```

### Git設定

```powershell
# 改行コード設定（重要）
git config core.autocrlf false
git config core.eol lf

# 長いパス名有効化
git config core.longpaths true
```

## 📦 パッケージ管理コマンド

```powershell
# 依存関係追加
pnpm add <package-name>

# 開発依存関係追加
pnpm add -D <package-name>

# workspace内パッケージ追加
pnpm add @ae-framework/ui --filter @ae-framework/web

# 依存関係更新
pnpm update

# 依存関係削除
pnpm remove <package-name>
```

## 🧪 テスト実行

```powershell
# 全テスト実行
pnpm test

# 高速テスト（一部除外）
pnpm run test:fast

# カバレッジ付きテスト
pnpm run test:coverage

# 個別テスト実行
pnpm test -- tests/specific.test.ts
```

## 🔍 デバッグ環境

### Node.js Inspector（VSCode）

`.vscode/launch.json`:
```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "Debug AE Framework",
      "type": "node",
      "request": "launch",
      "program": "${workspaceFolder}/dist/cli/index.js",
      "args": ["--help"],
      "console": "integratedTerminal",
      "skipFiles": ["<node_internals>/**"]
    }
  ]
}
```

## 🚀 次のステップ

セットアップ完了後：

1. **[クイックスタートガイド](./docs/getting-started/QUICK-START-GUIDE.md)** - 15分で基本機能を体験
2. **[開発指示ガイド](./docs/guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md)** - 実際の開発方法
3. **[Phase 6 ガイド](./docs/getting-started/PHASE-6-GETTING-STARTED.md)** - UI/UX機能の使用

## 🆘 サポート

問題が解決しない場合：

1. **Issue報告**: [GitHub Issues](https://github.com/itdojp/ae-framework/issues)
2. **環境情報収集**:
   ```powershell
   node --version
   pnpm --version
   git --version
   echo $env:OS
   ```

---

**Windows セットアップ完了！** 🎉 ae-frameworkを始めましょう。