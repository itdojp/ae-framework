# Windows Installation Troubleshooting Guide

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Comprehensive troubleshooting guide for Windows installation issues with AE Framework**

### 🔍 Known Issues

#### Issue #1: TypeScript Build Failures

**Symptoms:**
- 600+ TypeScript compilation errors during `pnpm run build`
- `TS6059` rootDir configuration errors
- `TS2532` undefined object access errors

**Root Cause:**
- Monorepo structure conflicts with TypeScript `rootDir` configuration
- Strict null checking enabled causing compatibility issues

**Solutions:**

##### Option A: Use Windows-specific Build (Recommended)
```bash
# Use the relaxed TypeScript configuration for Windows
pnpm run build:windows
```

##### Option B: Temporary TypeScript Configuration
Create a temporary `tsconfig.local.json`:
```json
{
  "extends": "./tsconfig.json",
  "compilerOptions": {
    "rootDir": ".",
    "strict": false,
    "noUncheckedIndexedAccess": false
  },
  "include": ["src/**/*", "packages/**/*"]
}
```

Then build with:
```bash
npx tsc --project tsconfig.local.json
```

#### Issue #2: Git Hooks Setup Failure

**Symptoms:**
- `'cp' is not recognized as an internal or external command`
- `setup-hooks` script fails on Windows

**Root Cause:**
- Unix-specific commands (`cp`, `chmod`) not available in Windows Command Prompt

**Solution:**
```bash
# Use the cross-platform Node.js script
pnpm run setup-hooks

# Or use the original Unix script in Git Bash/WSL
pnpm run setup-hooks:unix
```

### 🛠️ Step-by-Step Windows Installation

#### Prerequisites
- **Node.js 18+**
- **Git for Windows** (includes Git Bash)
- **pnpm**（Corepack を使用: `corepack enable`）

#### Installation Steps

1. **Clone Repository**
   ```bash
   git clone https://github.com/itdojp/ae-framework.git
   cd ae-framework
   ```

2. **Install Dependencies**
   ```bash
   pnpm install
   ```

3. **Setup Playwright** (Optional for testing)
   ```bash
   npx playwright install
   ```

4. **Build with Windows Configuration**
   ```bash
   pnpm run build:windows
   ```

5. **Setup Git Hooks**
   ```bash
   pnpm run setup-hooks
   ```

6. **Verify Installation**
   ```bash
   # Test basic CLI functionality
   node dist/cli/index.js --help
   ```

### 🔧 Alternative Installation Methods

#### Method 1: WSL (Windows Subsystem for Linux)
```bash
# Install WSL2 with Ubuntu
wsl --install

# Run standard Linux installation in WSL
pnpm install
pnpm run build
```

#### Method 2: Git Bash Environment
```bash
# Use Git Bash for Unix-like commands
pnpm run setup-hooks:unix
```

#### Method 3: Podman Development Environment
```bash
# Use the Podman-based development stack
podman compose -f podman/compose.test.yaml up --detach
# Verify containers
podman ps --filter "name=ae-framework"
```
> ℹ️ Docker Desktop を利用する場合は `docker compose -f podman/compose.test.yaml up` に置き換えて実行できます。

### ⚠️ Known Limitations on Windows

1. **File Path Length**: Windows has a 260-character path limit that may affect deeply nested files
2. **Case Sensitivity**: Git case sensitivity issues may occur
3. **Line Endings**: CRLF vs LF line ending differences

#### Recommendations:
- Enable long path support: `git config --system core.longpaths true`
- Configure line endings: `git config --global core.autocrlf true`
- Use Git Bash for command-line operations when possible

### 🐛 Common Error Solutions

#### Error: "Cannot find module 'xyz'"
```bash
# Clear node modules and reinstall
rm -rf node_modules
pnpm install
```

#### Error: "Permission denied" during hooks setup
```bash
# Run as Administrator or use Git Bash
# Ensure execution policy allows script running
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

#### Error: TypeScript "Cannot write file" errors
```bash
# Clear TypeScript cache and output directory
rm -rf dist
pnpm run build:windows
```

### 📚 Additional Resources

- [Node.js Windows Installation](https://nodejs.org/en/download/)
- [Git for Windows](https://gitforwindows.org/)
- [WSL Installation Guide](https://docs.microsoft.com/en-us/windows/wsl/install)
- [pnpm Installation](https://pnpm.io/installation)

### 🔍 Getting Help

If you continue to experience issues:

1. **Check the GitHub Issues**: Look for existing Windows-related issues
2. **Create a Detailed Issue**: Include your full error log and system information
3. **Join the Discussion**: Community support for installation issues

---

## Japanese

**AE FrameworkのWindows インストール問題に関する包括的なトラブルシューティングガイド**

### 🔍 既知の問題

#### 問題 #1: TypeScript ビルド失敗

**症状:**
- `pnpm run build` 実行時に600以上のTypeScriptコンパイルエラー
- `TS6059` rootDir設定エラー
- `TS2532` undefined オブジェクトアクセスエラー

**根本原因:**
- モノレポ構造がTypeScript `rootDir`設定と競合
- 厳密なnullチェックが有効化されて互換性問題が発生

**解決方法:**

##### オプション A: Windows専用ビルドを使用（推奨）
```bash
# Windows用の緩和されたTypeScript設定を使用
pnpm run build:windows
```

##### オプション B: 一時的なTypeScript設定
一時的な `tsconfig.local.json` を作成:
```json
{
  "extends": "./tsconfig.json",
  "compilerOptions": {
    "rootDir": ".",
    "strict": false,
    "noUncheckedIndexedAccess": false
  },
  "include": ["src/**/*", "packages/**/*"]
}
```

そして以下でビルド:
```bash
npx tsc --project tsconfig.local.json
```

#### 問題 #2: Git フック設定失敗

**症状:**
- `'cp' は内部コマンドまたは外部コマンドとして認識されていません`
- Windows で `setup-hooks` スクリプトが失敗

**根本原因:**
- Unix固有のコマンド（`cp`、`chmod`）がWindowsコマンドプロンプトで利用不可

**解決方法:**
```bash
# クロスプラットフォームNode.jsスクリプトを使用
pnpm run setup-hooks

# またはGit Bash/WSLで元のUnixスクリプトを使用
pnpm run setup-hooks:unix
```

### 🛠️ Windows段階的インストール

#### 前提条件
- **Node.js 18+**
- **Git for Windows** (Git Bashを含む)
- **pnpm**（Corepack を使用: `corepack enable`）

#### インストール手順

1. **リポジトリのクローン**
   ```bash
   git clone https://github.com/itdojp/ae-framework.git
   cd ae-framework
   ```

2. **依存関係のインストール**
   ```bash
   pnpm install
   ```

3. **Playwright設定** (テスト用、オプション)
   ```bash
   npx playwright install
   ```

4. **Windows設定でビルド**
   ```bash
   pnpm run build:windows
   ```

5. **Git フック設定**
   ```bash
   pnpm run setup-hooks
   ```

6. **インストール検証**
   ```bash
   # 基本CLI機能をテスト
   node dist/cli/index.js --help
   ```

### 🔧 代替インストール方法

#### 方法 1: WSL (Windows Subsystem for Linux)
```bash
# Ubuntu付きWSL2をインストール
wsl --install

# WSL内で標準Linuxインストールを実行
pnpm install
pnpm run build
```

#### 方法 2: Git Bash環境
```bash
# Unix類似コマンドにGit Bashを使用
pnpm run setup-hooks:unix
```

#### 方法 3: Podman開発環境
```bash
# Podman ベースの開発スタックを起動
podman compose -f podman/compose.test.yaml up --detach
# コンテナの起動確認
podman ps --filter "name=ae-framework"
```
> ℹ️ Docker Desktop に切り替える場合は `docker compose -f podman/compose.test.yaml up` へ読み替えてください。

### ⚠️ Windows での既知の制限

1. **ファイルパス長**: Windowsには深くネストしたファイルに影響する可能性のある260文字のパス制限
2. **大文字小文字の区別**: Git大文字小文字区別の問題が発生する可能性
3. **改行コード**: CRLF vs LF改行コードの違い

#### 推奨事項:
- 長パスサポートを有効化: `git config --system core.longpaths true`
- 改行コードを設定: `git config --global core.autocrlf true`
- 可能な場合はコマンドライン操作にGit Bashを使用

### 🐛 一般的なエラー解決法

#### エラー: "Cannot find module 'xyz'"
```bash
# node modulesをクリアして再インストール
rm -rf node_modules
pnpm install
```

#### エラー: フック設定時の "Permission denied"
```bash
# 管理者として実行するかGit Bashを使用
# 実行ポリシーがスクリプト実行を許可することを確認
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

#### エラー: TypeScript "Cannot write file" エラー
```bash
# TypeScriptキャッシュと出力ディレクトリをクリア
rm -rf dist
pnpm run build:windows
```

### 📚 追加リソース

- [Node.js Windows インストール](https://nodejs.org/en/download/)
- [Git for Windows](https://gitforwindows.org/)
- [WSL インストールガイド](https://docs.microsoft.com/en-us/windows/wsl/install)
- [pnpm インストール](https://pnpm.io/installation)

### 🔍 ヘルプの取得

問題が続く場合:

1. **GitHub Issues を確認**: 既存のWindows関連問題を検索
2. **詳細な問題を作成**: 完全なエラーログとシステム情報を含める
3. **ディスカッションに参加**: インストール問題のコミュニティサポート

---

**🚀 Ready to develop with AE Framework on Windows! / Windows で AE Framework を使用した開発の準備が整いました！**
