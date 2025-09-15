# ae-framework Quick Start Guide

> 🌍 Language / 言語: English | 日本語

## 📦 インストール

```bash
# リポジトリのクローン
git clone https://github.com/itdojp/ae-framework.git
cd ae-framework

# 依存関係のインストール
npm install

# ビルド
npm run build
npm run build:cli

# グローバルインストール（オプション）
npm link
```

## 🚀 5分で始める ae-framework

### Step 1: プロジェクトの初期化

```bash
# 新しいプロジェクトディレクトリを作成
mkdir my-awesome-project
cd my-awesome-project

# ae-frameworkプロジェクトを初期化
ae-phase init --name 'My Awesome Project'
```

### Step 2: Steering Documentsの作成

```bash
# Steering Documentsディレクトリを作成
mkdir -p .ae/steering

# プロダクトビジョンを定義
cat > .ae/steering/product.md << EOF
# Product Vision

## Vision Statement
革新的なタスク管理アプリケーション

## Target Users
- 個人ユーザー
- 小規模チーム

## Core Features
1. タスクの作成と管理
2. カテゴリ分類
3. 期限管理
EOF

# アーキテクチャを定義
cat > .ae/steering/architecture.md << EOF
# Architecture Decisions

## Technology Stack
- Language: TypeScript
- Framework: Express.js
- Database: PostgreSQL

## Architecture Pattern
- RESTful API
- MVC Pattern
EOF

# コーディング標準を定義
cat > .ae/steering/standards.md << EOF
# Coding Standards

## Naming Conventions
- Classes: PascalCase
- Functions: camelCase
- Constants: UPPER_SNAKE_CASE

## Testing Requirements
- Minimum coverage: 80%
- Test-first development
EOF
```

### Step 3: インタラクティブ開発の開始

```bash
# Slash Commandsのインタラクティブモードを起動
ae-slash interactive
```

インタラクティブモードで以下のコマンドを実行：

```
ae> /status
# 現在のプロジェクト状態が表示される

ae> /intent Users can create tasks with title and description
# 要件を分析して抽出

ae> /complete requirements.md
# Intent フェーズを完了

ae> /approve Phase completed successfully
# フェーズを承認

ae> /next
# 次のフェーズ（Formal）へ移行

ae> /timeline
# 進捗タイムラインを表示
```

### Step 4: 承認ワークフローの活用

```bash
# 別のターミナルで承認状態を確認
ae-approve pending

# フェーズの承認
ae-approve approve formal --user "Tech Lead" --notes "Specifications approved"

# 承認履歴の確認
ae-approve history formal
```

## 📋 基本的なコマンドリファレンス

### Phase Management (ae-phase)

| コマンド | 説明 |
|---------|------|
| `ae-phase init --name "Project"` | プロジェクトを初期化 |
| `ae-phase status` | 現在の状態を表示 |
| `ae-phase timeline` | タイムラインを表示 |
| `ae-phase complete <phase>` | フェーズを完了 |
| `ae-phase next` | 次のフェーズへ移行 |

### Approval Workflow (ae-approve)

| コマンド | 説明 |
|---------|------|
| `ae-approve request <phase>` | 承認をリクエスト |
| `ae-approve approve <phase>` | フェーズを承認 |
| `ae-approve pending` | 保留中の承認を表示 |
| `ae-approve status <phase>` | 承認状態を確認 |

### Slash Commands (ae-slash)

| コマンド | 説明 |
|---------|------|
| `ae-slash interactive` | インタラクティブモード起動 |
| `ae-slash exec "/command"` | 単一コマンド実行 |
| `ae-slash sequence /cmd1 /cmd2` | コマンドシーケンス実行 |
| `ae-slash list` | 利用可能なコマンド一覧 |

## 🎯 典型的な開発フロー

### 1. 要件定義（Intent Phase）

```bash
ae-slash i
ae> /intent Create a REST API for user management
ae> /intent Users can register with email and password
ae> /intent Users can login and receive JWT token
ae> /complete requirements.md user-stories.md
ae> /approve Requirements reviewed and approved
ae> /next
```

### 2. 仕様作成（Formal Phase）

```bash
ae> /formal openapi
# OpenAPI仕様が生成される
ae> /complete api-spec.yaml
ae> /approve API design approved
ae> /next
```

### 3. テスト作成（Test Phase）

```bash
ae> /test src/user-controller.ts unit
# ユニットテストが生成される
ae> /complete user-controller.test.ts
ae> /next
```

### 4. 実装（Code Phase）

```bash
ae> /code user-controller.test.ts
# テストを満たすコードが生成される
ae> /complete src/user-controller.ts
ae> /next
```

### 5. 検証（Verify Phase）

```bash
ae> /verify
# 全テストとカバレッジチェック
ae> /complete verification-report.md
ae> /next
```

### 6. 運用（Operate Phase）

```bash
ae> /operate deploy production
# デプロイメント実行
ae> /operate monitor
# メトリクス監視
```

## 🔍 ヒントとコツ

### 1. エイリアスを活用

```bash
ae-slash i
ae> /s      # /status のエイリアス
ae> /i      # /intent のエイリアス
ae> /n      # /next のエイリアス
ae> /a      # /approve のエイリアス
```

### 2. コマンドシーケンスでワークフローを自動化

```bash
# 一連のコマンドを一度に実行
ae-slash sequence "/init MyProject" "/complete" "/approve" "/next"
```

### 3. Steering Documentsを最新に保つ

```bash
# Steering Documentsの確認
ae-slash exec "/steering"

# 特定のドキュメントを読み込み
ae-slash i
ae> /steering load product
ae> /steering context
```

### 4. 承認ポリシーのカスタマイズ

```bash
# 重要なフェーズに複数承認者を設定
ae-approve set-policy code --multiple --min-approvers 2

# 自動承認条件を設定
ae-approve set-policy test --auto-test --auto-security
```

## 🆘 トラブルシューティング

### プロジェクトが見つからない

```bash
# 状態ファイルの確認
ls -la .ae/phase-state.json

# プロジェクトの再初期化
ae-phase reset --force
ae-phase init --name "My Project"
```

### コマンドが認識されない

```bash
# 利用可能なコマンドを確認
ae-slash list

# 特定コマンドのヘルプ
ae-slash help /intent
```

### 承認が期限切れ

```bash
# 期限切れ承認のクリーンアップ
ae-approve check-expired

# 新しい承認リクエスト
ae-approve request <phase> --summary "Re-requesting approval"
```

## 📚 次のステップ

- [新機能ガイド](./NEW_FEATURES.md) - 各機能の詳細な使用方法
- [API リファレンス](./API.md) - プログラマティックアクセス
- [ベストプラクティス](./BEST_PRACTICES.md) - 効果的な使用方法
- [コントリビューション](../CONTRIBUTING.md) - プロジェクトへの貢献方法

## 💬 サポート

問題が発生した場合は：
1. [Issues](https://github.com/itdojp/ae-framework/issues) で報告
2. [Discussions](https://github.com/itdojp/ae-framework/discussions) で質問
3. ドキュメントの [FAQ](./FAQ.md) を確認
