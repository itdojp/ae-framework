# ae-framework: AI-Agent Enabled Framework

> 人手最小＆仕様準拠最大。TDD強制機能付きIntent→Formal→Tests→Code→Verify→Operate の6フェーズ。

## 📢 最新アップデート
- **[🎯 Intent Agent 改善](./docs/TDD-FRAMEWORK-ARCHITECTURE.md)** - Claude Code Task Tool統合でMCP問題を解決
- **[🚀 クイックスタート](./docs/QUICK-START-GUIDE.md)** - 5分で始めるae-framework  
- **[📖 新機能ガイド](./docs/NEW_FEATURES.md)** - Steering Documents、Phase State Management、Approval Workflow、Slash Commandsの詳細な使用方法

## 🔧 Intent Agent 統合強化

### Claude Code Task Tool 統合（推奨）
ae-framework は Claude Code 環境で自動統合されており、追加設定なしで利用可能：

```
User: プロジェクトの要件分析をお願いします

Claude Code: Intent Task Adapterを使用して要件分析を実行します...

✅ Intent Analysis Complete - 12 requirements identified
📋 Next steps:
  • Proceed to Phase 2 (Formal Specification)
```

### CLI実行も強化
```bash
# Phase 1 Intent分析
ae-framework intent --analyze --sources="requirements.md"

# 完全性検証
ae-framework intent --validate

# フェーズチェック
ae-framework check --phase 1-intent
```

### ハイブリッドアプローチ
- **Claude Code**: Task Tool統合（最優先）
- **CLI**: コマンドライン環境
- **MCP**: フォールバック機能

詳細は [TDD Framework Architecture](./docs/TDD-FRAMEWORK-ARCHITECTURE.md) を参照。

## 🎯 主要機能

### 📚 [Steering Documents](./docs/NEW_FEATURES.md#-steering-documents)
プロジェクト全体のコンテキストと方向性を管理：
- **product.md**: プロダクトビジョン、ターゲットユーザー、コア機能
- **architecture.md**: 技術スタック、アーキテクチャパターン、システム構成  
- **standards.md**: コーディング規約、命名規則、品質基準

```bash
# クイックスタート
mkdir -p .ae/steering
echo '# Product Vision' > .ae/steering/product.md
```

### 📊 [Phase State Management](./docs/NEW_FEATURES.md#-phase-state-management)
6フェーズの進捗を自動追跡：
- 各フェーズの開始・完了・承認を記録
- プロジェクト全体の進捗率とタイムライン
- 成果物とメタデータの管理

```bash
# クイックスタート
ae-phase init --name 'My Project'
ae-phase status
ae-phase timeline
```

### ✅ [Approval Workflow](./docs/NEW_FEATURES.md#-approval-workflow)
フェーズ完了後の品質ゲート：
- 複数承認者のサポート
- 自動承認条件（テストカバレッジ、セキュリティスキャン）
- 承認期限とエスカレーション

```bash
# クイックスタート
ae-approve request intent --summary 'Ready for review'
ae-approve approve intent --user 'Tech Lead'
```

### 🚀 [Slash Commands](./docs/NEW_FEATURES.md#-slash-commands) 
統一されたコマンドインターフェース：
- インタラクティブモード（`ae-slash i`）
- 全フェーズのコマンド統合
- コマンドエイリアスとシーケンス実行

```bash
# クイックスタート
ae-slash interactive
ae> /init 'My Project'
ae> /status
ae> /next
```

## 🚀 開発ワークフロー

### 統合ワークフロー例
```bash
# 1. プロジェクト初期化
ae-phase init --name 'My Project'
mkdir -p .ae/steering

# 2. インタラクティブ開発
ae-slash i
ae> /init 'E-Commerce Platform'
ae> /intent Users can browse and purchase products
ae> /complete requirements.md
ae> /approve Ready for implementation
ae> /next

# 3. 進捗確認
ae-phase timeline
ae-approve pending
```

詳細は[新機能ガイド](./docs/NEW_FEATURES.md#-統合ワークフロー例)を参照してください。

## 🤖 AI-Powered Development Features

### 🤖 Test Generation Agent (NEW!)
自動的に包括的なテストを生成する AI エージェント：

- **要件からテスト生成**: 自然言語の要件から完全なテストスイートを作成
- **コードからテスト逆生成**: 既存コードを分析してテストを生成（リバースTDD）
- **Property-Based Testing**: 数学的性質からプロパティテストを自動設計
- **BDD シナリオ生成**: ユーザーストーリーから Gherkin シナリオを作成
- **セキュリティテスト**: OWASP ガイドラインに基づくセキュリティテスト生成
- **パフォーマンステスト**: SLA 要件からパフォーマンステストスイートを設計

```bash
# MCP サーバーとして起動
npm run mcp:test-gen

# 使用例
{
  "tool": "generate_tests_from_requirements",
  "args": {
    "feature": "User Authentication",
    "requirements": ["Users can login", "Password must be hashed"]
  }
}
```

### 🛡️ TDD Enforcement Features
TDD（Test-Driven Development）原則の遵守を自動的に強制：

### 🛡️ TDD Guards
- **TDD Guard**: コードファイルに対応するテストファイルの存在を強制
- **Test Execution Guard**: コミット前の全テスト通過を確認
- **RED-GREEN Cycle Guard**: RED→GREEN→REFACTORサイクルの遵守をチェック
- **Coverage Guard**: 最低カバレッジ（80%）の維持を監視

### 📋 Phase Validation
各フェーズで必要な成果物とバリデーションを自動チェック：
- **Phase 3 (Tests)**: テストが最初に失敗することを確認（RED phase）
- **Phase 4 (Code)**: 実装後にテストが通ることを確認（GREEN phase）
- **Phase 5 (Verify)**: 全テストスイート実行とカバレッジ確認

### 🔧 CLI Tools
```bash
# 現在フェーズの要件をチェック
ae-framework check --phase 3-tests

# TDDルール違反の報告
ae-framework violations

# ゲート通過状況の確認
ae-framework status
```

## 🤖 AI Agents

### Phase 1: Intent Agent 🎯
要件と意図の分析を担当：
- 自然言語からの要件抽出
- ユーザーストーリー生成
- ドメインモデル構築
- 曖昧性検出と解決
- 要件の優先順位付け（MoSCoW）
- トレーサビリティマトリックス作成

### Phase 2: Formal Agent 📐
形式仕様とモデル検証を担当：
- OpenAPI/AsyncAPI仕様生成
- GraphQLスキーマ定義
- TLA+形式検証
- 状態遷移モデル作成
- ER図とデータフロー図生成
- B-Method/Z記法サポート

### Phase 3: Test Generation Agent 🧪
包括的なテスト生成を担当：
- 要件からのテスト自動生成
- Property-based testing設計
- BDDシナリオ作成（Gherkin）
- セキュリティテスト生成（OWASP準拠）
- パフォーマンステスト設計
- カバレッジ最適化

### Phase 4: Code Generation Agent 💻
実装コードの生成を担当：
- テスト駆動による実装生成
- デザインパターン適用
- リファクタリング提案
- ドキュメント生成
- エラーハンドリング実装

### Phase 5: Verify Agent ✅
品質検証と保証を担当：
- 全テストスイート実行
- カバレッジ分析（目標: 80%以上）
- 静的解析とlinting
- セキュリティスキャン
- パフォーマンステスト実行
- Mutation testing実行

### Phase 6: Operate Agent 🚀
運用とデプロイメントを担当：
- CI/CDパイプライン統合
- デプロイメント自動化
- モニタリング設定
- ログ収集と分析
- インシデント対応
- ロールバック管理

## 📦 Installation

```bash
# Node.js 20+ required
npm install

# Install Git hooks for TDD enforcement
npm run setup-hooks

# Build the framework
npm run build
```

## 🚀 Quick Start

```bash
# 1. Initialize a new project with TDD enforcement
ae-framework init my-project --tdd

# 2. Create a feature specification
ae-framework feature "User Authentication"

# 3. Generate tests (Phase 3 - RED)
ae-framework generate:tests

# 4. Generate implementation (Phase 4 - GREEN)
ae-framework generate:code

# 5. Verify quality (Phase 5)
ae-framework verify

# 6. Deploy (Phase 6)
ae-framework deploy
```

## 🧪 Testing

```bash
# Run all tests
npm test

# Run specific test types
npm run test:unit
npm run test:integration
npm run test:e2e
npm run test:property
npm run test:mutation

# Coverage report
npm run coverage
```

## 📊 Metrics & Monitoring

The framework tracks:
- **TDD Compliance**: RED-GREEN-REFACTOR cycle adherence
- **Test Coverage**: Line, branch, function coverage
- **Mutation Score**: Test effectiveness measure
- **Phase Completion**: Progress through 6 phases
- **Quality Gates**: Pass/fail status per phase

## 🔒 Security

- **OWASP Compliance**: Security tests based on OWASP guidelines
- **Dependency Scanning**: Automated vulnerability detection
- **Secret Management**: Environment-based configuration
- **Access Control**: Role-based permissions
- **Audit Logging**: Complete activity tracking

## 📚 Documentation

- [Architecture Guide](docs/architecture.md)
- [Agent API Reference](docs/api/agents.md)
- [TDD Enforcement Rules](docs/tdd-rules.md)
- [Configuration Options](docs/configuration.md)
- [Contributing Guide](CONTRIBUTING.md)

## 🤝 Contributing

We welcome contributions! Please see our [Contributing Guide](CONTRIBUTING.md) for details.

## 📄 License

MIT License - see [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

Built with:
- MCP SDK for agent communication
- OpenAI/Anthropic APIs for AI capabilities
- Vitest for testing framework
- Fast-check for property-based testing
- Stryker for mutation testing

---

**ae-framework** - Automating excellence through AI-driven development 🚀