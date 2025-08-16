# ae-framework: AI-Agent Enabled Framework

> 人手最小＆仕様準拠最大。TDD強制機能付きIntent→Formal→Tests→Code→Verify→Operate の6フェーズ。

## 📢 最新アップデート
- **[🚀 Phase 2-5 Claude Code Task Tool統合](./docs/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - 全フェーズの完全自動化を実現
- **[🎯 Intent Agent 改善](./docs/TDD-FRAMEWORK-ARCHITECTURE.md)** - Claude Code Task Tool統合でMCP問題を解決
- **[📝 自然言語要件処理](./docs/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md)** - Phase 2の包括的な要件分析機能
- **[📋 ユーザーストーリー自動生成](./docs/PHASE-3-USER-STORIES-CREATION.md)** - Phase 3のアジャイル開発サポート
- **[🔍 多層品質検証](./docs/PHASE-4-VALIDATION.md)** - Phase 4の包括的品質保証システム
- **[🏗️ ドメイン駆動設計](./docs/PHASE-5-DOMAIN-MODELING.md)** - Phase 5のDDDによる設計自動化

## 🔧 Claude Code Task Tool 統合（全フェーズ対応）

### 🚀 完全自動統合
ae-framework は Claude Code 環境で**全6フェーズ**を自動統合。追加設定なしで利用可能：

#### Phase 1: Intent Analysis 🎯
```
User: プロジェクトの要件分析をお願いします

Claude Code: Intent Task Adapterを使用して要件分析を実行します...

✅ Intent Analysis Complete - 12 requirements identified
📋 Next steps:
  • Proceed to Phase 2 (Natural Language Requirements)
```

#### Phase 2: Natural Language Requirements 📝
```
User: 要件を構造化してください

Claude Code: Natural Language Task Adapterを実行中...

✅ Requirements Analysis - 15 requirements identified
📊 Analysis:
  • Functional Requirements: 10
  • Non-Functional Requirements: 3
  • Business Requirements: 2
💡 Recommendations:
  • Review identified gaps for completeness
  • Clarify ambiguous requirements with stakeholders
```

#### Phase 3: User Stories Creation 📋
```
User: ユーザーストーリーを作成してください

Claude Code: User Stories Task Adapterで処理中...

✅ User Story Generation Complete - 8 stories created across 3 epics
📊 Analysis:
  • Total Stories: 8
  • Total Epics: 3
  • Total Story Points: 34
  • Completeness Score: 85%
```

#### Phase 4: Validation 🔍
```
User: 要件とストーリーの整合性を検証してください

Claude Code: Validation Task Adapterで検証中...

✅ Cross-Validation Complete - 90% alignment across phases
📊 Analysis:
  • Requirements-Stories alignment: 95%
  • Traceability coverage: 88%
  • Consistency score: 92%
```

#### Phase 5: Domain Modeling 🏗️
```
User: ドメインモデルを設計してください

Claude Code: Domain Modeling Task Adapterで設計中...

✅ Domain Analysis Complete - 6 entities, 2 bounded contexts identified
📊 Analysis:
  • Core Domain Entities: 4
  • Bounded Contexts: 2
  • Business Rules: 12
  • Domain Services: 3
```

### CLI実行も全フェーズ対応
```bash
# Phase 1: Intent分析
ae-framework intent --analyze --sources="requirements.md"
ae-framework intent --validate

# Phase 2: 自然言語要件処理
ae-framework natural-language --analyze
ae-framework natural-language --extract-entities
ae-framework natural-language --validate-completeness

# Phase 3: ユーザーストーリー管理
ae-framework user-stories --generate
ae-framework user-stories --validate
ae-framework user-stories --prioritize

# Phase 4: 検証ワークフロー
ae-framework validate --requirements
ae-framework validate --stories
ae-framework validate --traceability

# Phase 5: ドメインモデリング
ae-framework domain-model --analyze
ae-framework domain-model --entities
ae-framework domain-model --contexts
```

### ハイブリッドアプローチ
- **Claude Code**: Task Tool統合（全フェーズ対応、最優先）
- **CLI**: コマンドライン環境（開発者向け）
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

## 🤖 AI Agents（Claude Code Task Tool統合）

### Phase 1: Intent Agent 🎯
要件と意図の分析を担当：
- 自然言語からの要件抽出
- ユーザーストーリー生成
- ドメインモデル構築
- 曖昧性検出と解決
- 要件の優先順位付け（MoSCoW）
- トレーサビリティマトリックス作成

**Claude Code統合**: Intent Task Adapterによる完全自動化

### Phase 2: Natural Language Requirements Agent 📝
自然言語要件の構造化と分析を担当：
- **要件分析**: 自然言語テキストから構造化要件を抽出
- **エンティティ抽出**: ビジネスエンティティとその関係性を特定
- **完全性検証**: 要件の網羅性と欠落項目の特定
- **曖昧性解決**: 不明確な要件の特定と明確化提案
- **要件構造化**: 要件のカテゴリ分類と優先度設定
- **ギャップ識別**: 要件間の矛盾と欠落の検出

**Claude Code統合**: Natural Language Task Adapterでシームレス処理

### Phase 3: User Stories Creation Agent 📋
ユーザーストーリーの生成と管理を担当：
- **ストーリー生成**: 要件からのユーザーストーリー自動作成
- **ストーリー検証**: "As a... I want... So that..."形式の品質確保
- **優先順位付け**: ビジネス価値に基づくストーリープライオリティ
- **見積もり**: ストーリーポイントによる複雑度評価
- **受入基準作成**: Given-When-Then形式の詳細条件定義
- **エピック組織化**: 関連ストーリーのエピック単位での管理
- **依存関係識別**: ストーリー間の技術的・ビジネス的依存関係

**Claude Code統合**: User Stories Task Adapterで包括的管理

### Phase 4: Validation Agent 🔍
要件・ストーリー・仕様の品質検証を担当：
- **要件検証**: 機能・非機能要件の完全性と一貫性チェック
- **ストーリー検証**: ユーザーストーリーの品質メトリクス評価
- **仕様検証**: 形式仕様の整合性と明確性検証
- **トレーサビリティ検証**: 要件からコードまでの追跡可能性確保
- **完全性検証**: 各フェーズの成果物の網羅性評価
- **一貫性検証**: フェーズ間の整合性と用語統一チェック
- **実現可能性検証**: 技術的・経済的・運用的実現可能性評価
- **クロス検証**: 複数フェーズにわたる総合的品質評価

**Claude Code統合**: Validation Task Adapterで多層検証

### Phase 5: Domain Modeling Agent 🏗️
ドメイン駆動設計（DDD）によるドメインモデリングを担当：
- **ドメイン分析**: ビジネスドメインの包括的分析
- **エンティティ識別**: ドメインエンティティとその分類
- **集約モデリング**: 集約ルートと境界の定義
- **境界コンテキスト定義**: マイクロサービス境界の明確化
- **ビジネスルール抽出**: ドメイン固有のビジネスロジック特定
- **ユビキタス言語作成**: チーム共通の専門用語辞書構築
- **ドメインサービス設計**: 複数エンティティにまたがるサービス設計
- **モデル検証**: ドメインモデルの整合性と完全性検証

**Claude Code統合**: Domain Modeling Task Adapterで設計自動化

### Phase 6: Test Generation Agent 🧪
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

### Claude Code Task Tool統合
- **[🚀 Claude Code自動実行ガイド](docs/CLAUDE-CODE-AUTOMATION-GUIDE.md)** - 要求から実装まで完全自動化
- [Claude Code Task Tool統合ガイド](docs/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md) - 全フェーズ統合の詳細
- [Phase 2: Natural Language Requirements](docs/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md) - 自然言語要件処理
- [Phase 3: User Stories Creation](docs/PHASE-3-USER-STORIES-CREATION.md) - ユーザーストーリー生成
- [Phase 4: Validation](docs/PHASE-4-VALIDATION.md) - 品質検証システム
- [Phase 5: Domain Modeling](docs/PHASE-5-DOMAIN-MODELING.md) - ドメイン駆動設計
- [CLI Commands Reference](docs/CLI-COMMANDS-REFERENCE.md) - 全コマンドリファレンス

### フレームワーク詳細
- [TDD Framework Architecture](docs/TDD-FRAMEWORK-ARCHITECTURE.md) - Phase 1 Intent Agent
- [New Features Guide](docs/NEW_FEATURES.md) - Steering Documents、Phase State Management
- [Quick Start Guide](docs/QUICK-START-GUIDE.md) - 5分で始めるガイド
- [Contributing Guide](CONTRIBUTING.md) - 貢献ガイドライン

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