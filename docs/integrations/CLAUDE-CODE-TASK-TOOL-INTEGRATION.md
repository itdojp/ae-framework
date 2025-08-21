# Claude Code Integration Guide - AE Framework Complete Integration

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Comprehensive Integration Documentation for AE Framework ↔ Claude Code**  
**Seamless workflow from natural language instructions to high-quality code generation**

### 📋 Table of Contents

1. [Integration Overview](#integration-overview)
2. [Architecture Details](#architecture-details)
3. [Task Tool Integration](#task-tool-integration)
4. [Phase-by-Phase Integration](#phase-by-phase-integration)
5. [Actual Call Flow](#actual-call-flow)
6. [Usage Examples & Best Practices](#usage-examples--best-practices)
7. [Performance & Optimization](#performance--optimization)
8. [Troubleshooting](#troubleshooting)

---

### Integration Overview

#### 🎯 Core Philosophy

AE Framework integrates as a **Task Tool** in Claude Code environment, enabling the following through natural language instructions alone:

- **Requirements Analysis** → **Domain Modeling** → **UI Generation** complete automation
- **6-Phase Development Methodology** seamless execution
- **WCAG 2.1 AA compliant** high-quality UI auto-generation
- **Enterprise-grade** quality assurance

#### 🔄 Integration Architecture

```
Claude Code (Natural Language) 
    ↓ Task Tool Call
AE Framework (Task Adapters)
    ↓ Structured Processing
High-Quality Artifacts (React+Next.js etc.)
```

#### ✨ Key Benefits

1. **Zero Learning Curve**: No complex CLI commands required
2. **Quality Assurance**: Automatic quality gates and metrics
3. **High-Speed Generation**: 21 files/30 seconds UI auto-generation
4. **Full Compliance**: WCAG 2.1 AA, Enterprise Security ready

**🎉 2025 Complete Implementation Status**:
- ✅ **Phase 6 UI/UX Generation**: 100% implementation complete (21 files/30 seconds generation)
- ✅ **Comprehensive Quality System**: Golden/Approval, Metamorphic, CLI Fuzzing complete
- ✅ **Integrated Security Audit**: 5 core modules implementation complete
- ✅ **CEGIS Auto-repair**: Failure artifact analysis & auto-correction implemented
- ✅ **Runtime Conformance**: Zod + OpenTelemetry runtime verification implemented
- ✅ **Fast CI/CD**: 5min/15min/30min staged pipeline implemented
- ✅ **Enterprise Quality**: WCAG 2.1 AA compliant, production-ready complete

### Architecture Details

#### 🏗️ Hybrid Integration System

```typescript
export interface HybridIntentConfig {
  enableCLI: boolean;                    // CLI integration
  enableMCPServer: boolean;              // MCP Server integration  
  enableClaudeCodeIntegration: boolean;  // 🎯 Claude Code integration (Primary)
  enforceRealTime: boolean;              // Real-time processing
  strictMode: boolean;                   // Strict mode
}

export class HybridIntentSystem {
  async handleIntentRequest(request: {
    type: 'cli' | 'task' | 'mcp' | 'auto';
    data: any;
    context?: {
      isClaudeCode: boolean;     // 🎯 Claude Code detection
      hasTaskTool: boolean;      // Task Tool availability
    };
  }): Promise<any> {
    
    if (request.context?.isClaudeCode && request.context?.hasTaskTool) {
      // 🎯 Claude Code Task Tool processing
      return this.handleTaskToolRequest(request);
    }
    
    // Fallback: CLI or MCP
    return this.handleFallbackRequest(request);
  }
}
```

### Task Tool Integration

#### 🔧 Interface Definition

```typescript
// Claude Code → AE Framework
interface TaskRequest {
  description: string;      // Task description
  prompt: string;          // Processing target prompt  
  subagent_type: string;   // Phase specification
}

// AE Framework → Claude Code
interface TaskResponse {
  summary: string;           // Execution result summary
  analysis: string;          // Detailed analysis (Markdown format)
  recommendations: string[]; // Recommendations
  nextActions: string[];     // Next actions
  warnings: string[];        // Warnings
  shouldBlockProgress: boolean; // Progress blocking determination
}
```

### Phase-by-Phase Integration

#### Phase 1: Intent Analysis 🎯
- **Task Adapter**: Intent Task Adapter
- **Primary Function**: User intent analysis and requirement extraction
- **Output**: 12+ requirements identified from natural language input

#### Phase 2: Natural Language Requirements 📝
- **Task Adapter**: Natural Language Task Adapter
- **Primary Function**: Structure and validate natural language requirements
- **Output**: Functional/non-functional requirements categorization

#### Phase 3: User Stories Creation 📋
- **Task Adapter**: User Stories Task Adapter
- **Primary Function**: Generate user stories and acceptance criteria
- **Output**: Epic-organized user stories with story points

#### Phase 4: Validation 🔍
- **Task Adapter**: Validation Task Adapter
- **Primary Function**: Cross-validate requirements, stories, and specifications
- **Output**: Traceability matrix and consistency reports

#### Phase 5: Domain Modeling 🏗️
- **Task Adapter**: Domain Modeling Task Adapter
- **Primary Function**: Create domain-driven design models
- **Output**: Entities, bounded contexts, domain services

#### Phase 6: UI/UX & Frontend Delivery 🎨
- **Task Adapter**: UI Generation Task Adapter
- **Primary Function**: React + Next.js 14 UI component generation
- **Output**: 21 files including components, pages, tests, Storybook stories

### Usage Examples

#### Basic UI Generation
```
User: "Create an e-commerce product management interface"

Claude Code: Executing UI Task Adapter for component generation...

📊 OpenTelemetry initialized for ae-framework Phase 6
✅ Generated 21 files for 3/3 entities
📊 Test Coverage: 96% (threshold: 80%) ✅
♿ A11y Score: 97% (threshold: 95%) ✅  
⚡ Performance Score: 79% (threshold: 75%) ✅
🏗️ Scaffold Time: 18243ms ✅
```

#### Complete 6-Phase Development
```
User: "Build a complete inventory management system"

Claude Code: Executing sequential 6-phase development...

Phase 1: Intent Analysis Complete - 15 requirements identified
Phase 2: Requirements structured - 8 functional, 7 non-functional
Phase 3: User Stories generated - 12 stories across 4 epics
Phase 4: Validation complete - 94% traceability achieved
Phase 5: Domain model created - 6 entities, 3 bounded contexts
Phase 6: UI generated - React components with full test coverage
```

### Performance & Optimization

#### Generation Speed
- **UI Components**: 21 files in <30 seconds
- **Full Application**: Complete app in <5 minutes
- **Quality Gates**: All checks in <2 minutes

#### Quality Metrics
- **Test Coverage**: ≥80% automatic
- **Accessibility**: WCAG 2.1 AA (≥95% score)
- **Performance**: Lighthouse ≥75%
- **Type Safety**: 100% TypeScript strict mode

### Best Practices

1. **Clear Intent**: Provide specific, actionable requirements
2. **Iterative Development**: Build incrementally through phases
3. **Quality Validation**: Review generated quality reports
4. **Customization**: Use design tokens for brand consistency

---

## Japanese

**AE Framework ↔ Claude Code の包括的統合ドキュメント**  
**自然言語指示から高品質コード生成まで一貫したワークフローを実現**

### 📋 目次

1. [統合概要](#統合概要)
2. [アーキテクチャ詳細](#アーキテクチャ詳細)
3. [Task Tool統合](#task-tool統合)
4. [フェーズ別連携](#フェーズ別連携)
5. [実際の呼び出しフロー](#実際の呼び出しフロー)
6. [使用例とベストプラクティス](#使用例とベストプラクティス)
7. [パフォーマンスと最適化](#パフォーマンスと最適化)
8. [トラブルシューティング](#トラブルシューティング)

---

## 統合概要

### 🎯 基本理念

AE FrameworkはClaude Code環境における**Task Tool**として統合され、自然言語指示だけで以下を実現：

- **要件分析** → **ドメインモデリング** → **UI生成**の完全自動化
- **6フェーズ開発手法**のシームレス実行
- **WCAG 2.1 AA準拠**の高品質UI自動生成
- **エンタープライズグレード**の品質保証

### 🔄 統合方式

```
Claude Code (自然言語) 
    ↓ Task Tool呼び出し
AE Framework (Task Adapters)
    ↓ 構造化処理
高品質成果物 (React+Next.js他)
```

### ✨ 主要メリット

1. **学習コスト ゼロ**: 複雑なCLIコマンド不要
2. **品質保証**: 自動的な品質ゲートとメトリクス
3. **高速生成**: 21ファイル/30秒のUI自動生成
4. **完全準拠**: WCAG 2.1 AA、Enterprise Security対応

**🎉 2025年完全実装状況**：
- ✅ **Phase 6 UI/UX Generation**: 100%実装完了 (21ファイル/30秒生成)
- ✅ **包括的品質システム**: Golden/Approval、Metamorphic、CLI Fuzzing完備  
- ✅ **統合セキュリティ監査**: 5コアモジュール実装完了
- ✅ **CEGIS自動修復**: 失敗アーティファクト分析・自動修正実装
- ✅ **Runtime Conformance**: Zod + OpenTelemetry実行時検証実装
- ✅ **Fast CI/CD**: 5分/15分/30分段階パイプライン実装
- ✅ **エンタープライズ品質**: WCAG 2.1 AA準拠、プロダクション対応完了

---

## アーキテクチャ詳細

### 🏗️ ハイブリッド統合システム

```typescript
export interface HybridIntentConfig {
  enableCLI: boolean;                    // CLI統合
  enableMCPServer: boolean;              // MCP Server統合  
  enableClaudeCodeIntegration: boolean;  // 🎯 Claude Code統合 (メイン)
  enforceRealTime: boolean;              // リアルタイム処理
  strictMode: boolean;                   // 厳密モード
}

export class HybridIntentSystem {
  async handleIntentRequest(request: {
    type: 'cli' | 'task' | 'mcp' | 'auto';
    data: any;
    context?: {
      isClaudeCode: boolean;     // 🎯 Claude Code判定
      hasTaskTool: boolean;      // Task Tool利用可能性
    };
  }): Promise<any> {
    
    if (request.context?.isClaudeCode && request.context?.hasTaskTool) {
      // 🎯 Claude Code Task Tool経由の処理
      return this.handleTaskToolRequest(request);
    }
    
    // フォールバック: CLI or MCP
    return this.handleFallbackRequest(request);
  }
}
```

### 📊 呼び出し優先度

```
1. Claude Code Task Tool (最優先)
   ↓ フォールバック
2. CLI Commands (開発者直接実行)
   ↓ フォールバック  
3. MCP Server (バックアップ統合)
```

---

## Task Tool統合

### 🔧 インターフェース定義

```typescript
// Claude Code → AE Framework
interface TaskRequest {
  description: string;      // タスクの説明
  prompt: string;          // 処理対象のプロンプト  
  subagent_type: string;   // フェーズ指定
}

// AE Framework → Claude Code
interface TaskResponse {
  summary: string;           // 実行結果サマリー
  analysis: string;          // 詳細分析（Markdown形式）
  recommendations: string[]; // 推奨事項
  nextActions: string[];     // 次のアクション
  warnings: string[];        // 警告事項
  shouldBlockProgress: boolean; // 進行ブロック判定
}
```

### 🎯 Task Adapterアーキテクチャ

```typescript
// src/cli/index.ts - 各フェーズのTask Handler
class AEFrameworkCLI {
  public naturalLanguageHandler: TaskHandler;    // Phase 2: 要件構造化
  public userStoriesHandler: TaskHandler;        // Phase 3: ストーリー生成
  public validationHandler: TaskHandler;         // Phase 4: 品質検証
  public domainModelingHandler: TaskHandler;     // Phase 5: ドメインモデリング
  public uiHandler: TaskHandler;                 // Phase 6: UI生成

  constructor() {
    // 各フェーズのTask Handlerを初期化
    this.naturalLanguageHandler = createNaturalLanguageTaskHandler();
    this.userStoriesHandler = createUserStoriesTaskHandler();
    this.validationHandler = createValidationTaskHandler();
    this.domainModelingHandler = createDomainModelingTaskHandler();
    this.uiHandler = createUIGenerationTaskHandler();
  }
}
```

---

## フェーズ別連携

### Phase 1: Intent Analysis 🎯

**Task Adapter**: Intent Task Adapter  
**主要機能**: ユーザー意図の分析と要件抽出

```typescript
// 呼び出し例
const request: TaskRequest = {
  description: "プロジェクト要件の意図分析",
  prompt: "ECサイトの商品管理システムを作りたい",
  subagent_type: "intent-analysis"
};

// 応答例
const response: TaskResponse = {
  summary: "Eコマース商品管理システムの要件を12項目特定",
  analysis: `
## 意図分析結果
### 特定された要件カテゴリ
- **コア機能**: 商品CRUD、在庫管理、価格設定
- **ユーザー管理**: 管理者権限、ロール管理
- **非機能要件**: パフォーマンス、セキュリティ
### ビジネス価値
- 売上向上: 効率的な商品管理により販売機会拡大
- 運用効率: 自動化により人的コスト削減
`,
  recommendations: [
    "Phase 2で詳細要件の構造化を推奨",
    "ステークホルダーへのヒアリング実施を検討"
  ],
  nextActions: [
    "自然言語要件処理フェーズへ進行",
    "要件の優先度設定を実施"
  ],
  warnings: [],
  shouldBlockProgress: false
};
```

### Phase 2: Natural Language Requirements 📝

**Task Adapter**: Natural Language Task Adapter  
**主要機能**: 自然言語要件の構造化と分析

**実行例**:
```
User: 商品管理システムの詳細要件を整理してください

Claude Code: Natural Language Task Adapterで要件分析を実行中...

✅ Requirements Analysis Complete - 15 requirements identified
📊 Analysis:
  • Functional Requirements: 10
  • Non-Functional Requirements: 3  
  • Business Requirements: 2
💡 Recommendations:
  • Review identified gaps for completeness
  • Clarify ambiguous requirements with stakeholders
```

### Phase 3: User Stories Creation 📋

**Task Adapter**: User Stories Task Adapter  
**主要機能**: ユーザーストーリー生成と管理

**実行例**:
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

### Phase 4: Validation 🔍

**Task Adapter**: Validation Task Adapter  
**主要機能**: 要件・ストーリー・仕様の品質検証

**実行例**:
```
User: 要件とストーリーの整合性を検証してください

Claude Code: Validation Task Adapterで検証中...

✅ Cross-Validation Complete - 90% alignment across phases
📊 Analysis:
  • Requirements-Stories alignment: 95%
  • Traceability coverage: 88%
  • Consistency score: 92%
```

### Phase 5: Domain Modeling 🏗️

**Task Adapter**: Domain Modeling Task Adapter  
**主要機能**: ドメイン駆動設計（DDD）によるドメインモデリング

**実行例**:
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

### Phase 6: UI/UX & Frontend Delivery 🎨

**Task Adapter**: UI Generation Task Adapter  
**主要機能**: React + Next.js 14 によるフロントエンド配信

**実行例**:
```
User: UI コンポーネントを生成してください

Claude Code: UI Task Adapterでコンポーネント生成中...

📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ae-framework v1.0.0
   Environment: development
   OTLP Export: ✅ Enabled

✅ Generated 21 files for 3/3 entities
📊 Test Coverage: 100% (threshold: 80%)
♿ A11y Score: 96% (threshold: 95%) ✅  
⚡ Performance Score: 78% (threshold: 75%) ✅
📈 Phase 6 Efficiency Metrics:
  🏗️  Scaffold Time: 15243ms ✅
  📊 Generated 21 files for 3/3 entities

🎨 UI Analysis:
  • React Components: 12 files
  • Next.js Pages: 6 files  
  • Storybook Stories: 3 files
  • E2E Tests: 3 files
  • Design Tokens: integrated ✅
  • i18n Support: ja/en ✅
```

---

## 使用例とベストプラクティス

### 基本的なUI生成

```
User: eコマースの商品管理インターフェースを作成してください

Claude Code: UIコンポーネント生成のためのUI Task Adapterを実行中...

📊 OpenTelemetry初期化完了 ae-framework Phase 6
✅ 3/3エンティティに対して21ファイル生成
📊 テストカバレッジ: 96% (閾値: 80%) ✅
♿ A11yスコア: 97% (閾値: 95%) ✅  
⚡ パフォーマンススコア: 79% (閾値: 75%) ✅
🏗️ スキャフォールド時間: 18243ms ✅
```

### 完全な6フェーズ開発

```
User: 完全な在庫管理システムを構築してください

Claude Code: 連続6フェーズ開発を実行中...

Phase 1: 意図分析完了 - 15要件を特定
Phase 2: 要件構造化完了 - 機能要件8、非機能要件7
Phase 3: ユーザーストーリー生成完了 - 4エピックにわたる12ストーリー
Phase 4: 検証完了 - 94%のトレーサビリティ達成
Phase 5: ドメインモデル作成完了 - 6エンティティ、3境界コンテキスト
Phase 6: UI生成完了 - 完全なテストカバレッジを持つReactコンポーネント
```

---

## パフォーマンスと最適化

### 生成速度
- **UIコンポーネント**: 30秒以内に21ファイル
- **完全アプリケーション**: 5分以内に完成アプリ
- **品質ゲート**: 2分以内に全チェック

### 品質メトリクス
- **テストカバレッジ**: ≥80% 自動達成
- **アクセシビリティ**: WCAG 2.1 AA (≥95%スコア)
- **パフォーマンス**: Lighthouse ≥75%
- **型安全性**: 100% TypeScript strict mode

### ベストプラクティス

1. **明確な意図**: 具体的で実行可能な要件を提供
2. **反復開発**: フェーズを通じて段階的に構築
3. **品質検証**: 生成された品質レポートをレビュー
4. **カスタマイズ**: ブランド一貫性のためデザイントークンを使用

---

**🤖 Experience the future of development with AE Framework and Claude Code integration today! / AE FrameworkとClaude Code統合で、開発の未来を今すぐ体験してください！**