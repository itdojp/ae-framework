# Claude Code Task Tool Integration

## 概要

ae-frameworkは、Claude Code環境において全6フェーズのソフトウェア開発ワークフローを自動統合する包括的なTask Tool統合を提供します。この統合により、開発者は自然言語での指示だけで、要件分析からドメインモデリングまでの一連のプロセスを実行できます。

## 統合アーキテクチャ

### ハイブリッドアプローチ
```
Claude Code Task Tool (最優先)
    ↓ フォールバック
CLI Commands (開発者向け)
    ↓ フォールバック  
MCP Server (バックアップ)
```

### Task Adapter パターン
各フェーズは専用のTask Adapterで実装：

```typescript
interface TaskAdapter {
  handleTask(request: TaskRequest): Promise<TaskResponse>;
  provideProactiveGuidance(context: any): Promise<any>;
}
```

## フェーズ別統合詳細

### Phase 1: Intent Analysis 🎯
**Task Adapter**: Intent Task Adapter
**主要機能**: 要件と意図の分析

```
User: プロジェクトの要件分析をお願いします

Claude Code: Intent Task Adapterを使用して要件分析を実行します...

✅ Intent Analysis Complete - 12 requirements identified
📋 Next steps:
  • Proceed to Phase 2 (Natural Language Requirements)
```

**ドキュメント**: [TDD Framework Architecture](./TDD-FRAMEWORK-ARCHITECTURE.md)

### Phase 2: Natural Language Requirements 📝
**Task Adapter**: Natural Language Task Adapter
**主要機能**: 自然言語要件の構造化と分析

```
User: 要件を構造化してください

Claude Code: Natural Language Task Adapterを実行中...

✅ Requirements Analysis - 15 requirements identified
📊 Analysis:
  • Functional Requirements: 10
  • Non-Functional Requirements: 3
  • Business Requirements: 2
```

**ドキュメント**: [Phase 2 詳細](./PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md)

### Phase 3: User Stories Creation 📋
**Task Adapter**: User Stories Task Adapter
**主要機能**: ユーザーストーリーの生成と管理

```
User: ユーザーストーリーを作成してください

Claude Code: User Stories Task Adapterで処理中...

✅ User Story Generation Complete - 8 stories created across 3 epics
📊 Analysis:
  • Total Stories: 8
  • Total Epics: 3
  • Total Story Points: 34
```

**ドキュメント**: [Phase 3 詳細](./PHASE-3-USER-STORIES-CREATION.md)

### Phase 4: Validation 🔍
**Task Adapter**: Validation Task Adapter
**主要機能**: 要件・ストーリー・仕様の品質検証

```
User: 要件とストーリーの整合性を検証してください

Claude Code: Validation Task Adapterで検証中...

✅ Cross-Validation Complete - 90% alignment across phases
📊 Analysis:
  • Requirements-Stories alignment: 95%
  • Traceability coverage: 88%
```

**ドキュメント**: [Phase 4 詳細](./PHASE-4-VALIDATION.md)

### Phase 5: Domain Modeling 🏗️
**Task Adapter**: Domain Modeling Task Adapter
**主要機能**: ドメイン駆動設計（DDD）によるモデリング

```
User: ドメインモデルを設計してください

Claude Code: Domain Modeling Task Adapterで設計中...

✅ Domain Analysis Complete - 6 entities, 2 bounded contexts identified
📊 Analysis:
  • Core Domain Entities: 4
  • Bounded Contexts: 2
  • Business Rules: 12
```

**ドキュメント**: [Phase 5 詳細](./PHASE-5-DOMAIN-MODELING.md)

## 技術実装詳細

### Task Request/Response インターフェース
```typescript
interface TaskRequest {
  description: string;      // タスクの説明
  prompt: string;          // 処理対象のプロンプト
  subagent_type: string;   // サブエージェントタイプ
}

interface TaskResponse {
  summary: string;           // 実行結果サマリー
  analysis: string;          // 詳細分析（Markdown形式）
  recommendations: string[]; // 推奨事項
  nextActions: string[];     // 次のアクション
  warnings: string[];        // 警告事項
  shouldBlockProgress: boolean; // 進行ブロック判定
}
```

### プロアクティブガイダンス
各Task Adapterは、開発状況を監視し自動的にガイダンスを提供：

```typescript
interface ProactiveGuidance {
  shouldIntervene: boolean;
  intervention: {
    type: 'warning' | 'suggestion' | 'block';
    message: string;
    recommendedActions: string[];
  };
}
```

### CLI統合
Claude Code Task Tool統合と並行して、CLI環境もサポート：

```bash
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

**ドキュメント**: [CLI Commands Reference](./CLI-COMMANDS-REFERENCE.md)

## 主要な特徴

### 🚀 完全自動統合
- Claude Code環境で追加設定なしで利用可能
- 自然言語での指示で複雑なワークフローを実行
- 段階的な品質ゲートとプロアクティブガイダンス

### 🔧 TypeScript型安全性
- 全インターフェースでTypeScript型定義を提供
- コンパイル時エラー検出で品質保証
- IDE支援による開発効率向上

### 📊 包括的メトリクス
- フェーズ別進捗追跡
- 品質メトリクスの自動計算
- トレーサビリティマトリックス生成

### 🛡️ 品質保証
- 多層検証アプローチ
- 一貫性チェック機能
- 完全性評価システム

### 🏗️ DDD統合
- ドメイン駆動設計パターンのサポート
- 境界コンテキスト自動識別
- ユビキタス言語構築支援

## 設定とカスタマイズ

### 基本設定
```typescript
// src/cli/index.ts での設定例
const taskHandlers = {
  naturalLanguage: createNaturalLanguageTaskHandler(),
  userStories: createUserStoriesTaskHandler(),
  validation: createValidationTaskHandler(),
  domainModeling: createDomainModelingTaskHandler()
};
```

### 品質閾値調整
```typescript
const qualityThresholds = {
  completeness: {
    critical: 50,    // 進行ブロック閾値
    warning: 70,     // 警告表示閾値
    good: 85         // 良好判定閾値
  },
  consistency: {
    minimum: 80,     // 最低一貫性要求
    target: 90       // 目標一貫性レベル
  }
};
```

### プロアクティブガイダンス設定
```typescript
const guidanceConfig = {
  enableAutoIntervention: true,
  interventionThresholds: {
    critical: 'block',      // 重要問題で進行ブロック
    high: 'warning',        // 高優先度で警告
    medium: 'suggestion'    // 中優先度で提案
  }
};
```

## 使用例とワークフロー

### 典型的な開発フロー
```
1. Phase 1: Intent Analysis
   User: "ECサイトの要件を分析してください"
   → 要件抽出、意図分析、次フェーズ準備

2. Phase 2: Natural Language Requirements
   User: "要件を構造化してください"
   → 機能・非機能要件の分類、エンティティ抽出

3. Phase 3: User Stories Creation
   User: "ユーザーストーリーを作成してください"
   → As a... I want... So that...形式での自動生成

4. Phase 4: Validation
   User: "全体の整合性を検証してください"
   → クロスフェーズ検証、トレーサビリティチェック

5. Phase 5: Domain Modeling
   User: "ドメインモデルを設計してください"
   → DDD原則によるエンティティ・集約・境界コンテキスト設計
```

### 段階的品質向上
```
初期要件 (60%品質)
    ↓ Phase 2
構造化要件 (75%品質)
    ↓ Phase 3
ユーザーストーリー (80%品質)
    ↓ Phase 4
検証済み仕様 (90%品質)
    ↓ Phase 5
ドメインモデル (95%品質)
```

## パフォーマンスと最適化

### 処理時間目安
- Phase 2 (Natural Language): 10-30秒
- Phase 3 (User Stories): 15-45秒
- Phase 4 (Validation): 20-60秒
- Phase 5 (Domain Modeling): 30-90秒

### メモリ使用量
- 小規模プロジェクト (<50要件): ~50MB
- 中規模プロジェクト (50-200要件): ~100MB
- 大規模プロジェクト (200+要件): ~200MB

### スケーラビリティ
- 同時処理: 最大3フェーズ並列実行
- ファイルサイズ: 最大10MB/ファイル
- 要件数: 最大500要件/プロジェクト

## トラブルシューティング

### よくある問題

**問題: Task Adapterが呼び出されない**
```
解決策:
1. Claude Code環境であることを確認
2. プロンプトが明確で具体的であることを確認
3. ファイルパスが正しいことを確認
```

**問題: 品質スコアが低い**
```
解決策:
1. より詳細な要件を提供
2. 段階的にフェーズを進める
3. 検証結果の推奨事項を実行
```

**問題: プロアクティブガイダンスが過度に介入**
```
解決策:
1. 介入閾値を調整
2. 特定の警告を無効化
3. バッチモードでの実行
```

## 今後の拡張予定

### Phase 6対応
- Test Generation Task Adapter
- 要件からテストケース自動生成
- Property-based testing統合

### Phase 7対応
- Code Generation Task Adapter
- ドメインモデルからコード生成
- テスト駆動開発サポート

### 高度な機能
- 多言語要件サポート
- リアルタイムコラボレーション
- AI支援レビュープロセス

## 関連ドキュメント

- [README.md](../README.md) - プロジェクト概要
- [TDD Framework Architecture](./TDD-FRAMEWORK-ARCHITECTURE.md) - Phase 1詳細
- [Phase 2: Natural Language Requirements](./PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md)
- [Phase 3: User Stories Creation](./PHASE-3-USER-STORIES-CREATION.md)
- [Phase 4: Validation](./PHASE-4-VALIDATION.md)
- [Phase 5: Domain Modeling](./PHASE-5-DOMAIN-MODELING.md)
- [CLI Commands Reference](./CLI-COMMANDS-REFERENCE.md)