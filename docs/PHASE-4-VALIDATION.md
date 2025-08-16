# Phase 4: Validation

## 概要

Phase 4では、要件・ストーリー・仕様の品質検証を行うためのClaude Code Task Tool統合を提供します。多層的な検証アプローチにより、プロジェクトの品質保証と整合性確保を実現します。

## Claude Code Task Tool統合

### 自動呼び出し
Claude Codeが品質検証が必要と判断した場合、自動的にValidation Task Adapterが呼び出されます：

```
User: 要件とストーリーの整合性を検証してください

Claude Code: Validation Task Adapterで検証中...

✅ Cross-Validation Complete - 90% alignment across phases
📊 Analysis:
  • Requirements-Stories alignment: 95%
  • Traceability coverage: 88%
  • Consistency score: 92%
```

### 主要機能

#### 1. 要件検証（Requirements Validation）
機能・非機能要件の完全性と一貫性チェック：

**検証項目:**
```typescript
interface ValidationResult {
  isValid: boolean;
  score: number;                    // 総合スコア: 85%
  issues: ValidationIssue[];        // 検出された問題
  recommendations: string[];        // 改善提案
  coverageReport: CoverageReport;   // カバレッジレポート
}
```

**カバレッジ分析:**
- 機能要件: 90%
- 非機能要件: 70%
- ビジネス要件: 80%
- 技術要件: 75%
- 全体: 85%

**検出される問題例:**
```typescript
interface ValidationIssue {
  id: string;                       // REQ001
  type: 'error' | 'warning' | 'info';
  severity: 'critical' | 'high' | 'medium' | 'low';
  category: string;                 // "Clarity"
  description: string;              // "Requirement statement could be more specific"
  location?: string;                // 問題箇所
  suggestion?: string;              // 修正提案
}
```

#### 2. ユーザーストーリー検証（User Stories Validation）
ユーザーストーリーの品質メトリクス評価：

**品質メトリクス:**
- 適切な形式 (As a... I want... So that...): 90%
- 明確な受入基準: 70%
- テスト可能性: 85%
- 独立性: 80%
- 見積もり可能性: 75%

**一般的な問題:**
- 受入基準の欠如 (3件発生)
- 形式の不備 (1件発生)
- 依存関係の問題 (0件発生)

**ストーリー固有の問題:**
- **US001**: 受入基準が不完全
- **US005**: ストーリーが大きすぎる

#### 3. 仕様検証（Specification Validation）
形式仕様の整合性と明確性検証：

**準拠度分析:**
- 形式記法: 80%
- 完全性: 70%
- 一貫性: 85%
- 明確性: 75%
- テスト可能性: 80%

**カテゴリ別問題:**
- 形式記法: 2問題
- 完全性: 3問題
- 一貫性: 1問題

**重要な仕様ギャップ:**
- API仕様の不完全性 (影響: 高)
- データモデルの曖昧性 (影響: 中)

#### 4. トレーサビリティ検証（Traceability Validation）
要件からコードまでの追跡可能性確保：

**トレーサビリティカバレッジ: 80%**

**トレーサビリティマトリックス:**
- 要件 → ユーザーストーリー (85%カバレッジ)
- ユーザーストーリー → 仕様 (75%カバレッジ)
- 仕様 → テスト (90%カバレッジ)

**欠落リンク:**
- REQ003 → US007 (要件とストーリーの不整合)
- US004 → SPEC002 (仕様の欠如)

**孤立アーティファクト:**
- 仕様SPEC005: トレーサビリティなし
- テストTEST012: 対応する要件なし

#### 5. 完全性検証（Completeness Validation）
各フェーズの成果物の網羅性評価：

**完全性スコア: 75%**

**カテゴリ別完全性:**
- 要件: 80% (2項目不足)
- ユーザーストーリー: 85% (1項目不足)
- 仕様: 70% (4項目不足)
- テスト: 90% (1項目不足)

**欠落コンポーネント:**
- セキュリティ: 認証要件の詳細 (優先度: 高)
- パフォーマンス: 負荷テスト仕様 (優先度: 中)
- 運用: 監視要件 (優先度: 低)

#### 6. 一貫性検証（Consistency Validation）
フェーズ間の整合性と用語統一チェック：

**一貫性スコア: 85%**

**一貫性分析:**
- 用語の一貫性: 90%
- 形式の一貫性: 80%
- ビジネスルールの一貫性: 85%
- 技術制約の一貫性: 80%

**主要な不整合:**
- 用語の競合: "ユーザー" vs "利用者"
- 形式の不統一: 要件記述スタイルの違い

#### 7. 実現可能性検証（Feasibility Validation）
技術的・経済的・運用的実現可能性評価：

**実現可能性スコア: 80%**

**次元別評価:**
- 技術的実現可能性: 85%
- 経済的実現可能性: 75%
- 運用的実現可能性: 80%
- スケジュール実現可能性: 70%

**リスク要因:**
- 高リスク: レガシーシステム統合 (影響: 大)
- 中リスク: サードパーティAPI依存 (影響: 中)

#### 8. クロス検証（Cross-Validation）
複数フェーズにわたる総合的品質評価：

**全体アライメント: 85%**

**フェーズ間アライメント:**
- 要件-ストーリー: 90%
- ストーリー-仕様: 85%
- 仕様-テスト: 80%

**クロスフェーズ問題:**
- 要件 ↔ 仕様: 定義の不一致 (重要度: 高)
- ストーリー ↔ テスト: カバレッジ不足 (重要度: 中)

## CLI コマンド使用例

### 要件検証
```bash
# 要件の完全性と一貫性を検証
ae-framework validate --requirements --sources="requirements.md"

# 出力例:
# ✅ Requirements Validation Complete - 85% valid (0 errors, 3 warnings)
# 📊 Coverage Analysis:
#   • Functional Requirements: 90%
#   • Non-Functional Requirements: 70%
#   • Business Requirements: 80%
```

### ユーザーストーリー検証
```bash
# ユーザーストーリーの品質検証
ae-framework validate --stories --sources="user-stories.md"

# 出力例:
# ✅ User Stories Validation Complete - 80% compliant
# 📊 Quality Metrics:
#   • Proper Format: 90%
#   • Clear Acceptance Criteria: 70%
#   • Testable Stories: 85%
```

### トレーサビリティ検証
```bash
# 要件からコードまでの追跡可能性を検証
ae-framework validate --traceability --sources="all-artifacts/"

# 出力例:
# ✅ Traceability Validation Complete - 80% traceability coverage
# 📊 Coverage Matrix:
#   • Requirements → Stories: 85%
#   • Stories → Specs: 75%
#   • Specs → Tests: 90%
```

### 完全性検証
```bash
# 全フェーズの完全性を検証
ae-framework validate --completeness --sources="project/"

# 出力例:
# ✅ Completeness Validation Complete - 75% complete
# ⚠️ Warnings:
#   • Security requirements missing details
#   • Performance specifications incomplete
```

## プロアクティブガイダンス

Validation Task Adapterは、以下の状況で自動的に介入を提案します：

### 重要な検証問題の検出
```
🚫 Block: Critical validation issues detected
🔧 Actions:
  • Address critical validation issues immediately
  • Improve requirements coverage in weak areas
  • Validate requirements with stakeholders
```

### 検証ギャップの検出
```
⚠️ Warning: Validation gaps detected
💡 Recommendations:
  • Validate updated requirements
  • Check consistency with existing specifications
  • Verify traceability links
```

### 変更に伴う検証の提案
```
💡 Suggestion: Recent changes should be validated
🔧 Actions:
  • Validate recent changes for consistency
  • Check impact on existing requirements
  • Update validation documentation
```

## TypeScript インターフェース

### ValidationResult
```typescript
interface ValidationResult {
  isValid: boolean;
  score: number;
  issues: ValidationIssue[];
  recommendations: string[];
  coverageReport: CoverageReport;
}
```

### ValidationIssue
```typescript
interface ValidationIssue {
  id: string;
  type: 'error' | 'warning' | 'info';
  severity: 'critical' | 'high' | 'medium' | 'low';
  category: string;
  description: string;
  location?: string;
  suggestion?: string;
}
```

### CoverageReport
```typescript
interface CoverageReport {
  functional: number;      // 機能要件カバレッジ
  nonFunctional: number;   // 非機能要件カバレッジ
  business: number;        // ビジネス要件カバレッジ
  technical: number;       // 技術要件カバレッジ
  overall: number;         // 全体カバレッジ
}
```

## 検証レベルの設定

### 基本検証
```typescript
const basicValidation = {
  requirements: true,
  stories: true,
  completeness: false,
  traceability: false
};
```

### 包括的検証
```typescript
const comprehensiveValidation = {
  requirements: true,
  stories: true,
  specifications: true,
  traceability: true,
  completeness: true,
  consistency: true,
  feasibility: true,
  crossValidation: true
};
```

## 次のステップ

Phase 4完了後は、以下のフェーズに進みます：

1. **Phase 5: Domain Modeling** - 検証済み要件に基づくドメインモデル設計
2. **Phase 6: Test Generation** - 検証された仕様からテストケース生成
3. **Phase 7: Code Generation** - テスト駆動による実装生成

## トラブルシューティング

### よくある問題と解決策

**問題: 検証スコアが低い**
```bash
# 詳細な問題分析
ae-framework validate --requirements --completeness --sources="all/"
```

**問題: トレーサビリティが不完全**
```bash
# トレーサビリティマトリックスの再構築
ae-framework validate --traceability --sources="artifacts/"
```

**問題: クロス検証で多数の問題**
```bash
# フェーズ別の段階的検証
ae-framework validate --requirements
ae-framework validate --stories
ae-framework validate --traceability
```

## 設定とカスタマイズ

### 検証閾値の調整
```typescript
const validationThresholds = {
  critical: 50,      // 進行をブロックする閾値
  warning: 70,       // 警告を表示する閾値
  good: 85,          // 良好とみなす閾値
  excellent: 95      // 優秀とみなす閾値
};
```

### カスタム検証ルール
```typescript
const customValidationRules = {
  requirementFormat: /^REQ-\d{3}:/,
  storyFormat: /^US-\d{3}:/,
  acceptanceCriteriaRequired: true,
  traceabilityRequired: true
};
```