---
docRole: ssot
lastVerified: 2026-03-11
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 3: User Stories Creation

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Automated user story generation and management system from structured requirements with Claude Code Task Tool integration**

### Overview

Phase 3 provides Claude Code Task Tool integration for generating and managing user stories from structured requirements. It automatically generates user stories in the essential "As a... I want... So that..." format crucial for agile development and ensures their quality.

### Claude Code Task Tool Integration

#### Automatic Invocation
When Claude Code determines user story creation is needed, the User Stories Task Adapter is automatically invoked:

```
User: Please create user stories

Claude Code: Processing with User Stories Task Adapter...

✅ User Story Generation Complete - 8 stories created across 3 epics
📊 Analysis:
  • Total Stories: 8
  • Total Epics: 3
  • Total Story Points: 34
  • Completeness Score: 85%
```

### Key Features

#### 1. Story Generation
Automatic user story creation from requirements:

**Example Input Requirements:**
```
User authentication functionality
- Users can log in with email and password
- Passwords are stored as hashes
- Login failures are allowed up to 3 times
```

**Generated Story Example:**
```
US001: User Login
As a registered user
I want to log into the system with my email and password
So that I can access my personalized dashboard

Acceptance Criteria:
- User can enter valid email address and password
- System validates authentication credentials
- Successful login redirects to dashboard
- Failed login displays appropriate error message

Priority: High
Story Points: 5
Epic: User Management
```

#### 2. Story Validation
Quality assurance for "As a... I want... So that..." format:

**Validation Items:**
```text
interface QualityMetrics {
  formatCompliance: number;      // Format compliance: 90%
  acceptanceCriteria: number;    // Acceptance criteria clarity: 70%
  testability: number;           // Testability: 85%
  independence: number;          // Independence: 80%
  estimability: number;          // Estimability: 75%
}
```

**Common Issues:**
- Missing acceptance criteria (3 occurrences)
- Ambiguous expressions (2 occurrences)
- Dependency issues (1 occurrence)

#### 3. Story Prioritization
Story priority based on business value:

**Priority Matrix:**
- **High Priority**: 3 stories (high business value)
- **Medium Priority**: 4 stories (medium business value)
- **Low Priority**: 1 story (low business value)

**Release Recommendations:**
- **Release 1.0**: 5 stories (8 weeks)
- **Release 1.1**: 3 stories (4 weeks)

#### 4. Story Estimation
Complexity assessment using story points:

**Estimation Distribution:**
- **1 Point**: 2 stories (simple)
- **3 Points**: 3 stories (simple)
- **5 Points**: 2 stories (medium)
- **8 Points**: 1 story (complex)

**Complexity Analysis:**
- Simple stories (1-3 points): 5 stories
- Medium stories (5-8 points): 3 stories
- Complex stories (13+ points): 0 stories

#### 5. Acceptance Criteria Creation
Detailed condition definition in Given-When-Then format:

**Example: User Login Story**
```
Acceptance Criteria:
1. Given user has valid authentication credentials
   When submitting login form
   Then user is redirected to dashboard

2. Given user enters invalid authentication credentials
   When submitting login form
   Then error message is displayed

3. Given user has failed login 3 times
   When attempting 4th login
   Then account is temporarily locked
```

**Test Scenarios:**
1. Valid login test (positive)
2. Invalid authentication test (negative)
3. Account lock test (edge case)

#### 6. Epic Organization
Management of related stories in epic units:

**Epic Example:**
```
Epic: User Management
- US001: User Login (5 points)
- US002: User Registration (8 points)
- US003: Password Reset (3 points)
Total: 16 points (estimated 2 weeks)

Epic: Product Management
- US004: Product Search (5 points)
- US005: Product Detail Display (3 points)
Total: 8 points (estimated 1 week)
```

#### 7. Dependency Identification
Technical and business dependencies between stories:

**Dependency Types:**
- Technical dependencies: 2 cases
- Business dependencies: 1 case
- Data dependencies: 1 case
- UI dependencies: 0 cases

**Critical Path:**
- US001 (User Login) → US004 (Product Search)
- US002 (User Registration) → US001 (User Login)

### CLI Command Examples

#### Story Generation
```text
# Generate user stories from requirements
ae-framework user-stories --generate --sources="requirements.md"

# Example output:
# ✅ User Story Generation Complete - 8 stories created across 3 epics
# 📊 Analysis:
#   • Total Stories: 8
#   • Total Epics: 3
#   • Total Story Points: 34
#   • Completeness Score: 85%
```

#### Story Validation
```text
# Validate user story quality
ae-framework user-stories --validate --sources="user-stories.md"

# Example output:
# ✅ Story Validation Complete - 7/8 stories are valid
# 📊 Quality Metrics:
#   • Proper Format: 90%
#   • Clear Acceptance Criteria: 70%
#   • Testable Stories: 85%
#   • Independent Stories: 80%
```

#### Prioritization
```text
# Prioritize stories
ae-framework user-stories --prioritize --sources="user-stories.md"

# Example output:
# ✅ Story Prioritization Complete - 8 stories prioritized
# 📊 Priority Matrix:
#   • High: 3 stories (high business value)
#   • Medium: 4 stories (medium business value)
#   • Low: 1 stories (low business value)
```

#### Estimation
```text
# Estimate story points
ae-framework user-stories --estimate --sources="user-stories.md"

# Example output:
# ✅ Story Estimation Complete - 34 total story points estimated
# 📊 Complexity Analysis:
#   • Simple Stories (1-3 points): 5 stories
#   • Medium Stories (5-8 points): 3 stories
#   • Complex Stories (13+ points): 0 stories
```

### Proactive Guidance

The User Stories Task Adapter automatically suggests interventions in these situations:

#### Incomplete Story Detection
```
⚠️ Warning: Incomplete user stories detected
💡 Recommendations:
  • Create comprehensive user stories
  • Define clear acceptance criteria
  • Estimate story complexity
```

#### Story Quality Issues
```
💡 Suggestion: User story quality can be improved
🔧 Actions:
  • Improve story structure and format
  • Add detailed acceptance criteria
  • Ensure stories are testable and independent
```

### TypeScript Interfaces

#### UserStory
```text
interface UserStory {
  id: string;
  title: string;
  description: string;
  asA: string;
  iWant: string;
  soThat: string;
  acceptanceCriteria: string[];
  priority: 'high' | 'medium' | 'low';
  storyPoints: number;
  epic?: string;
  dependencies: string[];
  testScenarios: string[];
}
```

#### UserStorySet
```text
interface UserStorySet {
  stories: UserStory[];
  epics: string[];
  totalStoryPoints: number;
  completenessScore: number;
  gaps: string[];
  conflicts: string[];
}
```

### Best Practices

#### Good User Story Characteristics (INVEST)
- **Independent**: Independent from other stories
- **Negotiable**: Details are negotiable
- **Valuable**: Provides value to users
- **Estimable**: Can be estimated
- **Small**: Appropriate size
- **Testable**: Can be tested

#### Acceptance Criteria Guidelines
1. **Clarity**: Eliminate ambiguity
2. **Measurability**: Objectively evaluable
3. **Completeness**: Cover all conditions
4. **Consistency**: No contradiction with other criteria

#### Epic Design Principles
1. **Business Value**: Clear value proposition
2. **Appropriate Size**: Completable in 1-4 weeks
3. **Independence**: Minimize dependencies with other epics
4. **Measurability**: Progress can be tracked

### Next Steps

After Phase 3 completion, proceed to these phases:

1. **Phase 4: Validation** - User story quality validation
2. **Phase 5: Domain Modeling** - Domain model design based on stories
3. **Phase 6: Test Generation** - Test case generation from stories

### Troubleshooting

#### Common Issues and Solutions

**Issue: Incorrect story format**
```text
# Execute story validation
ae-framework user-stories --validate --sources="stories.md"
```

**Issue: Difficult estimation**
```text
# More detailed story decomposition
ae-framework user-stories --generate --sources="detailed-requirements.md"
```

**Issue: Complex dependencies**
```text
# Execute dependency analysis
ae-framework user-stories --dependencies --sources="stories.md"
```

### Configuration and Customization

#### Story Template Customization
```text
const storyTemplate = {
  format: "As a {role}, I want {goal} so that {benefit}",
  acceptanceCriteriaFormat: "Given {context}, When {action}, Then {outcome}",
  priorities: ['high', 'medium', 'low'],
  storyPoints: [1, 2, 3, 5, 8, 13, 21]
};
```

#### Quality Metrics Adjustment
```text
const qualityThresholds = {
  formatCompliance: 90,      // Format compliance
  acceptanceCriteria: 80,    // Acceptance criteria
  testability: 85,           // Testability
  independence: 75           // Independence
};
```

---

## Japanese

**構造化された要件からの自動ユーザーストーリー生成・管理システム with Claude Code Task Tool統合**

### 概要

Phase 3では、構造化された要件からユーザーストーリーを生成し、管理するためのClaude Code Task Tool統合を提供します。アジャイル開発において重要な"As a... I want... So that..."形式のユーザーストーリーを自動生成し、品質を確保します。

## Claude Code Task Tool統合

### 自動呼び出し
Claude Codeがユーザーストーリー作成が必要と判断した場合、自動的にUser Stories Task Adapterが呼び出されます：

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

### 主要機能

#### 1. ストーリー生成（Story Generation）
要件からのユーザーストーリー自動作成：

**入力要件例:**
```
ユーザー認証機能
- ユーザーはメールアドレスとパスワードでログインできる
- パスワードはハッシュ化して保存される
- ログイン失敗は3回まで許可される
```

**生成されるストーリー例:**
```
US001: ユーザーログイン
As a registered user
I want to log into the system with my email and password
So that I can access my personalized dashboard

受入基準:
- ユーザーが有効なメールアドレスとパスワードを入力できる
- システムが認証情報を検証する
- 成功時にダッシュボードにリダイレクトされる
- 失敗時に適切なエラーメッセージが表示される

優先度: High
ストーリーポイント: 5
エピック: ユーザー管理
```

#### 2. ストーリー検証（Story Validation）
"As a... I want... So that..."形式の品質確保：

**検証項目:**
```text
interface QualityMetrics {
  formatCompliance: number;      // 形式準拠度: 90%
  acceptanceCriteria: number;    // 受入基準明確度: 70%
  testability: number;           // テスト可能性: 85%
  independence: number;          // 独立性: 80%
  estimability: number;          // 見積もり可能性: 75%
}
```

**一般的な問題:**
- 受入基準の欠如 (3件)
- 曖昧な表現 (2件)
- 依存関係の問題 (1件)

#### 3. 優先順位付け（Story Prioritization）
ビジネス価値に基づくストーリープライオリティ：

**優先度マトリックス:**
- **高優先度**: 3ストーリー (高ビジネス価値)
- **中優先度**: 4ストーリー (中ビジネス価値)
- **低優先度**: 1ストーリー (低ビジネス価値)

**リリース推奨:**
- **リリース 1.0**: 5ストーリー (8週間)
- **リリース 1.1**: 3ストーリー (4週間)

#### 4. 見積もり（Story Estimation）
ストーリーポイントによる複雑度評価：

**見積もり分布:**
- **1ポイント**: 2ストーリー (単純)
- **3ポイント**: 3ストーリー (単純)
- **5ポイント**: 2ストーリー (中程度)
- **8ポイント**: 1ストーリー (複雑)

**複雑度分析:**
- 単純ストーリー (1-3ポイント): 5ストーリー
- 中程度ストーリー (5-8ポイント): 3ストーリー
- 複雑ストーリー (13+ポイント): 0ストーリー

#### 5. 受入基準作成（Acceptance Criteria Creation）
Given-When-Then形式の詳細条件定義：

**例: ユーザーログインストーリー**
```
受入基準:
1. Given ユーザーが有効な認証情報を持っている
   When ログインフォームを送信する
   Then ダッシュボードにリダイレクトされる

2. Given ユーザーが無効な認証情報を入力した
   When ログインフォームを送信する
   Then エラーメッセージが表示される

3. Given ユーザーが3回ログインに失敗した
   When 4回目のログインを試行する
   Then アカウントが一時的にロックされる
```

**テストシナリオ:**
1. 有効ログインテスト (positive)
2. 無効認証テスト (negative)
3. アカウントロックテスト (edge case)

#### 6. エピック組織化（Epic Organization）
関連ストーリーのエピック単位での管理：

**エピック例:**
```
Epic: ユーザー管理
- US001: ユーザーログイン (5ポイント)
- US002: ユーザー登録 (8ポイント)
- US003: パスワードリセット (3ポイント)
総計: 16ポイント (推定2週間)

Epic: 商品管理
- US004: 商品検索 (5ポイント)
- US005: 商品詳細表示 (3ポイント)
総計: 8ポイント (推定1週間)
```

#### 7. 依存関係識別（Dependency Identification）
ストーリー間の技術的・ビジネス的依存関係：

**依存関係タイプ:**
- 技術的依存: 2件
- ビジネス的依存: 1件
- データ依存: 1件
- UI依存: 0件

**クリティカルパス:**
- US001 (ユーザーログイン) → US004 (商品検索)
- US002 (ユーザー登録) → US001 (ユーザーログイン)

## CLI コマンド使用例

### ストーリー生成
```text
# 要件からユーザーストーリーを生成
ae-framework user-stories --generate --sources="requirements.md"

# 出力例:
# ✅ User Story Generation Complete - 8 stories created across 3 epics
# 📊 Analysis:
#   • Total Stories: 8
#   • Total Epics: 3
#   • Total Story Points: 34
#   • Completeness Score: 85%
```

### ストーリー検証
```text
# ユーザーストーリーの品質検証
ae-framework user-stories --validate --sources="user-stories.md"

# 出力例:
# ✅ Story Validation Complete - 7/8 stories are valid
# 📊 Quality Metrics:
#   • Proper Format: 90%
#   • Clear Acceptance Criteria: 70%
#   • Testable Stories: 85%
#   • Independent Stories: 80%
```

### 優先順位付け
```text
# ストーリーの優先順位付け
ae-framework user-stories --prioritize --sources="user-stories.md"

# 出力例:
# ✅ Story Prioritization Complete - 8 stories prioritized
# 📊 Priority Matrix:
#   • High: 3 stories (high business value)
#   • Medium: 4 stories (medium business value)
#   • Low: 1 stories (low business value)
```

### 見積もり
```text
# ストーリーポイント見積もり
ae-framework user-stories --estimate --sources="user-stories.md"

# 出力例:
# ✅ Story Estimation Complete - 34 total story points estimated
# 📊 Complexity Analysis:
#   • Simple Stories (1-3 points): 5 stories
#   • Medium Stories (5-8 points): 3 stories
#   • Complex Stories (13+ points): 0 stories
```

## プロアクティブガイダンス

User Stories Task Adapterは、以下の状況で自動的に介入を提案します：

### 不完全なストーリーの検出
```
⚠️ Warning: Incomplete user stories detected
💡 Recommendations:
  • Create comprehensive user stories
  • Define clear acceptance criteria
  • Estimate story complexity
```

### ストーリー品質の問題
```
💡 Suggestion: User story quality can be improved
🔧 Actions:
  • Improve story structure and format
  • Add detailed acceptance criteria
  • Ensure stories are testable and independent
```

## TypeScript インターフェース

### UserStory
```text
interface UserStory {
  id: string;
  title: string;
  description: string;
  asA: string;
  iWant: string;
  soThat: string;
  acceptanceCriteria: string[];
  priority: 'high' | 'medium' | 'low';
  storyPoints: number;
  epic?: string;
  dependencies: string[];
  testScenarios: string[];
}
```

### UserStorySet
```text
interface UserStorySet {
  stories: UserStory[];
  epics: string[];
  totalStoryPoints: number;
  completenessScore: number;
  gaps: string[];
  conflicts: string[];
}
```

## ベストプラクティス

### 良いユーザーストーリーの特徴 (INVEST)
- **Independent**: 他のストーリーから独立している
- **Negotiable**: 詳細は交渉可能
- **Valuable**: ユーザーに価値を提供
- **Estimable**: 見積もり可能
- **Small**: 適切なサイズ
- **Testable**: テスト可能

### 受入基準のガイドライン
1. **明確性**: 曖昧さを排除
2. **測定可能性**: 客観的に評価可能
3. **完全性**: 全ての条件を網羅
4. **一貫性**: 他の基準と矛盾しない

### エピック設計の原則
1. **ビジネス価値**: 明確な価値提案
2. **適切なサイズ**: 1-4週間で完了可能
3. **独立性**: 他のエピックとの依存を最小化
4. **測定可能性**: 進捗が追跡可能

## 次のステップ

Phase 3完了後は、以下のフェーズに進みます：

1. **Phase 4: Validation** - ユーザーストーリーの品質検証
2. **Phase 5: Domain Modeling** - ストーリーに基づくドメインモデル設計
3. **Phase 6: Test Generation** - ストーリーからテストケース生成

## トラブルシューティング

### よくある問題と解決策

**問題: ストーリーの形式が正しくない**
```text
# ストーリー検証の実行
ae-framework user-stories --validate --sources="stories.md"
```

**問題: 見積もりが困難**
```text
# より詳細なストーリー分解
ae-framework user-stories --generate --sources="detailed-requirements.md"
```

**問題: 依存関係が複雑**
```text
# 依存関係分析の実行
ae-framework user-stories --dependencies --sources="stories.md"
```

## 設定とカスタマイズ

### ストーリーテンプレートのカスタマイズ
```text
const storyTemplate = {
  format: "As a {role}, I want {goal} so that {benefit}",
  acceptanceCriteriaFormat: "Given {context}, When {action}, Then {outcome}",
  priorities: ['high', 'medium', 'low'],
  storyPoints: [1, 2, 3, 5, 8, 13, 21]
};
```

### 品質メトリクスの調整
```text
const qualityThresholds = {
  formatCompliance: 90,      // 形式準拠度
  acceptanceCriteria: 80,    // 受入基準
  testability: 85,           // テスト可能性
  independence: 75           // 独立性
};
```