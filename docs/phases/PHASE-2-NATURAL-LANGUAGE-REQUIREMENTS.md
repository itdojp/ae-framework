---
docRole: ssot
lastVerified: 2026-03-11
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 2: Natural Language Requirements

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Natural language requirements structuring and analysis system with Claude Code Task Tool integration**

### Overview

Phase 2 provides Claude Code Task Tool integration for structuring and analyzing requirements written in natural language. This phase aims to systematically organize scattered requirement information and convert it into formats usable by subsequent phases.

### Claude Code Task Tool Integration

#### Automatic Invocation
When Claude Code determines that natural language requirements processing is needed, the Natural Language Task Adapter is automatically invoked:

```
User: Please structure this requirements document

Claude Code: Executing Natural Language Task Adapter...

✅ Requirements Analysis - 15 requirements identified
📊 Analysis:
  • Functional Requirements: 10
  • Non-Functional Requirements: 3
  • Business Requirements: 2
```

### Key Features

#### 1. Requirements Analysis
Extracting structured requirements from natural language text:

**Input Example:**
```
The system must allow users to register accounts.
Login functionality should be secure and fast.
Payment processing needs to be reliable.
The interface should be user-friendly.
```

**Structured Output:**
```text
interface RequirementAnalysisResult {
  functional: FunctionalRequirement[];    // 2 requirements
  nonFunctional: NonFunctionalRequirement[]; // 2 requirements  
  business: BusinessRequirement[];        // 0 requirements
  technical: TechnicalRequirement[];      // 0 requirements
}
```

**Analysis Results:**
- **Functional Requirements**: User registration, Login functionality
- **Non-functional Requirements**: Security and performance, Reliability
- **Quality Attributes**: Usability, Security, Performance

#### 2. Requirement Categorization
Systematic classification of requirements by type and priority:

**Category Types:**
```text
enum RequirementType {
  FUNCTIONAL = 'functional',
  NON_FUNCTIONAL = 'non_functional', 
  BUSINESS = 'business',
  TECHNICAL = 'technical',
  CONSTRAINT = 'constraint'
}
```

**Priority Levels:**
- **High Priority**: Core functionality, Security requirements
- **Medium Priority**: Performance enhancements, Usability features
- **Low Priority**: Nice-to-have features, Future enhancements

#### 3. Ambiguity Detection
Identifying and resolving ambiguous or incomplete requirements:

**Ambiguity Types:**
- **Unclear Terms**: "fast", "user-friendly", "reliable"
- **Missing Details**: Incomplete specifications
- **Contradictions**: Conflicting requirements
- **Assumptions**: Implicit requirements

**Resolution Process:**
```text
interface AmbiguityResolution {
  original: string;
  issues: AmbiguityIssue[];
  suggestions: string[];
  clarificationQuestions: string[];
}
```

#### 3.1 DbC extraction (pre/post/invariant)
For each requirement or use-case, extract Design by Contract (DbC) statements with stable IDs.

```text
interface DbcExtractionItem {
  id: string; // PRE-*, POST-*, INV-*
  requirementRef: string;
  statement: string;
  type: 'precondition' | 'postcondition' | 'invariant';
  violationBehavior: string;
}
```

Example:
- PRE-LOGIN-001: Login input must include non-empty email/password.
- POST-LOGIN-001: Successful login creates an auditable session record.
- INV-SEC-001: Locked accounts never receive active sessions.

#### 3.2 Clarification question template (DbC-oriented)
When ambiguous terms like "fast", "reliable", "secure" are found, ask:
- **precondition**: Which inputs/states are accepted? How should invalid input be rejected?
- **postcondition**: What must be true after execution? Which side effects are expected?
- **invariant**: What must always hold? What is the recovery behavior on violation?

#### 3.3 Verification linkage (minimum)
- Preconditions -> request validation / negative tests / type guards
- Postconditions -> unit/integration assertions for state/events
- Invariants -> property tests / runtime conformance / DB constraints

#### 4. Requirements Validation
Ensuring completeness and consistency of requirements:

**Validation Checks:**
- **Completeness**: All necessary requirements covered
- **Consistency**: No conflicting requirements
- **Feasibility**: Technically achievable
- **Testability**: Verifiable requirements

**Validation Score: 85%**
- Completeness: 90%
- Consistency: 85%
- Feasibility: 80%
- Testability: 85%

#### 5. Formal Specification Generation
Converting natural language requirements to formal specifications:

**Specification Types:**
```text
interface FormalSpecification {
  tlaPlus: TLASpecification;      // TLA+ formal specification
  contracts: ContractSpec[];      // Pre/post conditions
  stateMachines: StateMachine[];  // Behavioral specifications
  interfaces: InterfaceSpec[];    // API specifications
}
```

**Example TLA+ Generation:**
```tla
EXTENDS Naturals, Sequences

VARIABLES users, sessions, loginAttempts

UserRegistration ==
  /\ users' = users \cup {newUser}
  /\ newUser \notin users
  /\ IsValidEmail(newUser.email)
```

#### 6. Documentation Generation
Creating comprehensive requirement documentation:

**Document Types:**
- **Requirements Specification Document (RSD)**
- **System Requirements Specification (SRS)**
- **Functional Requirements Document (FRD)**
- **Non-Functional Requirements (NFR) Document**

**Generated Sections:**
- Introduction and scope
- Functional requirements with examples
- Non-functional requirements with metrics
- Constraints and assumptions
- Acceptance criteria
- Traceability matrix

### CLI Command Examples

#### Requirements Analysis
```text
# Analyze natural language requirements
ae-framework phase-2 --analyze --source="requirements.txt"

# Example output:
# ✅ Requirements Analysis Complete - 15 requirements identified
# 📊 Breakdown:
#   • Functional: 10 requirements
#   • Non-Functional: 3 requirements
#   • Business: 2 requirements
```

#### Requirement Validation
```text
# Validate requirements completeness and consistency
ae-framework phase-2 --validate --source="requirements.md"

# Example output:
# ✅ Validation Complete - 85% validation score
# 📊 Results:
#   • Completeness: 90%
#   • Consistency: 85%
#   • Feasibility: 80%
```

#### Formal Specification Generation
```text
# Generate formal specifications
ae-framework phase-2 --formal --source="validated-requirements.json"

# Example output:
# ✅ Formal Specification Generated
# 📊 Generated:
#   • TLA+ specifications: 3 files
#   • Contract specifications: 5 contracts
#   • State machines: 2 machines
```

### Proactive Guidance

The Natural Language Task Adapter automatically suggests interventions in these situations:

#### Incomplete Requirements Detection
```
⚠️ Warning: Requirements appear incomplete
💡 Recommendations:
  • Add missing functional requirements
  • Define acceptance criteria
  • Specify non-functional requirements
```

#### Ambiguity Detection
```
💡 Suggestion: Ambiguous requirements detected
🔧 Actions:
  • Clarify unclear terms
  • Add specific metrics
  • Define acceptance criteria
```

### TypeScript Interfaces

#### RequirementAnalysisResult
```text
interface RequirementAnalysisResult {
  functional: FunctionalRequirement[];
  nonFunctional: NonFunctionalRequirement[];
  business: BusinessRequirement[];
  technical: TechnicalRequirement[];
  constraints: Constraint[];
  assumptions: Assumption[];
}
```

#### FormalSpecification
```text
interface FormalSpecification {
  tlaPlus: TLASpecification;
  contracts: ContractSpecification[];
  stateMachines: StateMachineSpecification[];
  interfaces: InterfaceSpecification[];
}
```

### Best Practices

#### Effective Requirement Writing
1. **Clarity**: Use clear, unambiguous language
2. **Completeness**: Include all necessary details
3. **Consistency**: Avoid contradictions
4. **Traceability**: Link to business objectives
5. **Testability**: Define verifiable criteria

#### Natural Language Guidelines
1. **Active Voice**: Use active rather than passive voice
2. **Specific Terms**: Avoid vague terms like "fast" or "user-friendly"
3. **Quantifiable Metrics**: Include specific measurements where possible
4. **Structured Format**: Use consistent formatting and templates

### Integration with Phase 1 and Phase 3

#### Input from Phase 1 (Intent Analysis)
- Analyzed user intentions
- Identified ambiguities
- Extracted context and constraints
- Prioritized requirements

#### Output to Phase 3 (User Stories)
- Structured requirements
- Formal specifications
- Validation results
- Documentation artifacts

### Advanced Features

#### Machine Learning Integration
- **Requirement Classification**: Automatic categorization using ML models
- **Similarity Detection**: Finding related requirements
- **Quality Prediction**: Predicting requirement quality scores

#### Collaborative Features
- **Multi-stakeholder Input**: Support for multiple requirement sources
- **Review Workflows**: Systematic requirement review processes
- **Change Management**: Tracking requirement evolution

---

## Japanese

**自然言語要件の構造化・分析システム with Claude Code Task Tool統合**

## 概要

Phase 2では、自然言語で記述された要件を構造化し、分析するためのClaude Code Task Tool統合を提供します。このフェーズは、散在する要件情報を体系的に整理し、後続フェーズで利用可能な形式に変換することを目的としています。

## Claude Code Task Tool統合

### 自動呼び出し
Claude Codeが自然言語要件処理が必要と判断した場合、自動的にNatural Language Task Adapterが呼び出されます：

```
User: この要件ドキュメントを構造化してください

Claude Code: Natural Language Task Adapterを実行中...

✅ Requirements Analysis - 15 requirements identified
📊 Analysis:
  • Functional Requirements: 10
  • Non-Functional Requirements: 3
  • Business Requirements: 2
```

### 主要機能

#### 1. 要件分析（Requirements Analysis）
自然言語テキストから構造化要件を抽出：

**入力例:**
```
システムはユーザーがログインできる必要があります。
パスワードは暗号化されて保存されるべきです。
システムは2秒以内にレスポンスする必要があります。
```

**出力:**
- 機能要件: ユーザーログイン機能
- 技術要件: パスワード暗号化
- 非機能要件: 2秒以内のレスポンス時間

#### 2. エンティティ抽出（Entity Extraction）
ビジネスエンティティとその関係性を特定：

**抽出される情報:**
```text
interface BusinessEntity {
  name: string;
  type: 'core' | 'supporting';
  description: string;
  relationships?: string[];
}
```

**例:**
- User (core): システムユーザーエンティティ
- Profile (supporting): ユーザープロフィール情報
- 関係性: User has Profile

#### 3. 完全性検証（Completeness Validation）
要件の網羅性と欠落項目の特定：

**検証項目:**
- 機能要件カバレッジ: 80%
- 非機能要件カバレッジ: 60%
- ビジネスルールカバレッジ: 70%
- UIカバレッジ: 50%
- データ要件カバレッジ: 65%

**欠落要素の例:**
- エラーハンドリング要件
- パフォーマンスベンチマーク
- セキュリティ制約

#### 4. 曖昧性解決（Ambiguity Resolution）
不明確な要件の特定と明確化提案：

**曖昧な表現の例:**
- "システムは高速である必要がある" → "システムは2秒以内に応答する必要がある"
- "ユーザーフレンドリーなUI" → "3クリック以内で主要機能にアクセス可能"

#### 4.1 DbC 3条件抽出（pre/post/invariant）
各要件・ユースケースごとに DbC を抽出し、IDを付与します。

- Preconditions（PRE-*）: 入力制約、前提状態、許容範囲
- Postconditions（POST-*）: 事後状態、観測可能な副作用、出力保証
- Invariants（INV-*）: 常時成立する整合性制約、セキュリティ制約

最小出力例:

```text
dbc:
  - id: PRE-ORDER-001
    type: precondition
    requirementRef: FR-ORDER-01
    statement: "注文数量は1以上"
    violationBehavior: "400 Bad Request"
  - id: POST-ORDER-001
    type: postcondition
    requirementRef: FR-ORDER-01
    statement: "注文確定後に在庫が減算される"
    violationBehavior: "トランザクションをロールバック"
  - id: INV-STOCK-001
    type: invariant
    requirementRef: FR-ORDER-01
    statement: "在庫は負数にならない"
    violationBehavior: "監視アラート + 補正ジョブ"
```

#### 4.2 確認質問テンプレ（DbC）
曖昧語彙（例: fast / reliable / secure）を検出したら、以下を確認します。

- pre: どの入力/状態を許容するか。違反時は reject / error / no-op のどれか。
- post: 実行後に必ず満たす状態は何か。副作用（DB/イベント/ログ）は何か。
- invariant: 常時守る整合性は何か。違反時に停止/回復/通知のどれを行うか。

#### 4.3 テスト/ゲートへの接続（最小）
- pre/post: unit・integration の assertion と negative test に接続
- invariant: property test / runtime conformance / DB制約 に接続

#### 5. 要件構造化（Requirements Structuring）
要件のカテゴリ分類と優先度設定：

**カテゴリ例:**
- ユーザー管理: 5要件
- データ処理: 8要件
- セキュリティ: 3要件

**優先度分布:**
- 高優先度: 6要件
- 中優先度: 7要件
- 低優先度: 2要件

#### 6. ギャップ識別（Gap Identification）
要件間の矛盾と欠落の検出：

**ギャップの例:**
- セキュリティ: 認証要件の欠如
- パフォーマンス: 負荷要件の未定義
- 運用: バックアップ要件の不足

## CLI コマンド使用例

### 基本的な要件分析
```text
# 要件ドキュメントの分析
ae-framework natural-language --analyze --sources="requirements.md"

# 出力例:
# ✅ Requirements Analysis - 15 requirements identified
# 📊 Analysis:
#   • Functional Requirements: 10
#   • Non-Functional Requirements: 3
#   • Business Requirements: 2
```

### エンティティ抽出
```text
# ビジネスエンティティの抽出
ae-framework natural-language --extract-entities --sources="requirements.md"

# 出力例:
# ✅ Entity Extraction Complete - 6 entities identified
# 📊 Analysis:
#   • Core Entities: 4
#   • Supporting Entities: 2
#   • Relationships: 8
```

### 完全性検証
```text
# 要件の完全性チェック
ae-framework natural-language --validate-completeness --sources="requirements.md"

# 出力例:
# ✅ Completeness Validation - 75% complete
# ⚠️ Warnings:
#   • Low completeness score - significant gaps detected
# 💡 Recommendations:
#   • Add performance requirements
#   • Specify security constraints
```

## プロアクティブガイダンス

Natural Language Task Adapterは、以下の状況で自動的に介入を提案します：

### 不完全な要件の検出
```
⚠️ Warning: Incomplete requirements detected
💡 Recommendations:
  • Create comprehensive requirements specification
  • Analyze stakeholder needs thoroughly
  • Document functional and non-functional requirements
```

### 曖昧な要件の検出
```
💡 Suggestion: Ambiguous requirements found
🔧 Actions:
  • Clarify ambiguous requirement statements
  • Define specific acceptance criteria
  • Validate understanding with stakeholders
```

## TypeScript インターフェース

### TaskRequest
```text
interface TaskRequest {
  description: string;
  prompt: string;
  subagent_type: string;
}
```

### TaskResponse
```text
interface TaskResponse {
  summary: string;
  analysis: string;
  recommendations: string[];
  nextActions: string[];
  warnings: string[];
  shouldBlockProgress: boolean;
}
```

### ProcessedRequirements
```text
interface ProcessedRequirements {
  structured: RequirementDocument[];
  summary: string;
  gaps: string[];
  conflicts: string[];
  ambiguities: string[];
  clarificationNeeded: string[];
}
```

## 関連テンプレート / 関連ガイド

- `docs/templates/plan-to-spec-normalization-template.md`
- `docs/guides/context-bundle.md`
- `docs/quality/verification-gates.md`

## 次のステップ

Phase 2完了後は、以下のフェーズに進みます：

1. **Phase 3: User Stories Creation** - 構造化された要件からユーザーストーリーを生成
2. **Phase 4: Validation** - 要件とストーリーの品質検証
3. **Phase 5: Domain Modeling** - ドメインモデルの設計

## トラブルシューティング

### よくある問題と解決策

**問題: 要件の抽出精度が低い**
```text
# より詳細な要件パターンを使用
ae-framework natural-language --analyze --sources="detailed-requirements.md"
```

**問題: エンティティの関係性が不明確**
```text
# エンティティ抽出の再実行
ae-framework natural-language --extract-entities --sources="updated-requirements.md"
```

**問題: 完全性スコアが低い**
```text
# ギャップ分析の実行
ae-framework natural-language --validate-completeness --sources="all-requirements.md"
```

## 設定とカスタマイズ

### 要件パターンのカスタマイズ
要件抽出パターンは`src/agents/natural-language-task-adapter.ts`で設定可能：

```text
const requirementPatterns = [
  /^\\s*[-*+]\\s+(.+)/,                    // Markdown bullet points
  /^\\s*\\d+[\\.\\)]\\s+(.+)/,            // Numbered lists
  /^\\s*•\\s+(.+)/,                       // Unicode bullet
  /^\\s*Requirement\\s*\\d*[:\\-\\.]?\\s*(.+)/i, // "Requirement 1: ..."
  /^\\s*(The system|System|It|Software|Application)\\s+(shall|must|should|will)\\b(.+)/i
];
```

### 検証閾値の調整
完全性検証の閾値は設定可能：

```text
const COMPLETENESS_THRESHOLDS = {
  critical: 50,    // 進行をブロックする閾値
  warning: 70,     // 警告を表示する閾値
  good: 85         // 良好とみなす閾値
};
```
