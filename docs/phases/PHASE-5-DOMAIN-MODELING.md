---
docRole: ssot
lastVerified: 2026-03-11
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 5: Domain Modeling

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Comprehensive domain modeling system using Domain-Driven Design (DDD) principles with Claude Code Task Tool integration**

### Overview

Phase 5 provides Claude Code Task Tool integration for domain modeling through Domain-Driven Design (DDD). Based on validated requirements and stories, it designs robust and maintainable domain models.

### Claude Code Task Tool Integration

#### Automatic Invocation
When Claude Code determines domain modeling is needed, the Domain Modeling Task Adapter is automatically invoked:

```
User: Please design a domain model

Claude Code: Designing with Domain Modeling Task Adapter...

✅ Domain Analysis Complete - 6 entities, 2 bounded contexts identified
📊 Analysis:
  • Core Domain Entities: 4
  • Bounded Contexts: 2
  • Business Rules: 12
  • Domain Services: 3
```

#### Input Extraction (Mixed Language Prompts)
`DomainModelingTaskAdapter` extracts structured input from both English and Japanese prompt sections.

Example prompt:
```text
Identify entities for reservation domain.
Entities: Customer, Reservation, Inventory
ビジネスルール: 在庫は0未満にできない, 重複予約は禁止
Domain Services: ReservationService
```

Extracted fields (conceptual):
- `taskType`: `identify-entities`
- `entities`: `Customer`, `Reservation`, `Inventory`
- `businessRules`: `在庫は0未満にできない`, `重複予約は禁止`
- `domainServices`: `ReservationService`

### Key Features

#### 1. Domain Analysis
Comprehensive business domain analysis:

**Analysis Results:**
```text
interface DomainAnalysisResult {
  entities: DomainEntity[];           // 6 entities
  boundedContexts: BoundedContext[];  // 2 bounded contexts
  businessRules: BusinessRule[];      // 12 business rules
  domainServices: DomainService[];    // 3 domain services
}
```

**Core Domain Entities:**
- **User** (entity): System user entity
- **Order** (aggregate): Customer order aggregate
- **Product** (entity): Product entity
- **Payment** (value object): Payment information

**Bounded Context Overview:**
- **User Management**: User operation processing (3 entities)
- **Order Processing**: Order processing workflow (4 entities)

**Critical Business Rules:**
- **Email Validation**: Email address uniqueness constraint
- **Order Total Calculation**: Order total calculation logic
- **Payment Authorization**: Payment authorization process

**Domain Complexity Analysis:**
- High complexity areas: Order Processing
- Medium complexity areas: User Management, Payment
- Simple areas: Product Catalog

#### 2. Entity Identification
Domain entity identification and classification:

**Entity Classification:**
```text
interface DomainEntity {
  name: string;
  type: 'aggregate' | 'entity' | 'value_object' | 'service' | 'repository';
  description: string;
  attributes: EntityAttribute[];
  methods: EntityMethod[];
  relationships: EntityRelationship[];
  businessRules: string[];
  invariants: string[];
}
```

**Identified Entities:**
- **Aggregate Roots**: Order, User
- **Value Objects**: Email, Address, Money
- **Domain Services**: OrderService, PaymentService

**Entity Relationships:**
- User has Profile (1:1)
- Order contains OrderItem (1:many)
- Product belongs to Category (many:1)

**Business Rule Coverage:**
- **User**: 3 business rules
- **Order**: 5 business rules
- **Product**: 2 business rules

#### 3. Aggregate Modeling
Definition of aggregate roots and boundaries:

**Aggregate Details:**
```text
interface AggregateRoot {
  name: string;              // Order
  description: string;       // Customer order aggregate
  entities: string[];        // [OrderItem, ShippingInfo]
  valueObjects: string[];    // [Money, Quantity]
  businessRules: string[];   // [Order total calculation]
  invariants: string[];     // [Order must have at least one item]
}
```

**Aggregate Boundary Analysis:**
- **Order**: Strong boundary (85% coupling)
- **User**: Strong boundary (90% coupling)
- **Product**: Medium boundary (70% coupling)

**Inter-Aggregate Dependencies:**
- Order → User (customer reference)
- Order → Product (product reference)
- Payment → Order (order reference)

#### 4. Bounded Context Definition
Clarification of microservice boundaries:

**Context Definition:**
```text
interface BoundedContext {
  name: string;                    // Sales
  description: string;             // Sales and order management
  entities: string[];              // [Order, Customer]
  services: string[];              // [OrderService]
  responsibilities: string[];      // [Order processing, Customer management]
  interfaces: ContextInterface[];  // API definition
}
```

**Context Relationships:**
- **Sales** → **Inventory** (customer-supplier)
- **Payment** → **Sales** (conformist)
- **Shipping** → **Sales** (anticorruption layer)

**Integration Patterns:**
- **Sales ↔ Inventory**: Event Sourcing (inventory update with order events)
- **Payment ↔ Sales**: Command/Query (payment commands and queries)

#### 5. Business Rule Extraction
Identification of domain-specific business logic:

**Business Rule Analysis:**
```text
interface BusinessRule {
  id: string;                 // BR001
  name: string;               // Order Validation
  description: string;        // Orders must have valid customer and items
  type: 'constraint' | 'derivation' | 'existence' | 'action_enabler';
  entities: string[];         // [Order, Customer, OrderItem]
  conditions: string[];       // [Customer exists, Items available]
  actions: string[];          // [Create order, Update inventory]
}
```

**High Priority Rules:**
- **Order Validation**: Orders require valid customer and products
- **Payment Authorization**: Payments require pre-authorization
- **Inventory Check**: Product reservation after inventory verification

**Rule Complexity Analysis:**
- **Order Validation**: Medium complexity (2 dependencies)
- **Payment Authorization**: High complexity (4 dependencies)
- **Inventory Check**: Low complexity (1 dependency)

**Entity-Rule Mapping:**
- **Order**: 5 rules
- **Payment**: 3 rules
- **User**: 2 rules

#### 6. Ubiquitous Language Creation
Building a shared vocabulary dictionary for the team:

**Core Domain Terms:**
```text
interface UbiquitousLanguageTerm {
  term: string;           // Order
  definition: string;     // Customer request for products
  context: string;        // Sales
  synonyms: string[];     // [Purchase, Request]
  relatedTerms: string[]; // [OrderItem, Customer]
}
```

**Key Terms:**
- **Order**: Customer's product purchase request (Context: Sales)
- **Customer**: User as customer in the system (Context: Sales)
- **Product**: Sellable merchandise (Context: Catalog)

**Term Relationships:**
- **Order** contains **OrderItem**
- **Customer** places **Order**
- **Product** belongs to **Category**

#### 7. Domain Service Design
Service design spanning multiple entities:

**Service Definition:**
```text
interface DomainService {
  name: string;               // OrderService
  description: string;        // Order processing service
  operations: ServiceOperation[];
  dependencies: string[];     // [PaymentService, InventoryService]
}
```

**Service Operations:**
```text
interface ServiceOperation {
  name: string;           // processOrder
  description: string;    // Process customer order
  inputs: Parameter[];    // [order: Order]
  outputs: Parameter[];   // [result: OrderResult]
  businessRule: string;   // Validate order before processing
}
```

**Service Dependency Analysis:**
- **OrderService**: 2 dependencies (medium coupling)
- **PaymentService**: 1 dependency (low coupling)
- **InventoryService**: 3 dependencies (high coupling)

**Service Coupling Analysis:**
- **OrderService**: 85% coupling (3 responsibilities)
- **PaymentService**: 95% coupling (1 responsibility)
- **InventoryService**: 70% coupling (4 responsibilities)

#### 8. Domain Model Validation
Domain model consistency and completeness validation:

**Validation Score: 85%**

**Validation Items:**
- Entity validation: 90%
- Relationship validation: 80%
- Business rule validation: 85%

**Validation Issues:**
- Medium importance: Some relationships lack cardinality (relationships)
- Low importance: Entity naming consistency (naming)

**Model Completeness:**
- Entities: 90%
- Relationships: 80%
- Business rules: 85%
- Bounded contexts: 75%

**Consistency Check:**
- Entity names: Pass (0 issues)
- Relationship definitions: Pass (1 issue)
- Business rules: Pass (0 issues)

### CLI Command Examples

#### Domain Analysis
```text
# Comprehensive domain analysis
ae-framework domain-model --analyze --sources="requirements.md,user-stories.md"

# Example output:
# ✅ Domain Analysis Complete - 6 entities, 2 bounded contexts identified
# 📊 Analysis:
#   • Core Domain Entities: 4
#   • Bounded Contexts: 2
#   • Business Rules: 12
```

#### Entity Identification
```text
# Domain entity identification
ae-framework domain-model --entities --sources="domain-requirements.md"

# Example output:
# ✅ Entity Identification Complete - 8 entities identified
# 📊 Classification:
#   • Aggregate Roots: 3
#   • Value Objects: 2
#   • Domain Services: 3
```

#### Aggregate Modeling
```text
# Aggregate design and boundary definition
ae-framework domain-model --aggregates --sources="entities.md"

# Example output:
# ✅ Aggregate Modeling Complete - 3 aggregates defined
# 📊 Boundary Analysis:
#   • Strong boundaries: 2
#   • Medium boundaries: 1
```

#### Bounded Context Definition
```text
# Bounded context design
ae-framework domain-model --contexts --sources="domain-analysis.md"

# Example output:
# ✅ Bounded Context Definition Complete - 3 contexts defined
# 📊 Integration Patterns:
#   • Event Sourcing: 2
#   • Command/Query: 1
```

### Proactive Guidance

The Domain Modeling Task Adapter automatically suggests interventions in these situations:

#### Incomplete Modeling Detection
```
⚠️ Warning: Domain model appears incomplete
💡 Recommendations:
  • Create comprehensive entity models
  • Define aggregate boundaries
  • Establish bounded contexts
```

#### Modeling Inconsistency Detection
```
💡 Suggestion: Domain model inconsistencies detected
🔧 Actions:
  • Review entity relationships
  • Validate business rule consistency
  • Check ubiquitous language usage
```

#### Model Improvement Suggestions
```
💡 Suggestion: Consider refining domain model
🔧 Actions:
  • Update domain model based on new requirements
  • Refine entity definitions
  • Adjust aggregate boundaries if needed
```

### TypeScript Interfaces

#### DomainEntity
```text
interface DomainEntity {
  name: string;
  type: 'aggregate' | 'entity' | 'value_object' | 'service' | 'repository';
  description: string;
  attributes: EntityAttribute[];
  methods: EntityMethod[];
  relationships: EntityRelationship[];
  businessRules: string[];
  invariants: string[];
}
```

#### BoundedContext
```text
interface BoundedContext {
  name: string;
  description: string;
  entities: string[];
  services: string[];
  responsibilities: string[];
  interfaces: ContextInterface[];
}
```

#### BusinessRule
```text
interface BusinessRule {
  id: string;
  name: string;
  description: string;
  type: 'constraint' | 'derivation' | 'existence' | 'action_enabler';
  entities: string[];
  conditions: string[];
  actions: string[];
}
```

### DDD Best Practices

#### Entity Design Principles
1. **Uniqueness**: Each entity has a unique identifier
2. **Invariants**: Clearly define entity invariants
3. **Lifecycle**: Manage from creation to deletion
4. **Clear Responsibility**: Follow single responsibility principle

#### Aggregate Design Principles
1. **Consistency Boundaries**: Aggregates as transaction boundaries
2. **Keep Small**: Design aggregates as small as possible
3. **Reference by ID**: Other aggregates referenced by ID only
4. **Eventual Consistency**: Allow eventual consistency between aggregates

#### Bounded Context Design Principles
1. **Team Boundaries**: Align with development team responsibilities
2. **Language Boundaries**: Ubiquitous language application scope
3. **Technical Boundaries**: Technology stack and data store boundaries
4. **Evolution Boundaries**: Independent release cycles

### Next Steps

After Phase 5 completion, proceed to these phases:

1. **Phase 6: Test Generation** - Test design based on domain models
2. **Phase 7: Code Generation** - Implementation generation from domain models
3. **Phase 8: Implementation** - Implementation based on DDD patterns

### Troubleshooting

#### Common Issues and Solutions

**Issue: Unclear entity boundaries**
```text
# More detailed domain analysis
ae-framework domain-model --analyze --entities --sources="detailed-requirements.md"
```

**Issue: Aggregates too large**
```text
# Aggregate redesign
ae-framework domain-model --aggregates --sources="refined-entities.md"
```

**Issue: Complex business rules**
```text
# Business rule analysis and simplification
ae-framework domain-model --rules --sources="business-requirements.md"
```

### Configuration and Customization

#### Domain Modeling Configuration
```text
const domainModelingConfig = {
  maxEntitiesPerAggregate: 7,        // Maximum entities per aggregate
  maxBusinessRulesPerEntity: 5,      // Maximum rules per entity
  enforceUbiquitousLanguage: true,   // Enforce ubiquitous language
  validateInvariants: true           // Validate invariants
};
```

#### Complexity Threshold Adjustment
```text
const complexityThresholds = {
  lowComplexity: 3,      // Low complexity upper limit
  mediumComplexity: 7,   // Medium complexity upper limit
  highComplexity: 10     // High complexity upper limit
};
```

---

## Japanese

**ドメイン駆動設計（DDD）原則を用いたClaude Code Task Tool統合による包括的ドメインモデリングシステム**

### 概要

Phase 5では、ドメイン駆動設計（DDD）によるドメインモデリングを行うためのClaude Code Task Tool統合を提供します。検証済みの要件とストーリーに基づいて、堅牢で保守性の高いドメインモデルを設計します。

## Claude Code Task Tool統合

### 自動呼び出し
Claude Codeがドメインモデリングが必要と判断した場合、自動的にDomain Modeling Task Adapterが呼び出されます：

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

### 入力抽出（日本語/英語混在プロンプト）
`DomainModelingTaskAdapter` は、日本語と英語が混在するプロンプトから構造化入力を抽出します。

入力例:
```text
Identify entities for reservation domain.
Entities: Customer, Reservation, Inventory
ビジネスルール: 在庫は0未満にできない, 重複予約は禁止
Domain Services: ReservationService
```

抽出される主な項目（概念）:
- `taskType`: `identify-entities`
- `entities`: `Customer`, `Reservation`, `Inventory`
- `businessRules`: `在庫は0未満にできない`, `重複予約は禁止`
- `domainServices`: `ReservationService`

### 主要機能

#### 1. ドメイン分析（Domain Analysis）
ビジネスドメインの包括的分析：

**分析結果例:**
```text
interface DomainAnalysisResult {
  entities: DomainEntity[];           // 6エンティティ
  boundedContexts: BoundedContext[];  // 2境界コンテキスト
  businessRules: BusinessRule[];      // 12ビジネスルール
  domainServices: DomainService[];    // 3ドメインサービス
}
```

**コアドメインエンティティ:**
- **User** (entity): システムユーザーエンティティ
- **Order** (aggregate): 顧客注文集約
- **Product** (entity): 商品エンティティ
- **Payment** (value object): 決済情報

**境界コンテキスト概要:**
- **User Management**: ユーザー操作処理 (3エンティティ)
- **Order Processing**: 注文処理ワークフロー (4エンティティ)

**重要なビジネスルール:**
- **Email Validation**: メールアドレスの一意性制約
- **Order Total Calculation**: 注文合計の計算ロジック
- **Payment Authorization**: 決済承認プロセス

**ドメイン複雑度分析:**
- 高複雑度エリア: Order Processing
- 中複雑度エリア: User Management, Payment
- 単純エリア: Product Catalog

#### 2. エンティティ識別（Entity Identification）
ドメインエンティティとその分類：

**エンティティ分類:**
```text
interface DomainEntity {
  name: string;
  type: 'aggregate' | 'entity' | 'value_object' | 'service' | 'repository';
  description: string;
  attributes: EntityAttribute[];
  methods: EntityMethod[];
  relationships: EntityRelationship[];
  businessRules: string[];
  invariants: string[];
}
```

**識別されたエンティティ:**
- **集約ルート**: Order, User
- **値オブジェクト**: Email, Address, Money
- **ドメインサービス**: OrderService, PaymentService

**エンティティ関係:**
- User has Profile (1:1)
- Order contains OrderItem (1:many)
- Product belongs to Category (many:1)

**ビジネスルールカバレッジ:**
- **User**: 3ビジネスルール
- **Order**: 5ビジネスルール
- **Product**: 2ビジネスルール

#### 3. 集約モデリング（Aggregate Modeling）
集約ルートと境界の定義：

**集約詳細:**
```text
interface AggregateRoot {
  name: string;              // Order
  description: string;       // Customer order aggregate
  entities: string[];        // [OrderItem, ShippingInfo]
  valueObjects: string[];    // [Money, Quantity]
  businessRules: string[];   // [Order total calculation]
  invariants: string[];     // [Order must have at least one item]
}
```

**集約境界分析:**
- **Order**: 強境界 (85%結合度)
- **User**: 強境界 (90%結合度)
- **Product**: 中境界 (70%結合度)

**集約間依存関係:**
- Order → User (customer reference)
- Order → Product (product reference)
- Payment → Order (order reference)

#### 4. 境界コンテキスト定義（Bounded Context Definition）
マイクロサービス境界の明確化：

**コンテキスト定義:**
```text
interface BoundedContext {
  name: string;                    // Sales
  description: string;             // Sales and order management
  entities: string[];              // [Order, Customer]
  services: string[];              // [OrderService]
  responsibilities: string[];      // [Order processing, Customer management]
  interfaces: ContextInterface[];  // API定義
}
```

**コンテキスト関係:**
- **Sales** → **Inventory** (customer-supplier)
- **Payment** → **Sales** (conformist)
- **Shipping** → **Sales** (anticorruption layer)

**統合パターン:**
- **Sales ↔ Inventory**: Event Sourcing (注文イベントで在庫更新)
- **Payment ↔ Sales**: Command/Query (決済コマンドと照会)

#### 5. ビジネスルール抽出（Business Rule Extraction）
ドメイン固有のビジネスロジック特定：

**ビジネスルール分析:**
```text
interface BusinessRule {
  id: string;                 // BR001
  name: string;               // Order Validation
  description: string;        // Orders must have valid customer and items
  type: 'constraint' | 'derivation' | 'existence' | 'action_enabler';
  entities: string[];         // [Order, Customer, OrderItem]
  conditions: string[];       // [Customer exists, Items available]
  actions: string[];          // [Create order, Update inventory]
}
```

**高優先度ルール:**
- **Order Validation**: 注文には有効な顧客と商品が必要
- **Payment Authorization**: 決済は事前承認が必要
- **Inventory Check**: 在庫確認後の商品予約

**ルール複雑度分析:**
- **Order Validation**: 中複雑度 (2依存関係)
- **Payment Authorization**: 高複雑度 (4依存関係)
- **Inventory Check**: 低複雑度 (1依存関係)

**エンティティ-ルールマッピング:**
- **Order**: 5ルール
- **Payment**: 3ルール
- **User**: 2ルール

#### 6. ユビキタス言語作成（Ubiquitous Language Creation）
チーム共通の専門用語辞書構築：

**コアドメイン用語:**
```text
interface UbiquitousLanguageTerm {
  term: string;           // Order
  definition: string;     // Customer request for products
  context: string;        // Sales
  synonyms: string[];     // [Purchase, Request]
  relatedTerms: string[]; // [OrderItem, Customer]
}
```

**主要用語:**
- **Order**: 顧客の商品購入要求 (コンテキスト: Sales)
- **Customer**: システム利用者としての顧客 (コンテキスト: Sales)
- **Product**: 販売可能な商品 (コンテキスト: Catalog)

**用語関係:**
- **Order** contains **OrderItem**
- **Customer** places **Order**
- **Product** belongs to **Category**

#### 7. ドメインサービス設計（Domain Service Design）
複数エンティティにまたがるサービス設計：

**サービス定義:**
```text
interface DomainService {
  name: string;               // OrderService
  description: string;        // Order processing service
  operations: ServiceOperation[];
  dependencies: string[];     // [PaymentService, InventoryService]
}
```

**サービス操作:**
```text
interface ServiceOperation {
  name: string;           // processOrder
  description: string;    // Process customer order
  inputs: Parameter[];    // [order: Order]
  outputs: Parameter[];   // [result: OrderResult]
  businessRule: string;   // Validate order before processing
}
```

**サービス依存関係分析:**
- **OrderService**: 2依存関係 (中結合)
- **PaymentService**: 1依存関係 (低結合)
- **InventoryService**: 3依存関係 (高結合)

**サービス結合度分析:**
- **OrderService**: 85%結合度 (3責任)
- **PaymentService**: 95%結合度 (1責任)
- **InventoryService**: 70%結合度 (4責任)

#### 8. ドメインモデル検証（Domain Model Validation）
ドメインモデルの整合性と完全性検証：

**検証スコア: 85%**

**検証項目:**
- エンティティ検証: 90%
- 関係検証: 80%
- ビジネスルール検証: 85%

**検証問題:**
- 中重要度: 一部の関係にカーディナリティが不足 (relationships)
- 低重要度: エンティティ命名の統一性 (naming)

**モデル完全性:**
- エンティティ: 90%
- 関係: 80%
- ビジネスルール: 85%
- 境界コンテキスト: 75%

**一貫性チェック:**
- エンティティ名: 合格 (0問題)
- 関係定義: 合格 (1問題)
- ビジネスルール: 合格 (0問題)

## CLI コマンド使用例

### ドメイン分析
```text
# ドメインの包括的分析
ae-framework domain-model --analyze --sources="requirements.md,user-stories.md"

# 出力例:
# ✅ Domain Analysis Complete - 6 entities, 2 bounded contexts identified
# 📊 Analysis:
#   • Core Domain Entities: 4
#   • Bounded Contexts: 2
#   • Business Rules: 12
```

### エンティティ識別
```text
# ドメインエンティティの識別
ae-framework domain-model --entities --sources="domain-requirements.md"

# 出力例:
# ✅ Entity Identification Complete - 8 entities identified
# 📊 Classification:
#   • Aggregate Roots: 3
#   • Value Objects: 2
#   • Domain Services: 3
```

### 集約モデリング
```text
# 集約の設計と境界定義
ae-framework domain-model --aggregates --sources="entities.md"

# 出力例:
# ✅ Aggregate Modeling Complete - 3 aggregates defined
# 📊 Boundary Analysis:
#   • Strong boundaries: 2
#   • Medium boundaries: 1
```

### 境界コンテキスト定義
```text
# 境界コンテキストの設計
ae-framework domain-model --contexts --sources="domain-analysis.md"

# 出力例:
# ✅ Bounded Context Definition Complete - 3 contexts defined
# 📊 Integration Patterns:
#   • Event Sourcing: 2
#   • Command/Query: 1
```

## プロアクティブガイダンス

Domain Modeling Task Adapterは、以下の状況で自動的に介入を提案します：

### 不完全なモデリングの検出
```
⚠️ Warning: Domain model appears incomplete
💡 Recommendations:
  • Create comprehensive entity models
  • Define aggregate boundaries
  • Establish bounded contexts
```

### モデリング不整合の検出
```
💡 Suggestion: Domain model inconsistencies detected
🔧 Actions:
  • Review entity relationships
  • Validate business rule consistency
  • Check ubiquitous language usage
```

### モデル改善の提案
```
💡 Suggestion: Consider refining domain model
🔧 Actions:
  • Update domain model based on new requirements
  • Refine entity definitions
  • Adjust aggregate boundaries if needed
```

## TypeScript インターフェース

### DomainEntity
```text
interface DomainEntity {
  name: string;
  type: 'aggregate' | 'entity' | 'value_object' | 'service' | 'repository';
  description: string;
  attributes: EntityAttribute[];
  methods: EntityMethod[];
  relationships: EntityRelationship[];
  businessRules: string[];
  invariants: string[];
}
```

### BoundedContext
```text
interface BoundedContext {
  name: string;
  description: string;
  entities: string[];
  services: string[];
  responsibilities: string[];
  interfaces: ContextInterface[];
}
```

### BusinessRule
```text
interface BusinessRule {
  id: string;
  name: string;
  description: string;
  type: 'constraint' | 'derivation' | 'existence' | 'action_enabler';
  entities: string[];
  conditions: string[];
  actions: string[];
}
```

## DDDベストプラクティス

### エンティティ設計原則
1. **一意性**: 各エンティティは一意の識別子を持つ
2. **不変条件**: エンティティの不変条件を明確に定義
3. **ライフサイクル**: エンティティの生成から削除まで管理
4. **責任の明確化**: 単一責任原則の遵守

### 集約設計原則
1. **一貫性境界**: トランザクション境界としての集約
2. **小さく保つ**: 集約は可能な限り小さく設計
3. **参照による結合**: 他の集約への参照はIDのみ
4. **結果整合性**: 集約間は結果整合性を許容

### 境界コンテキスト設計原則
1. **チーム境界**: 開発チームの責任範囲と整合
2. **言語境界**: ユビキタス言語の適用範囲
3. **技術境界**: 技術スタックとデータストアの境界
4. **進化境界**: 独立したリリースサイクル

## 次のステップ

Phase 5完了後は、以下のフェーズに進みます：

1. **Phase 6: Test Generation** - ドメインモデルに基づくテスト設計
2. **Phase 7: Code Generation** - ドメインモデルからの実装生成
3. **Phase 8: Implementation** - DDDパターンに基づく実装

## トラブルシューティング

### よくある問題と解決策

**問題: エンティティの境界が不明確**
```text
# より詳細なドメイン分析
ae-framework domain-model --analyze --entities --sources="detailed-requirements.md"
```

**問題: 集約が大きすぎる**
```text
# 集約の再設計
ae-framework domain-model --aggregates --sources="refined-entities.md"
```

**問題: ビジネスルールが複雑**
```text
# ビジネスルールの分析と簡素化
ae-framework domain-model --rules --sources="business-requirements.md"
```

## 設定とカスタマイズ

### ドメインモデリング設定
```text
const domainModelingConfig = {
  maxEntitiesPerAggregate: 7,        // 集約内の最大エンティティ数
  maxBusinessRulesPerEntity: 5,      // エンティティあたりの最大ルール数
  enforceUbiquitousLanguage: true,   // ユビキタス言語の強制
  validateInvariants: true           // 不変条件の検証
};
```

### 複雑度閾値の調整
```text
const complexityThresholds = {
  lowComplexity: 3,      // 低複雑度の上限
  mediumComplexity: 7,   // 中複雑度の上限
  highComplexity: 10     // 高複雑度の上限
};
```
