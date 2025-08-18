# Phase 5: Domain Modeling

## 概要

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

### 主要機能

#### 1. ドメイン分析（Domain Analysis）
ビジネスドメインの包括的分析：

**分析結果例:**
```typescript
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
```typescript
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
```typescript
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
```typescript
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
```typescript
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
```typescript
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
```typescript
interface DomainService {
  name: string;               // OrderService
  description: string;        // Order processing service
  operations: ServiceOperation[];
  dependencies: string[];     // [PaymentService, InventoryService]
}
```

**サービス操作:**
```typescript
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
```bash
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
```bash
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
```bash
# 集約の設計と境界定義
ae-framework domain-model --aggregates --sources="entities.md"

# 出力例:
# ✅ Aggregate Modeling Complete - 3 aggregates defined
# 📊 Boundary Analysis:
#   • Strong boundaries: 2
#   • Medium boundaries: 1
```

### 境界コンテキスト定義
```bash
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
```typescript
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
```typescript
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
```typescript
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
```bash
# より詳細なドメイン分析
ae-framework domain-model --analyze --entities --sources="detailed-requirements.md"
```

**問題: 集約が大きすぎる**
```bash
# 集約の再設計
ae-framework domain-model --aggregates --sources="refined-entities.md"
```

**問題: ビジネスルールが複雑**
```bash
# ビジネスルールの分析と簡素化
ae-framework domain-model --rules --sources="business-requirements.md"
```

## 設定とカスタマイズ

### ドメインモデリング設定
```typescript
const domainModelingConfig = {
  maxEntitiesPerAggregate: 7,        // 集約内の最大エンティティ数
  maxBusinessRulesPerEntity: 5,      // エンティティあたりの最大ルール数
  enforceUbiquitousLanguage: true,   // ユビキタス言語の強制
  validateInvariants: true           // 不変条件の検証
};
```

### 複雑度閾値の調整
```typescript
const complexityThresholds = {
  lowComplexity: 3,      // 低複雑度の上限
  mediumComplexity: 7,   // 中複雑度の上限
  highComplexity: 10     // 高複雑度の上限
};
```