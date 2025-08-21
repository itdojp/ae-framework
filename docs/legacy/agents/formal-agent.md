# Formal Agent - Phase 2 of ae-framework

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

The Formal Agent is a critical component of the ae-framework that bridges Phase 1 (Intent) and Phase 3 (Tests) by converting requirements into formal, verifiable specifications. It provides comprehensive capabilities for generating, validating, and model-checking formal specifications across multiple notations and formats.

## Overview

The Formal Agent transforms natural language requirements into mathematically precise specifications that can be validated, verified, and used to generate tests. It supports multiple formal specification languages and provides integrated validation and model checking capabilities.

### Key Capabilities

- **Formal Specification Generation**: TLA+, Alloy, Z notation
- **API Specification Creation**: OpenAPI, AsyncAPI, GraphQL schemas
- **State Machine Generation**: FSM definitions with invariants
- **Contract Specification**: Design by Contract (preconditions, postconditions, invariants)
- **Property-based Specifications**: For property-based testing
- **Formal Verification**: Model checking and property verification
- **Specification Validation**: Consistency and correctness checking
- **Diagram Generation**: UML, sequence, state, class, and component diagrams

## Architecture

The Formal Agent consists of two main components:

1. **Core Agent** (`src/agents/formal-agent.ts`): The main business logic
2. **MCP Server Wrapper** (`src/mcp-server/formal-server.ts`): Model Context Protocol server for tool integration

## Installation and Setup

### Prerequisites

- Node.js 18+
- TypeScript 5.5+
- Optional: TLA+ tools for advanced model checking
- Optional: Alloy Analyzer for Alloy specifications

### Dependencies

The Formal Agent requires the following key dependencies:

```json
{
  "dependencies": {
    "zod": "^3.23.8",
    "@modelcontextprotocol/sdk": "^1.0.0"
  }
}
```

### Running the Formal Agent

```bash
# Start the MCP server
npm run formal-agent

# Development mode with hot reload
npm run formal-agent:dev

# Quick specification generation
npm run formal-spec

# Validate existing specifications
npm run validate-specs

# Generate TLA+ specifications
npm run generate-tla

# Run model checking
npm run model-check
```

## Usage

### Core Agent API

The `FormalAgent` class provides the main functionality:

```typescript
import { FormalAgent } from './src/agents/formal-agent.js';

// Initialize with configuration
const agent = new FormalAgent({
  outputFormat: 'tla+',
  validationLevel: 'comprehensive',
  generateDiagrams: true,
  enableModelChecking: true
});

// Generate formal specification
const spec = await agent.generateFormalSpecification(
  'A reservation system that manages inventory...',
  'tla+',
  { includeDiagrams: true, generateProperties: true }
);

// Create API specification
const apiSpec = await agent.createAPISpecification(
  'REST API for inventory management...',
  'openapi',
  { includeExamples: true, generateContracts: true }
);

// Generate state machine
const stateMachine = await agent.generateStateMachine(
  'Order processing workflow...',
  { generateInvariants: true, includeDiagrams: true }
);
```

### MCP Tools

The Formal Agent provides the following MCP tools:

#### `generate_formal_spec`
Generate formal specifications from requirements.

**Parameters:**
- `requirements` (string): The requirements to convert
- `type` (enum): 'tla+' | 'alloy' | 'z-notation'
- `options` (object): Generation options

**Example:**
```json
{
  "requirements": "A concurrent inventory system with atomic reservations",
  "type": "tla+",
  "options": {
    "includeDiagrams": true,
    "generateProperties": true
  }
}
```

#### `create_api_spec`
Create API specifications from requirements.

**Parameters:**
- `requirements` (string): The requirements to convert
- `format` (enum): 'openapi' | 'asyncapi' | 'graphql'
- `options` (object): Generation options

#### `generate_state_machine`
Generate state machine definitions.

**Parameters:**
- `requirements` (string): The requirements to convert
- `options` (object): Generation options

#### `create_contracts`
Generate Design by Contract specifications.

**Parameters:**
- `functionSignature` (string): Function signature
- `requirements` (string): Behavior requirements
- `options` (object): Contract options

#### `validate_spec`
Validate specification consistency and correctness.

**Parameters:**
- `specificationId` (string): ID of specification to validate
- `validationLevel` (enum): 'basic' | 'comprehensive' | 'formal-verification'

#### `model_check`
Run formal model checking on specifications.

**Parameters:**
- `specificationId` (string): ID of specification to check
- `properties` (array): Properties to verify
- `options` (object): Model checking options

#### `generate_diagrams`
Generate UML/sequence diagrams from specifications.

**Parameters:**
- `specificationId` (string): ID of specification
- `types` (array): Diagram types to generate

## Formal Specification Languages

### TLA+ (Temporal Logic of Actions)

TLA+ is used for specifying and verifying concurrent and distributed systems.

**Example Output:**
```tla
----------------------------- MODULE Inventory -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxStock, MaxOrders

VARIABLES stock, reserved, orders

Init == 
    /\ stock = MaxStock 
    /\ reserved = [o \in {} |-> 0]
    /\ orders = {}

Reserve(orderId, quantity) ==
    /\ orderId \notin orders
    /\ quantity > 0
    /\ stock >= quantity
    /\ stock' = stock - quantity
    /\ reserved' = reserved @@ (orderId :> quantity)
    /\ orders' = orders \cup {orderId}

SafetyInvariant == stock >= 0
LivenessProperty == <>[](\A o \in orders: reserved[o] > 0)

============================================================================
```

### Alloy

Alloy is used for structural modeling and constraint solving.

**Example Output:**
```alloy
sig Order {
    id: String,
    items: set Item,
    status: Status
}

sig Item {
    id: String,
    quantity: Int
} {
    quantity > 0
}

abstract sig Status {}
one sig Pending, Confirmed, Cancelled extends Status {}

fact OrderConstraints {
    all o: Order | some o.items
    all o: Order | o.status in Status
}

pred ValidReservation[o: Order] {
    o.status = Confirmed implies all i: o.items | i.quantity > 0
}
```

### Z Notation

Z notation provides mathematical precision for specification.

**Example Output:**
```z
[ORDER, ITEM]

Stock == ℕ
Quantity == ℕ₁

┌─ InventoryState ─────────────────────────────────
│ stock: ITEM → Stock
│ reserved: ORDER → (ITEM → Quantity)
├─────────────────────────────────────────────────
│ dom stock = dom reserved
└─────────────────────────────────────────────────

┌─ Reserve ──────────────────────────────────────
│ ΔInventoryState
│ order?: ORDER
│ item?: ITEM
│ quantity?: Quantity
├───────────────────────────────────────────────
│ order? ∉ dom reserved
│ item? ∈ dom stock
│ stock(item?) ≥ quantity?
│ stock' = stock ⊕ {item? ↦ (stock(item?) - quantity?)}
│ reserved' = reserved ⊕ {order? ↦ {item? ↦ quantity?}}
└───────────────────────────────────────────────
```

## API Specifications

### OpenAPI 3.0

The agent generates comprehensive OpenAPI specifications with:

- Complete endpoint definitions
- Request/response schemas
- Parameter validation
- Contract annotations
- Example data

**Example Output:**
```yaml
openapi: 3.0.3
info:
  title: Inventory Management API
  version: 1.0.0
  description: Formal specification for inventory operations

paths:
  /reservations:
    post:
      operationId: createReservation
      summary: Create inventory reservation
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/ReservationRequest'
      responses:
        '201':
          description: Reservation created successfully
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Reservation'
        '409':
          description: Insufficient inventory
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'

components:
  schemas:
    ReservationRequest:
      type: object
      required: [orderId, itemId, quantity]
      properties:
        orderId:
          type: string
          pattern: '^[A-Za-z0-9_-]+$'
        itemId:
          type: string
          pattern: '^[A-Za-z0-9_-]+$'
        quantity:
          type: integer
          minimum: 1
          maximum: 1000
```

### AsyncAPI 2.6

For event-driven architectures:

```yaml
asyncapi: 2.6.0
info:
  title: Inventory Events API
  version: 1.0.0

channels:
  inventory/reserved:
    description: Inventory reservation events
    subscribe:
      message:
        $ref: '#/components/messages/ReservationEvent'

components:
  messages:
    ReservationEvent:
      payload:
        type: object
        properties:
          orderId: { type: string }
          itemId: { type: string }
          quantity: { type: integer }
          timestamp: { type: string, format: date-time }
```

### GraphQL Schema

For graph-based APIs:

```graphql
type Query {
  inventory(itemId: ID!): InventoryItem
  reservation(orderId: ID!): Reservation
}

type Mutation {
  createReservation(input: ReservationInput!): ReservationResult!
  cancelReservation(orderId: ID!): CancellationResult!
}

type InventoryItem {
  id: ID!
  name: String!
  stock: Int!
  reserved: Int!
  available: Int!
}

input ReservationInput {
  orderId: ID!
  itemId: ID!
  quantity: Int! @constraint(min: 1, max: 1000)
}

type ReservationResult {
  success: Boolean!
  reservation: Reservation
  errors: [ValidationError!]
}
```

## State Machine Generation

The agent generates formal state machine definitions with:

- States and transitions
- Guards and actions
- Invariant properties
- Visual diagrams

**Example:**
```typescript
{
  "name": "OrderProcessing",
  "states": [
    {
      "name": "Created",
      "type": "initial",
      "properties": { "timestamp": "Date" },
      "invariants": ["order.items.length > 0"]
    },
    {
      "name": "Reserved",
      "type": "intermediate", 
      "properties": { "reservationId": "string" },
      "invariants": ["reservation.isValid()"]
    },
    {
      "name": "Confirmed",
      "type": "final",
      "properties": { "confirmedAt": "Date" },
      "invariants": ["payment.isCompleted()"]
    }
  ],
  "transitions": [
    {
      "from": "Created",
      "to": "Reserved",
      "event": "reserve",
      "guard": "hasAvailableInventory()",
      "action": "createReservation()"
    }
  ],
  "invariants": [
    "order.status matches current state",
    "all reservations have positive quantity"
  ]
}
```

## Design by Contract

The agent generates comprehensive contract specifications:

### Preconditions
```typescript
// Before method execution
{
  type: "precondition",
  expression: "orderId != null && quantity > 0 && inventory.has(itemId)",
  description: "Valid order with positive quantity for existing item"
}
```

### Postconditions
```typescript
// After method execution
{
  type: "postcondition", 
  expression: "result.success implies (old(inventory.stock) - inventory.stock == quantity)",
  description: "Successful reservation reduces stock by requested quantity"
}
```

### Invariants
```typescript
// Always true
{
  type: "invariant",
  expression: "inventory.stock >= 0 && totalReserved() <= initialStock",
  description: "Stock never goes negative and reservations don't exceed initial stock"
}
```

## Validation and Model Checking

### Specification Validation

The agent performs multi-level validation:

1. **Basic**: Syntax and structure checking
2. **Comprehensive**: Semantic analysis and consistency checking  
3. **Formal Verification**: Mathematical property verification

**Validation Output:**
```typescript
{
  "status": "valid",
  "errors": [],
  "warnings": [
    {
      "type": "completeness_warning",
      "message": "Consider adding liveness properties",
      "suggestion": "Add properties ensuring progress"
    }
  ]
}
```

### Model Checking

Formal verification of specifications:

```typescript
{
  "specification": "spec_123",
  "properties": [
    {
      "name": "SafetyInvariant",
      "satisfied": true,
      "description": "Stock never goes negative"
    },
    {
      "name": "DeadlockFreedom", 
      "satisfied": false,
      "description": "System is deadlock-free",
      "counterExample": {
        "trace": [
          { "state": { "stock": 0, "pending": 5 }, "action": "reserve", "timestamp": 1000 },
          { "state": { "stock": 0, "pending": 10 }, "action": "reserve", "timestamp": 1001 }
        ],
        "description": "Deadlock when stock exhausted with pending reservations"
      }
    }
  ],
  "counterExamples": [...],
  "statistics": {
    "statesExplored": 1507,
    "timeElapsed": 2350,
    "memoryUsed": 45000
  }
}
```

## Diagram Generation

The agent generates multiple diagram types:

### Sequence Diagrams (PlantUML)
```
@startuml
title Inventory Reservation Sequence

actor Client
participant API
participant InventoryService  
participant Database

Client -> API: POST /reservations
API -> InventoryService: reserve(orderId, itemId, quantity)
InventoryService -> Database: checkAvailability(itemId)
Database -> InventoryService: currentStock
alt sufficient stock
    InventoryService -> Database: createReservation(reservation)
    Database -> InventoryService: reservationId
    InventoryService -> API: ReservationResult(success=true)
    API -> Client: 201 Created
else insufficient stock
    InventoryService -> API: ReservationResult(success=false)
    API -> Client: 409 Conflict
end
@enduml
```

### State Diagrams
```
@startuml
title Order State Machine

[*] -> Created
Created -> Reserved : reserve / checkInventory()
Reserved -> Confirmed : confirm / processPayment() 
Reserved -> Cancelled : cancel / releaseReservation()
Confirmed -> Shipped : ship / updateInventory()
Cancelled -> [*]
Shipped -> [*]

note right of Reserved : Invariant: reservation.quantity > 0
note right of Confirmed : Invariant: payment.isValid()
@enduml
```

## Configuration

The Formal Agent supports comprehensive configuration:

```typescript
const config: FormalAgentConfig = {
  outputFormat: 'tla+',           // Default specification format
  validationLevel: 'comprehensive', // Validation thoroughness
  generateDiagrams: true,         // Auto-generate diagrams
  enableModelChecking: true      // Enable formal verification
};
```

### Configuration Options

- **outputFormat**: Default format for specifications
- **validationLevel**: Depth of validation checking
- **generateDiagrams**: Automatic diagram generation
- **enableModelChecking**: Formal verification capabilities

## Integration with ae-framework Phases

### Phase 1 Integration (Intent)
- Consumes natural language requirements
- Processes user stories and acceptance criteria
- Transforms informal specifications to formal ones

### Phase 3 Integration (Tests)
- Provides formal specifications for test generation
- Supplies contracts for property-based testing
- Offers state machines for model-based testing
- Generates API specifications for contract testing

## Best Practices

### Writing Requirements for Formal Specification

1. **Be Precise**: Use specific quantities, constraints, and conditions
2. **Include Edge Cases**: Specify boundary conditions and error scenarios
3. **Define Invariants**: State what should always be true
4. **Specify Temporal Properties**: What should eventually happen

### Example Good Requirements

```
Inventory Reservation System Requirements:

1. The system maintains a non-negative stock count for each item
2. Reservations can only be created for items with sufficient available stock
3. A reservation reduces available stock by the reserved quantity
4. Cancelled reservations restore the reserved quantity to available stock
5. The sum of all reservations for an item never exceeds initial stock
6. All reservation operations are atomic and isolated
7. The system must handle concurrent reservations without double-booking
```

### Validation Strategy

1. **Start with Basic**: Ensure syntax correctness
2. **Progress to Comprehensive**: Check semantic consistency  
3. **End with Formal**: Verify mathematical properties
4. **Iterate**: Refine based on validation feedback

### Model Checking Guidelines

1. **Property Selection**: Focus on safety and liveness properties
2. **Scope Management**: Balance thoroughness with performance
3. **Counter-example Analysis**: Use failures to improve specifications
4. **Incremental Verification**: Build complexity gradually

## Error Handling

The Formal Agent provides comprehensive error reporting:

### Specification Errors
```typescript
{
  "type": "syntax_error",
  "message": "TLA+ specification must include MODULE declaration",
  "location": { "line": 1, "column": 1 },
  "severity": "error"
}
```

### Validation Warnings
```typescript
{
  "type": "completeness_warning", 
  "message": "Consider adding temporal properties",
  "suggestion": "Add liveness properties to ensure progress"
}
```

### Model Checking Errors
```typescript
{
  "type": "property_violation",
  "message": "Safety property violated",
  "counterExample": {
    "trace": [...],
    "description": "Execution path leading to property violation"
  }
}
```

## Performance Considerations

### Specification Generation
- TLA+ generation: ~100-500ms per specification
- Alloy generation: ~50-200ms per specification
- Z notation generation: ~200-800ms per specification

### Model Checking
- State space exploration: Exponential with system complexity
- Property verification: Linear with number of properties
- Memory usage: ~1MB per 1000 states explored

### Optimization Tips
1. **Limit Scope**: Use bounded model checking
2. **Property Focus**: Verify critical properties first
3. **Incremental**: Build specifications incrementally
4. **Caching**: Reuse validation results when possible

## Troubleshooting

### Common Issues

**Issue: TLA+ specification generation fails**
- Solution: Ensure requirements include state variables and actions
- Check: Module name conflicts with reserved words

**Issue: Model checking times out**
- Solution: Reduce scope or increase timeout limits
- Check: State space complexity and property count

**Issue: API specification incomplete**
- Solution: Provide more detailed endpoint descriptions
- Check: Include request/response examples

### Debug Mode

Enable detailed logging:
```bash
DEBUG=formal-agent npm run formal-agent
```

## Contributing

Contributions to the Formal Agent are welcome! Please see the main project's CONTRIBUTING.md for guidelines.

### Areas for Enhancement

1. **Additional Formal Languages**: Coq, Isabelle/HOL, Event-B
2. **Advanced Model Checking**: Integration with TLC, Alloy Analyzer
3. **Diagram Enhancements**: Interactive diagrams, animation
4. **Performance Optimization**: Parallel processing, caching
5. **Integration**: Direct IDE support, CI/CD integration

## License

The Formal Agent is part of the ae-framework and follows the same license terms.

---

The Formal Agent represents a significant step forward in bridging the gap between informal requirements and formal, testable specifications, enabling higher confidence in system correctness and reliability.

---

## Japanese

**フォーマル・エージェント - ae-frameworkのフェーズ2**

フォーマル・エージェントは、フェーズ1（Intent）とフェーズ3（Tests）の橋渡しを行うae-frameworkの重要なコンポーネントで、要件を正式で検証可能な仕様に変換します。複数の記法とフォーマットにわたって、正式仕様の生成、検証、モデルチェックのための包括的な機能を提供します。

## 概要

フォーマル・エージェントは、自然言語の要件を数学的に正確な仕様に変換し、検証、確認、テスト生成に使用できるようにします。複数の正式仕様言語をサポートし、統合された検証とモデルチェック機能を提供します。

### 主要機能

- **正式仕様生成**: TLA+、Alloy、Z記法
- **API仕様作成**: OpenAPI、AsyncAPI、GraphQLスキーマ
- **状態機械生成**: 不変条件付きFSM定義
- **契約仕様**: Design by Contract（事前条件、事後条件、不変条件）
- **プロパティベース仕様**: プロパティベーステスト用
- **正式検証**: モデルチェックとプロパティ検証
- **仕様検証**: 一貫性と正確性のチェック
- **図表生成**: UML、シーケンス、状態、クラス、コンポーネント図

## アーキテクチャ

フォーマル・エージェントは2つの主要コンポーネントで構成されます：

1. **コアエージェント** (`src/agents/formal-agent.ts`): メインビジネスロジック
2. **MCPサーバーラッパー** (`src/mcp-server/formal-server.ts`): ツール統合用Model Context Protocolサーバー

## 使用方法

### フォーマル・エージェントの実行

#### MCPサーバーとして
```bash
npm run formal-agent
```

#### 直接統合
```typescript
import { FormalAgent, FormalSpecificationRequest } from './src/agents/formal-agent.js';

const agent = new FormalAgent();

const request: FormalSpecificationRequest = {
  requirements: [
    {
      id: 'REQ-001',
      description: 'ユーザーは認証後にシステムにアクセスできる',
      type: 'functional'
    }
  ],
  specificationTypes: ['tla+', 'openapi', 'state-machine'],
  validationOptions: {
    enableModelChecking: true,
    maxStates: 10000
  }
};

const result = await agent.generateFormalSpecifications(request);
```

## 対応する正式言語

### TLA+
- 並行システムと分散システムの仕様
- 安全性と活性プロパティの検証
- 状態空間探索とモデルチェック

### Alloy
- 構造的な制約の表現
- リレーショナルロジックベースの仕様
- 軽量な正式手法アプローチ

### Z記法
- 数学的ベースの仕様言語
- 複雑なデータ構造とオペレーション
- 厳密な型システム

## 生成される成果物

### TLA+仕様
```tla
EXTENDS Naturals, Sequences

VARIABLES users, sessions, permissions

UserLogin(user) ==
  /\ user \notin sessions
  /\ IsValidCredentials(user)
  /\ sessions' = sessions \cup {user}
  /\ UNCHANGED <<users, permissions>>

Safety == \A user \in sessions : IsAuthenticated(user)
```

### OpenAPI仕様
```yaml
openapi: 3.0.0
info:
  title: ユーザー管理API
  version: 1.0.0
paths:
  /login:
    post:
      summary: ユーザーログイン
      requestBody:
        content:
          application/json:
            schema:
              type: object
              properties:
                username:
                  type: string
                password:
                  type: string
```

### 状態機械定義
```typescript
interface AuthenticationStateMachine {
  states: ['未認証', '認証中', '認証済み', 'エラー'];
  transitions: [
    { from: '未認証', to: '認証中', event: 'login_attempt' },
    { from: '認証中', to: '認証済み', event: 'auth_success' },
    { from: '認証中', to: 'エラー', event: 'auth_failure' }
  ];
  invariants: ['認証済みユーザーは有効な権限を持つ'];
}
```

## 検証機能

### プロパティ検証
```typescript
// 安全性プロパティ
const safetyProperty = {
  name: 'データ整合性',
  description: '未認証ユーザーは保護されたリソースにアクセスできない',
  formal: '[] (unauthenticated => ~access_protected_resource)'
};

// 活性プロパティ
const livenessProperty = {
  name: 'ログイン完了',
  description: '有効な認証情報での最終的なログイン成功',
  formal: '<> (valid_credentials => authenticated)'
};
```

### モデルチェック結果
```typescript
interface ModelCheckResult {
  property: string;
  satisfied: boolean;
  counterexample?: {
    states: StateSequence;
    actions: ActionSequence;
    description: string;
  };
}
```

## パフォーマンス考慮事項

### 仕様生成
- TLA+生成: 仕様あたり約100-500ms
- Alloy生成: 仕様あたり約50-200ms
- Z記法生成: 仕様あたり約200-800ms

### モデルチェック
- 状態空間探索: システム複雑性に対して指数的
- プロパティ検証: プロパティ数に対して線形
- メモリ使用量: 探索状態1000個あたり約1MB

### 最適化のヒント
1. **スコープ制限**: 有界モデルチェックを使用
2. **プロパティ重視**: 重要なプロパティを優先検証
3. **段階的構築**: 仕様を段階的に構築
4. **キャッシュ活用**: 可能な場合は検証結果を再利用

## トラブルシューティング

### よくある問題

**問題: TLA+仕様生成が失敗する**
- 解決策: 要件に状態変数とアクションが含まれていることを確認
- チェック: モジュール名が予約語と競合していないか

**問題: モデルチェックがタイムアウトする**
- 解決策: スコープを削減するかタイムアウト制限を増加
- チェック: 状態空間の複雑性とプロパティ数

**問題: API仕様が不完全**
- 解決策: より詳細なエンドポイント記述を提供
- チェック: リクエスト/レスポンス例を含める

### デバッグモード

詳細ログを有効化：
```bash
DEBUG=formal-agent npm run formal-agent
```

## 拡張の領域

1. **追加の正式言語**: Coq、Isabelle/HOL、Event-B
2. **高度なモデルチェック**: TLC、Alloy Analyzerとの統合
3. **図表拡張**: インタラクティブ図表、アニメーション
4. **パフォーマンス最適化**: 並列処理、キャッシュ
5. **統合**: 直接IDE支援、CI/CD統合

フォーマル・エージェントは、非形式的な要件と形式的でテスト可能な仕様の間のギャップを埋める重要な一歩を表し、システムの正確性と信頼性への高い信頼を可能にします。