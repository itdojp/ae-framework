---
docRole: derived
canonicalSource:
  - README.md
  - docs/agents/commands.md
  - docs/agents/hook-feedback.md
lastVerified: '2026-03-10'
---

# Claude Code統合ガイド - AE Framework完全連携

> 🌍 Language / 言語: 日本語 | English

---

> **AE Framework ↔ Claude Code** の包括的統合ドキュメント  
> 自然言語指示から高品質コード生成まで一貫したワークフローを実現

## 📋 目次

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

---

## English

### 1. Overview
This guide describes the current AE Framework x Claude Code integration model. The repository treats Claude Code Task Tool execution as the primary path, while CLI and MCP remain fallback surfaces for cases where Task Tool is unavailable or when operators want a direct/manual execution path.

Highlights
- intent analysis -> natural language requirements -> stories -> validation -> domain modeling -> UI generation
- six-phase collaboration with explicit checkpoints between phases
- Task Tool as the preferred runtime path, with CLI/MCP fallback for recovery and manual control
- UI generation optimized for WCAG 2.1 AA, TypeScript strictness, and automated test scaffolding

### 2. Core operating model
#### 2.1 Hybrid integration
The current architecture is a hybrid intent system. A request is first evaluated for Claude Code context and Task Tool availability. When both are present, AE Framework routes the request through the Task Tool handler. If not, it falls back to CLI commands or MCP integration.

Operational priority:
1. Claude Code Task Tool
2. CLI commands
3. MCP Server fallback

This priority matters because the user experience, blocking semantics, and proactive guidance are designed around the Task Tool path first. CLI and MCP exist to preserve recoverability and manual operability.

#### 2.2 Task Tool contract
The repository documents the Task Tool exchange in terms of `TaskRequest` and `TaskResponse`. The interface excerpt in the Japanese section below follows the same shared contract, including the optional `context` field. In practice, the request carries:
- task description
- prompt content
- phase or subagent type
- optional execution context

The response is expected to include:
- concise summary
- detailed analysis in Markdown
- recommendations
- next actions
- warnings
- an explicit blocking signal when progress should stop

This shape is important because Claude Code needs both a machine-actionable decision surface and a human-readable explanation surface.

#### 2.3 Proactive guidance
The integration is not limited to passive command execution. The design assumes proactive guidance using recent file changes, recent actions, and inferred user intent. The guidance path can return warnings, suggestions, or blocking interventions. Use this when AE Framework detects a quality, sequencing, or modeling problem that should be surfaced before the next phase continues.

### 3. Phase map and recommended operator flow
#### 3.1 Six phases
| Phase | Primary purpose | Typical output | Typical duration |
| --- | --- | --- | --- |
| 1. Intent Analysis | classify user intent and identify requirement themes | initial requirement inventory | ~10-20s |
| 2. Natural Language Requirements | structure functional / non-functional / business requirements | structured requirement set | ~15-30s |
| 3. User Stories | organize work into stories and epics | stories, epics, point estimates | ~20-45s |
| 4. Validation | check consistency, gaps, and quality concerns | validation findings and recommendations | ~25-60s |
| 5. Domain Modeling | derive bounded contexts, entities, services, and events | domain model package | ~30-90s |
| 6. UI Generation | generate implementation-facing UI assets | React/Next.js UI set and quality metrics | usually <30s |

#### 3.2 Recommended interaction pattern
The Japanese examples later in this document show a full conversational walk-through. The current recommended English-side interpretation is:
- run Phases 1-2 to converge on requirement meaning
- run Phases 3-4 to confirm delivery scope and quality findings
- run Phase 5 when DDD boundaries, services, and events must be fixed
- run Phase 6 when the model is stable enough to generate UI artifacts

Recommended execution styles:
- small project: run the full six-phase flow end to end
- medium project: pause after validation and domain modeling for explicit review
- large project: split work by bounded context or major capability area

### 4. Current architecture detail
#### 4.1 Hybrid system responsibilities
The Japanese section below contains the full pseudo-code, but the operational reading is straightforward:
- Claude Code path is selected when the runtime knows it is inside Claude Code and Task Tool is available
- fallback path is selected for direct CLI execution, MCP integration, or recovery scenarios
- strictness and real-time handling are explicit configuration surfaces, not implicit side effects

#### 4.2 Adapter layout
The guide models one handler per phase:
- Intent Task Adapter
- Natural Language handler
- User Stories handler
- Validation handler
- Domain Modeling handler
- UI Generation handler

This keeps the integration boundary narrow. Claude Code calls an adapter oriented to the active phase rather than a monolithic black-box command. Intent Analysis is not special-cased out of the adapter layout; it is the first adapter in the flow.

### 5. Performance, scale, and expectations
#### 5.1 Expected runtime envelope
The current Japanese section documents representative timings. These runtime figures are illustrative examples unless they are explicitly tied to generated artifacts or measured CI evidence. Treat them as planning guidance rather than guaranteed SLO values. The operational expectation is roughly:
- end-to-end flow in about 4 minutes for a medium-sized example
- Phase 6 is intentionally much faster than the earlier analytical phases
- memory demand grows with requirement volume and generated output count

#### 5.2 Scaling guidance
Use these heuristics:
- fewer than 20 requirements: end-to-end flow is usually acceptable
- 20-100 requirements: prefer staged confirmation between phases
- more than 100 requirements: split by bounded context or major capability area

### 6. Troubleshooting guidance
Common failure categories in the current design are:
- Task Tool unavailable or misconfigured
- execution timeout caused by oversized batches
- UI generation quality below expected thresholds
- Node.js memory exhaustion on large projects

Pragmatic remediation order:
1. confirm Claude Code / Task Tool availability
2. reduce batch size or split the request
3. tighten quality configuration when UI output quality is insufficient
4. raise Node.js memory limits or split execution by bounded context
5. use diagnostic commands and debug logging before retrying broad flows

### 7. References and reading order
Use this reading order when you are operating in English first:
1. this English section for the operating model
2. the detailed Japanese sections below for full pseudo-code, examples, and troubleshooting payloads
3. repository architecture and phase references when implementation details are required

Commands, workflow entry points, and artifact semantics are shared across both languages. The main difference is the amount of explanatory detail. This section narrows that gap by documenting the current operational model in English.

## アーキテクチャ詳細

### 🏗️ ハイブリッド統合システム

```text
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

```text
// Claude Code → AE Framework
interface TaskRequest {
  description: string;      // タスクの説明
  prompt: string;          // 処理対象のプロンプト  
  subagent_type: string;   // フェーズ指定
  context?: {
    validationTaskType?: string;
    strict?: boolean;
    sources?: string | string[];
    [key: string]: unknown;
  };
}

// AE Framework → Claude Code
interface TaskResponse {
  summary: string;           // 実行結果サマリー
  analysis: string;          // 詳細分析（Markdown形式）
  recommendations: string[]; // 推奨事項
  nextActions: string[];     // 次のアクション
  warnings: string[];        // 警告事項
  shouldBlockProgress: boolean; // 進行ブロック判定
  blockingReason?: string;   // 機械可読のブロッカー理由
  requiredHumanInput?: string; // 再開に必要な最小人手入力
}
```

### 🎯 Task Adapterアーキテクチャ

```text
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

### 🔄 プロアクティブガイダンス

```text
interface ProactiveGuidanceContext {
  recentFiles: string[];     // 最近変更されたファイル
  recentActions: string[];   // 最近の行動
  userIntent: string;        // ユーザーの意図
}

interface ProactiveGuidanceResult {
  shouldIntervene: boolean;
  intervention: {
    type: 'warning' | 'suggestion' | 'block';
    message: string;
    recommendedActions: string[];
  };
}
```

---

## フェーズ別連携

### Phase 1: Intent Analysis 🎯

**Task Adapter**: Intent Task Adapter  
**主要機能**: ユーザー意図の分析と要件抽出

```text
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
  nextActions: ["Phase 2: Natural Language Requirements"],
  warnings: ["非機能要件の詳細化が必要"],
  shouldBlockProgress: false
};
```

### Phase 2: Natural Language Requirements 📝

**Task Adapter**: Natural Language Task Adapter  
**主要機能**: 自然言語要件の構造化と分析

```text
// 呼び出し例
const request: TaskRequest = {
  description: "自然言語要件の構造化",
  prompt: "商品登録、在庫管理、価格変更機能が必要...",
  subagent_type: "natural-language"
};

// 応答例 (処理時間: 10-30秒)
const response: TaskResponse = {
  summary: "15件の要件を機能・非機能・ビジネス要件に分類",
  analysis: `
## 要件分析結果

### 機能要件 (10件)
1. **商品登録機能**
   - 商品名、説明、価格、カテゴリの入力
   - 画像アップロード（複数枚対応）
   - SKU自動生成機能

2. **在庫管理機能**
   - リアルタイム在庫数表示
   - 在庫アラート設定
   - 入荷・出荷履歴管理

### 非機能要件 (3件)
1. **パフォーマンス要件**
   - ページ読み込み時間: 2秒以内
   - 同時アクセス: 100ユーザー対応

2. **セキュリティ要件**
   - 認証・認可機能
   - SQLインジェクション対策

### ビジネス要件 (2件)
1. **運用要件**
   - 24時間365日稼働
   - バックアップ・復旧体制
`,
  recommendations: [
    "ユーザーストーリー作成でアジャイル開発に対応",
    "非機能要件の具体的数値目標設定"
  ],
  nextActions: ["Phase 3: User Stories Creation"],
  warnings: ["セキュリティ要件の詳細化推奨"],
  shouldBlockProgress: false
};
```

### Phase 3: User Stories Creation 📋

**Task Adapter**: User Stories Task Adapter  
**主要機能**: アジャイル開発用ユーザーストーリー生成

```text
// 呼び出し例
const request: TaskRequest = {
  description: "ユーザーストーリーの自動生成",
  prompt: "Phase 2で構造化された要件からユーザーストーリーを作成",
  subagent_type: "user-stories"
};

// 応答例 (処理時間: 15-45秒)
const response: TaskResponse = {
  summary: "8個のユーザーストーリーを3つのエピックに整理 (合計34ポイント)",
  analysis: `
## ユーザーストーリー生成結果

### Epic 1: 商品管理 (13ポイント)

#### Story 1.1: 商品登録 (5ポイント)
**As a** 店舗管理者  
**I want to** 新しい商品を登録する  
**So that** 顧客に商品を販売できる

**受け入れ条件:**
- [ ] 商品名、価格、説明を入力できる
- [ ] 商品画像を最大5枚アップロードできる
- [ ] カテゴリを選択できる
- [ ] SKUが自動生成される

#### Story 1.2: 在庫管理 (8ポイント)
**As a** 在庫管理者  
**I want to** 商品の在庫数を管理する  
**So that** 適切な在庫レベルを維持できる

**受け入れ条件:**
- [ ] 現在の在庫数を確認できる
- [ ] 在庫の入荷・出荷を記録できる
- [ ] 在庫アラートを設定できる

### Epic 2: ユーザー管理 (13ポイント)
[詳細省略...]

### Epic 3: レポート機能 (8ポイント)
[詳細省略...]
`,
  recommendations: [
    "受け入れ条件の詳細化を推奨",
    "ストーリーポイント見積もりの妥当性確認"
  ],
  nextActions: ["Phase 4: Validation"],
  warnings: [],
  shouldBlockProgress: false
};
```

### Phase 4: Validation 🔍

**Task Adapter**: Validation Task Adapter  
**主要機能**: 要件・ストーリー・仕様の品質検証

```text
// 呼び出し例
const request: TaskRequest = {
  description: "要件とストーリーの整合性検証",
  prompt: "Phase 2-3の成果物の整合性とトレーサビリティを検証",
  subagent_type: "validation"
};

// 応答例 (処理時間: 20-60秒)
const response: TaskResponse = {
  summary: "90%の整合性を達成、3件の改善推奨事項を特定",
  analysis: `
## 品質検証結果

### 整合性分析
- **要件-ストーリー整合性**: 95% (15/15件の要件がストーリーでカバー)
- **トレーサビリティ**: 88% (優良レベル)
- **完全性**: 85% (良好レベル)

### 検証項目詳細

#### ✅ 合格項目
1. **機能要件カバレッジ**: 100%
   - 全機能要件がユーザーストーリーに反映済み
   
2. **受け入れ条件品質**: 92%
   - SMART基準に準拠した受け入れ条件

3. **ストーリー独立性**: 95%
   - 依存関係が明確で実装順序が最適化

#### ⚠️ 改善推奨項目
1. **非機能要件の具体化** (重要度: 高)
   - パフォーマンス要件の数値目標明確化
   - セキュリティ要件の具体的実装方針

2. **ストーリー粒度の調整** (重要度: 中)
   - Story 1.2の8ポイントを3-5ポイントに分割推奨

3. **テスタビリティ向上** (重要度: 中)
   - UI要件の検証方法明記
`,
  recommendations: [
    "非機能要件の詳細仕様策定",
    "ドメインモデリングによる設計品質向上",
    "テスト戦略の早期策定"
  ],
  nextActions: ["Phase 5: Domain Modeling"],
  warnings: [
    "非機能要件の曖昧さが実装段階でリスクとなる可能性"
  ],
  shouldBlockProgress: false
};
```

### Phase 5: Domain Modeling 🏗️

**Task Adapter**: Domain Modeling Task Adapter  
**主要機能**: ドメイン駆動設計（DDD）によるモデリング

```text
// 呼び出し例
const request: TaskRequest = {
  description: "ドメインモデルの設計",
  prompt: "検証済み要件とストーリーからDDDアプローチでドメインモデルを設計",
  subagent_type: "domain-modeling"
};

// 応答例 (処理時間: 30-90秒)
const response: TaskResponse = {
  summary: "6エンティティ、2境界コンテキスト、12ビジネスルールを特定",
  analysis: `
## ドメインモデル設計結果

### 境界コンテキスト

#### 1. 商品管理コンテキスト (Product Management Context)
**責務**: 商品の生命周期管理

**エンティティ:**
- **Product** (集約ルート)
  - productId: ProductId
  - name: ProductName
  - price: Price
  - description: Description
  - category: Category
  - createdAt: DateTime

- **Inventory** (集約ルート)  
  - inventoryId: InventoryId
  - productId: ProductId
  - quantity: Quantity
  - reservedQuantity: Quantity
  - lastUpdated: DateTime

**ビジネスルール:**
1. 商品価格は0より大きい値である必要がある
2. 在庫数は0以上の整数である必要がある
3. 商品名は一意である必要がある

#### 2. 注文管理コンテキスト (Order Management Context)
**責務**: 注文処理とステータス管理

**エンティティ:**
- **Order** (集約ルート)
  - orderId: OrderId
  - customerId: CustomerId
  - orderItems: List<OrderItem>
  - status: OrderStatus
  - totalAmount: Money

**値オブジェクト:**
- **OrderItem**
  - productId: ProductId
  - quantity: Quantity
  - unitPrice: Price

### ドメインサービス
1. **在庫確認サービス**: 注文時の在庫可用性チェック
2. **価格計算サービス**: 割引・税金計算

### イベント
1. **ProductCreated**: 商品作成時
2. **InventoryUpdated**: 在庫変更時
3. **OrderPlaced**: 注文確定時

### 技術的推奨事項
- **アーキテクチャ**: ヘキサゴナルアーキテクチャ
- **永続化**: Repository パターン
- **イベント**: ドメインイベントによる結合度低減
`,
  recommendations: [
    "UI生成でドメインモデルベースの画面設計実行",
    "Repository実装でデータアクセス層分離",
    "ドメインイベント活用で疎結合アーキテクチャ構築"
  ],
  nextActions: ["Phase 6: UI Generation"],
  warnings: [],
  shouldBlockProgress: false
};
```

### Phase 6: UI Generation 🎨 ⭐ **2025年完全実装**

**Task Adapter**: UI Generation Task Adapter  
**主要機能**: React+Next.js完全自動生成

```text
// 呼び出し例
const request: TaskRequest = {
  description: "React UIコンポーネントの自動生成",
  prompt: "ドメインモデルからCRUD操作可能な高品質UIを生成",
  subagent_type: "ui-generation"
};

// 応答例 (処理時間: <30秒で21ファイル生成!)
const response: TaskResponse = {
  summary: "React+Next.js UI一式を30秒で生成完了 (21ファイル)",
  analysis: `
## UI生成結果 🎨

### 生成されたコンポーネント (21ファイル)

#### Core Components
1. **ProductForm.tsx** 
   - TypeScript完全型付け
   - React Hook Form統合
   - Zod バリデーション
   - WCAG 2.1 AA準拠

2. **ProductCard.tsx**
   - Radix UI Primitives使用
   - CVA variants適用
   - レスポンシブデザイン

3. **ProductList.tsx**
   - Virtual scrolling対応
   - TanStack Query統合
   - 検索・フィルタリング機能

4. **InventoryDashboard.tsx**
   - リアルタイム在庫表示
   - Chart.js統合
   - アクセシブルなデータ可視化

#### Generated Files Structure
\`\`\`
apps/web/
├── app/[locale]/                 # App Router (Next.js 14)
│   ├── products/
│   │   ├── page.tsx             # 商品一覧ページ
│   │   ├── create/page.tsx      # 商品作成ページ
│   │   └── [id]/
│   │       ├── page.tsx         # 商品詳細ページ
│   │       └── edit/page.tsx    # 商品編集ページ
│   └── inventory/
│       └── page.tsx             # 在庫管理ページ
├── components/ui/               # 再利用可能UIコンポーネント
│   ├── button.tsx
│   ├── input.tsx
│   ├── card.tsx
│   └── dialog.tsx
├── components/product/          # ドメイン固有コンポーネント
│   ├── product-form.tsx
│   ├── product-card.tsx
│   └── product-list.tsx
├── messages/                    # i18n対応
│   ├── en.json
│   └── ja.json
└── __e2e__/                    # E2Eテスト
    ├── product.spec.ts
    └── inventory.spec.ts
\`\`\`

### 品質メトリクス 📊

#### Lighthouse スコア
- **Performance**: 94/100 ⭐
- **Accessibility**: 100/100 ⭐
- **Best Practices**: 96/100 ⭐
- **SEO**: 92/100 ⭐

#### アクセシビリティ
- **WCAG 2.1 AA準拠**: 100% ✅
- **重大違反**: 0件 ✅
- **ARIA属性**: 完全実装 ✅
- **キーボードナビゲーション**: 全対応 ✅
- **スクリーンリーダー**: 完全対応 ✅

#### TypeScript品質
- **型カバレッジ**: 100% ✅
- **strictモード**: 有効 ✅
- **\`any\`型使用**: 0箇所 ✅

#### テスト品質
- **Unit テスト**: 21ファイル生成 ✅
- **E2E テスト**: 8シナリオカバー ✅
- **Storybook**: 全コンポーネント対応 ✅

### デザインシステム統合
- **Design Tokens**: Tailwind CSS統合
- **Color Palette**: アクセシブルなカラーセット
- **Typography**: システムフォント最適化
- **Spacing**: 8px グリッドシステム
- **Components**: shadcn/ui ベース

### 国際化 (i18n)
- **対応言語**: 英語、日本語
- **自動翻訳**: 基本UI文言
- **ロケールルーティング**: App Router統合
- **日付・通貨**: 地域別フォーマット
`,
  recommendations: [
    "E2Eテスト実行で動作検証推奨",
    "Storybookでコンポーネント仕様確認",
    "本番デプロイ前のセキュリティ監査実行"
  ],
  nextActions: [
    "品質ゲート実行",
    "セキュリティ監査実行", 
    "パフォーマンステスト実行",
    "本番デプロイ検討"
  ],
  warnings: [],
  shouldBlockProgress: false
};
```

---

## 実際の呼び出しフロー

### 🔄 完全な開発フロー例

```
👤 User: "ECサイトの商品管理機能を作りたいです"

🤖 Claude Code: 
要件分析から開始します。ae-frameworkのIntent Task Adapterを使用...

[Intent Task Adapter実行 - 15秒]
✅ Phase 1完了: 12項目の要件を特定
📋 次は詳細要件の構造化を行いますか？

👤 User: "はい、お願いします"

🤖 Claude Code:
Natural Language Task Adapterで要件構造化中...

[Natural Language Task Adapter実行 - 25秒]
✅ Phase 2完了: 15件の要件を機能・非機能・ビジネス要件に分類
🔍 続いてユーザーストーリー作成に進みますか？

👤 User: "はい、アジャイル開発に対応してください"

🤖 Claude Code:
User Stories Task Adapterでストーリー生成中...

[User Stories Task Adapter実行 - 40秒]
✅ Phase 3完了: 8つのストーリーを3エピックに整理 (34ポイント)
🔍 品質検証に進みますか？

👤 User: "品質チェックをお願いします"

🤖 Claude Code:
Validation Task Adapterで整合性検証中...

[Validation Task Adapter実行 - 45秒]
✅ Phase 4完了: 90%の整合性達成、改善点3件特定
🏗️ ドメインモデル設計に進みますか？

👤 User: "DDDアプローチで設計してください"

🤖 Claude Code:
Domain Modeling Task Adapterで設計中...

[Domain Modeling Task Adapter実行 - 70秒]
✅ Phase 5完了: 6エンティティ、2境界コンテキスト設計完了
🎨 最終的にUIまで生成しますか？

👤 User: "React+Next.jsでモダンなUIを生成してください"

🤖 Claude Code:
UI Generation Task Adapterで自動生成中...

[UI Generation Task Adapter実行 - 28秒] ⚡
✅ Phase 6完了: React+Next.js UI一式生成 (21ファイル)
🎨 品質メトリクス:
   • Lighthouse: Performance 94, A11y 100
   • WCAG 2.1 AA: 完全準拠
   • TypeScript: 100%型付け
   • テスト: Unit + E2E + Storybook完備

🚀 本番デプロイの準備が整いました！
```

### 📊 処理時間詳細

```
Phase 1 (Intent Analysis):      ~15秒
Phase 2 (Natural Language):     ~25秒  
Phase 3 (User Stories):         ~40秒
Phase 4 (Validation):           ~45秒
Phase 5 (Domain Modeling):      ~70秒
Phase 6 (UI Generation):        ~28秒 ⚡
───────────────────────────────────
合計処理時間:                   ~223秒 (約3分43秒)
```

**🎯 結果: 自然言語指示から本格的なWebアプリケーション完成まで4分以内!**

---

## 使用例とベストプラクティス

### 🎯 効果的な指示の仕方

#### ✅ 良い例

```
👤 "ECサイトの商品管理システムを作成してください。
    要件：
    - 商品の登録・編集・削除
    - 在庫管理（入荷・出荷・アラート）
    - カテゴリ管理
    - 売上レポート機能
    - 管理者権限制御
    
    非機能要件：
    - 同時アクセス100ユーザー対応
    - ページ読み込み2秒以内
    - WCAG 2.1 AA準拠"

→ 明確で構造化された指示により最適な結果
```

#### ❌ 避けるべき例

```
👤 "なんか商品管理するやつ作って"

→ 曖昧な指示では要件分析で多くの確認が必要
```

### 🔧 段階的開発アプローチ

#### パターン1: フルフロー実行
```
User: "要件分析からUI生成まで一括実行"
→ 全6フェーズを連続実行 (約4分)
→ 最終成果物まで一気に完成
```

#### パターン2: 段階的確認
```
User: "まず要件分析だけ実行"
→ Phase 1-2実行、結果確認
User: "続きをお願いします"
→ Phase 3-4実行、中間確認
User: "UIまで生成してください"
→ Phase 5-6実行、完成
```

#### パターン3: 特定フェーズ実行
```
User: "このドメインモデルからUIを生成"
→ Phase 6のみ実行 (30秒で完了)
→ 既存設計からの迅速なUI実装
```

### 📋 プロジェクト規模別推奨事項

#### 小規模プロジェクト (要件数 <20)
- **推奨**: フルフロー一括実行
- **時間**: 3-5分で完成
- **メリット**: 最速での成果物完成

#### 中規模プロジェクト (要件数 20-100)
- **推奨**: 段階的確認アプローチ
- **時間**: 10-15分（確認時間含む）
- **メリット**: 途中での方向修正可能

#### 大規模プロジェクト (要件数 100+)
- **推奨**: 境界コンテキスト別実行
- **時間**: 20-30分
- **メリット**: 複雑性の管理と品質担保

---

## パフォーマンスと最適化

### ⚡ 処理速度実績

#### Phase別処理時間 (平均値)
| Phase | 処理内容 | 時間(秒) | 成果物 |
|-------|----------|----------|--------|
| 1 | Intent Analysis | 10-20 | 要件一覧、意図分析 |
| 2 | Natural Language | 15-30 | 構造化要件、エンティティ |
| 3 | User Stories | 20-45 | ストーリー、エピック |
| 4 | Validation | 25-60 | 整合性レポート、改善点 |
| 5 | Domain Modeling | 30-90 | ドメインモデル、設計書 |
| 6 | UI Generation | **<30** | **21ファイル UI一式** ⭐ |

#### 🚀 Phase 6の圧倒的速度

```
従来の手動開発:
  設計: 2-4時間
  実装: 8-16時間  
  テスト: 4-8時間
  品質チェック: 2-4時間
  ─────────────────
  合計: 16-32時間

AE Framework Phase 6:
  自動生成: 30秒以内 ⚡
  品質保証: 自動完了
  テスト: 自動生成
  ─────────────────
  合計: 30秒 (1900倍+ 高速化!)
```

### 💾 メモリとリソース使用量

#### システム要件
- **最小メモリ**: 512MB
- **推奨メモリ**: 2GB
- **ディスク容量**: 1GB (生成物含む)
- **CPU**: 2コア以上推奨

#### 規模別リソース使用量
```
小規模 (<50要件):
  メモリ: ~100MB
  処理時間: 2-4分
  生成ファイル: 10-15個

中規模 (50-200要件):
  メモリ: ~200MB  
  処理時間: 5-10分
  生成ファイル: 20-35個

大規模 (200+要件):
  メモリ: ~400MB
  処理時間: 10-20分
  生成ファイル: 40-60個
```

### 🔧 最適化設定

#### パフォーマンス調整
```text
// 高速化設定
const optimizedConfig = {
  // 並列処理の最大数
  maxConcurrency: 4,
  
  // キャッシュ有効化
  enableCaching: true,
  
  // 詳細分析の簡略化
  detailedAnalysis: false,
  
  // 生成物の最小セット
  minimalOutput: true
};
```

#### 品質重視設定
```text
// 品質重視設定
const qualityConfig = {
  // 詳細検証有効化
  comprehensiveValidation: true,
  
  // 複数観点からの分析
  multiPerspectiveAnalysis: true,
  
  // 完全なドキュメント生成
  fullDocumentation: true,
  
  // 厳密な品質ゲート
  strictQualityGates: true
};
```

---

## トラブルシューティング

### 🚨 よくある問題と解決方法

#### 1. Task Tool呼び出しエラー

**症状**: `Task Tool not found` エラー
```
Error: Task Tool integration not available
```

**原因と解決**:
```text
// 原因: Claude Code統合が無効
enableClaudeCodeIntegration: false

// 解決: 統合を有効化
export const config: HybridIntentConfig = {
  enableClaudeCodeIntegration: true,  // ✅ 有効化
  enableCLI: true,
  enableMCPServer: false,
  enforceRealTime: true,
  strictMode: false
};
```

#### 2. 処理タイムアウト

**症状**: 長時間処理が完了しない
```
Warning: Task execution timeout (>300s)
```

**原因と解決**:
```text
// 原因: 大量の要件による処理負荷
// 解決: バッチサイズ制限
const processingConfig = {
  maxRequirements: 50,     // 要件数制限
  batchSize: 10,           // バッチサイズ
  timeoutMs: 180000        // 3分でタイムアウト
};
```

#### 3. UI生成品質問題

**症状**: 生成されたUIの品質が期待以下
```
Warning: Generated UI failed quality gates
```

**解決方法**:
```text
// 品質設定の調整
const uiQualityConfig = {
  accessibilityLevel: 'WCAG_AA',    // アクセシビリティレベル
  performanceTarget: 90,             // Lighthouseスコア目標
  typeScriptStrict: true,            // TypeScript厳密モード
  testCoverage: 0.8                  // テストカバレッジ目標
};
```

#### 4. メモリ不足エラー

**症状**: `Out of memory` エラー
```
Error: JavaScript heap out of memory
```

**解決方法**:
```bash
# Node.js メモリ制限拡張
export NODE_OPTIONS="--max-old-space-size=4096"

# または分割実行アプローチ
# 大規模プロジェクトを境界コンテキスト別に分割
```

### 🔧 診断コマンド

#### システム状態確認
```bash
# AE Framework状態確認
npx ae-framework health-check

# Claude Code統合確認
npx ae-framework integration-status

# リソース使用量確認
npx ae-framework resource-usage
```

#### ログ出力設定
```text
// デバッグログ有効化
const debugConfig = {
  logLevel: 'debug',
  enableDetailedLogging: true,
  outputToFile: true,
  logFile: './logs/ae-framework-debug.log'
};
```

### 📞 サポート情報

#### ドキュメント参照
- **Technical Implementation**: `/docs/architecture/TECHNICAL-IMPLEMENTATION-DETAILS.md`
- **Phase 6 Details**: `/docs/phases/phase-6-uiux.md`
- **Quality System**: `/docs/quality/quality-implementation-status.md`

#### 問題報告
```
GitHub Issues: https://github.com/itdojp/ae-framework/issues
Template: Bug Report / Feature Request / Integration Issue
```

---

## 🎯 まとめ

### 🌟 AE Framework × Claude Code統合の価値

1. **開発効率の革命的向上**
   - 手動開発: 16-32時間 → AI自動化: 4分以内
   - **1900倍以上の高速化**実現

2. **品質保証の自動化**
   - WCAG 2.1 AA準拠: 100%自動達成
   - Lighthouse >90: 確実な性能担保
   - TypeScript 100%: 完全型安全性

3. **学習コストゼロ**
   - 複雑なCLIコマンド不要
   - 自然言語指示のみで完成
   - プロアクティブガイダンス提供

4. **エンタープライズ対応**
   - セキュリティ監査統合
   - Runtime Conformance検証
   - 包括的テスト自動生成

### 🚀 次世代開発の実現

**AE Framework**はClaude Codeとの完全統合により、**「自然言語 → 厳密仕様 → 正しいコード」**の完全自動化を実現し、AI-Enhanced Developmentの新標準となっています。

**開発チームは今すぐ**:
- ✨ **90%以上の時間短縮**
- 🛡️ **ゼロ品質トラブル**  
- ♿ **完全アクセシブル**
- 🏢 **エンタープライズ対応**

を実現できます。

---

**📚 関連ドキュメント**
- [Phase 6 UI/UX Details](../phases/phase-6-uiux.md)
- [Technical Implementation](../architecture/TECHNICAL-IMPLEMENTATION-DETAILS.md)
- [Quality System Guide](../quality/quality-implementation-status.md)
- [Architecture Overview](../architecture/AE-FRAMEWORK-ARCHITECTURE-2025.md)

**🔗 外部リンク**
- [Claude Code Documentation](https://docs.anthropic.com/en/docs/claude-code)
- [AE Framework GitHub](https://github.com/itdojp/ae-framework)
