---
docRole: derived
canonicalSource:
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
lastVerified: '2026-03-23'
---
# 🎯 AE Framework Phase-Detailed Architecture

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Comprehensive technical details of the functions, implementation methods, and architecture for each phase of the AI-Enhanced Development Framework**

## 📋 Table of Contents

1. [Phase 1: Intent Analysis](#phase-1-intent-analysis)
2. [Phase 2: Natural Language Requirements](#phase-2-natural-language-requirements)
3. [Phase 3: User Stories Creation](#phase-3-user-stories-creation)
4. [Phase 4: Validation](#phase-4-validation)
5. [Phase 5: Domain Modeling](#phase-5-domain-modeling)
6. [Phase 6: UI/UX & Frontend Delivery](#phase-6-uiux--frontend-delivery)
7. [Inter-Phase Integration and Data Flow](#-inter-phase-integration-and-data-flow)
8. [Summary](#-summary)

---

## Phase 1: Intent Analysis

### 🎯 Purpose and Overview

Phase 1 converts natural-language input into structured development intent. The objective is not only to understand user wording, but also to establish category, priority, complexity, scope, assumptions, and constraints in a form that later phases can process deterministically.

### 📌 Key Features

#### 1.1 Natural Language Processing
- **Function**: Parse free-form user input and extract development intent.
- **Implementation**:
  - intent understanding through LLM-assisted analysis
  - contextual classification of requirements and constraints
  - keyword extraction and semantic normalization
- **Technical Details**:
  ```text
  class IntentAnalyzer {
    async analyzeIntent(userInput: string): Promise<IntentResult> {
      const context = this.extractContext(userInput);
      const keywords = this.extractKeywords(userInput);
      const intent = await this.intentEngine.analyze({
        input: userInput,
        context,
        keywords,
      });
      return this.structureIntent(intent);
    }
  }
  ```

#### 1.2 Intent Classification
- **Function**: Classify analyzed intent into execution-relevant categories.
- **Categories**:
  - Feature Development
  - Bug Fix
  - Refactoring
  - Quality Improvement
- **Classification Axes**:
  - urgency: High / Medium / Low
  - complexity: Simple / Moderate / Complex
  - scope: Component / Module / System

#### 1.3 Requirement Prioritization
- **Function**: Assign priority using a MoSCoW-style decision model.
- **Implementation**:
  - Must have
  - Should have
  - Could have
  - Won't have
- **Operational Benefit**: Later phases can preserve business-critical paths while separating optional improvements.

### 🔧 Technical Implementation

#### Intent Agent Architecture
```text
interface IntentAgent {
  analyzeUserIntent(input: UserInput): Promise<Intent>;
  validateIntent(intent: Intent): ValidationResult;
  structureIntent(rawIntent: RawIntent): StructuredIntent;
}

interface Intent {
  id: string;
  category: IntentCategory;
  priority: Priority;
  complexity: Complexity;
  scope: Scope;
  requirements: string[];
  constraints: string[];
  acceptanceCriteria: string[];
}
```

#### Hybrid Intent System Integration
- LLM-backed intent analysis expands interpretation depth.
- MCP or persistence surfaces retain intent artifacts for downstream reuse.
- CLI integration keeps operator-triggered intent capture aligned with repository execution.

### 📊 Phase 1 Quality Metrics
- intent understanding accuracy: >=95%
- classification accuracy: >=90%
- processing time: <5 seconds
- misinterpretation rate: <5%

---

## Phase 2: Natural Language Requirements

### 📝 Purpose and Overview

Phase 2 expands Phase 1 intent into explicit natural-language requirements. The output remains business-readable, but becomes traceable, structured, and ready for story creation and validation.

### 📌 Key Features

#### 2.1 Requirements Specification Generation
- **Function**: Expand intent into a detailed requirements document.
- **Implementation**:
  - template-based document generation
  - industry-standard structure and labeling
  - stakeholder-oriented grouping of functional and non-functional requirements
- **Output Shape**:
  - overview
  - functional requirements
  - non-functional requirements
  - constraints and assumptions

#### 2.2 Requirements Traceability
- **Function**: Make dependencies and impact relationships explicit.
- **Implementation**:
  - requirement ID assignment
  - dependency matrix generation
  - change impact analysis
- **Technical Details**:
  ```text
  interface RequirementTrace {
    id: string;
    parentIntent: string;
    dependencies: string[];
    impactedBy: string[];
    traceabilityMatrix: TraceMatrix;
  }
  ```

#### 2.3 Stakeholder-Specific Requirements
- **Function**: Reframe requirements for different stakeholders.
- **Stakeholders**:
  - end users
  - business owners
  - engineering teams
  - operations teams
- **Benefit**: The same intent can be validated from delivery, runtime, and governance perspectives.

### 🔧 Technical Implementation

#### Natural Language Task Adapter
```text
class NaturalLanguageTaskAdapter {
  async processIntent(intent: Intent): Promise<Requirements> {
    const context = await this.buildContext(intent);
    const templates = await this.loadTemplates(intent.category);
    return {
      functional: await this.generateFunctionalReqs(intent, context),
      nonFunctional: await this.generateNonFunctionalReqs(intent, context),
      constraints: await this.generateConstraints(intent, context),
      assumptions: await this.generateAssumptions(intent, context),
    };
  }
}
```

#### Requirements Extractor Engine
- automatic extraction assisted by AI or deterministic rules
- completeness and consistency verification
- ambiguity, duplication, and contradiction detection

### 📊 Phase 2 Quality Metrics
- requirements completeness: >=95%
- ambiguity detection rate: >=90%
- requirements coverage: 100%
- stakeholder approval rate: >=95%

---

## Phase 3: User Stories Creation

### 📋 Purpose and Overview

Phase 3 transforms natural-language requirements into implementation-sized user stories. The output is intended for planning and execution, not just documentation.

### 📌 Key Features

#### 3.1 User Story Generation
- **Function**: Generate user stories from requirements.
- **Implementation**:
  - `As a ... I want ... So that ...` structure
  - INVEST principle enforcement
  - epic -> feature -> story hierarchy

#### 3.2 Acceptance Criteria Generation
- **Function**: Generate Given-When-Then style acceptance criteria.
- **Implementation**:
  - BDD-oriented scenarios
  - boundary-value coverage
  - abnormal-path generation
- **Technical Details**:
  ```text
  interface AcceptanceCriteria {
    id: string;
    scenario: string;
    given: string[];
    when: string;
    then: string[];
    examples?: DataTable;
  }
  ```

#### 3.3 Story Point Estimation
- **Function**: Estimate story size relatively.
- **Implementation**:
  - Fibonacci sequence
  - joint evaluation of complexity, uncertainty, and effort
  - historical calibration when prior data exists

### 🔧 Technical Implementation

#### User Stories Task Adapter
```text
class UserStoriesTaskAdapter {
  async generateUserStories(requirements: Requirements): Promise<UserStory[]> {
    const epics = await this.createEpics(requirements);
    const features = await this.createFeatures(epics);
    const stories = await this.createStories(features);
    return stories.map((story) => ({
      ...story,
      acceptanceCriteria: this.generateAcceptanceCriteria(story),
      storyPoints: this.estimateStoryPoints(story),
      priority: this.calculatePriority(story),
    }));
  }
}
```

#### Story Generator Engine
- template management by industry or project type
- INVEST-oriented quality checks
- dependency detection across stories

### 📊 Phase 3 Quality Metrics
- INVEST compliance: >=95%
- acceptance criteria coverage: 100%
- estimation accuracy: within +/-20%
- story slicing appropriateness: >=90%

### 🛡️ TDD Guard Integration
- test-first generation from acceptance criteria
- minimum coverage target: >=80%
- explicit boundary and abnormal-path test expectations

---

## Phase 4: Validation

### 🔍 Purpose and Overview

Phase 4 validates generated stories and specifications from multiple viewpoints before implementation. The focus is business value, technical feasibility, consistency, and quality-gate readiness.

### 📌 Key Features

#### 4.1 Cross Validation
- **Validation Perspectives**:
  - business value and ROI
  - technical feasibility and architecture constraints
  - UX/UI and accessibility impact
  - security threats and vulnerability exposure
- **Technical Details**:
  ```text
  interface CrossValidator {
    validateBusiness(story: UserStory): BusinessValidation;
    validateTechnical(story: UserStory): TechnicalValidation;
    validateUX(story: UserStory): UXValidation;
    validateSecurity(story: UserStory): SecurityValidation;
    validateIntegration(stories: UserStory[]): IntegrationValidation;
  }
  ```

#### 4.2 Consistency Check
- **Function**: Verify consistency between stories, schemas, interfaces, and execution order.
- **Checks**:
  - logical contradictions
  - data and schema alignment
  - API/UI consistency
  - delivery sequence consistency

#### 4.3 Quality Gate Assessment
- **Function**: Assess readiness against predefined quality gates.
- **Gates**:
  - completeness gate
  - testability gate
  - sizing gate
  - dependency gate

### 🔧 Technical Implementation

#### Validation Task Adapter
```text
class ValidationTaskAdapter {
  async performValidation(stories: UserStory[]): Promise<ValidationReport> {
    const results = await Promise.all([
      this.crossValidator.validateAll(stories),
      this.consistencyChecker.checkAll(stories),
      this.qualityGateAssessor.assess(stories),
      this.riskAnalyzer.analyze(stories),
    ]);
    return this.generateValidationReport(results);
  }
}
```

#### Cross Validator Engine
- AI-assisted reasoning for ambiguous cases
- rule-based validation for deterministic checks
- historical comparison against prior projects when useful

### 📊 Phase 4 Quality Metrics
- validation coverage: 100%
- validation accuracy: >=95%
- false-positive rate: <5%
- true issue detection rate: >=90%

### 🛡️ Test Guard Integration
- acceptance-criteria-derived tests
- boundary-value scenario expansion
- abnormal-path completeness checks

---

## Phase 5: Domain Modeling

### 🏗️ Purpose and Overview

Phase 5 builds implementable domain models from validated stories. The emphasis is on DDD-aligned structure: entities, aggregates, domain services, value objects, and bounded contexts.

### 📌 Key Features

#### 5.1 Domain Entity Extraction
- **Function**: Extract domain entities and relationships from stories.
- **Implementation**:
  - noun phrase and concept extraction
  - relationship mapping
  - attribute inference and type assignment

#### 5.2 Aggregate Design
- **Function**: Define DDD aggregates and consistency boundaries.
- **Implementation**:
  - aggregate root identification
  - transaction and invariants boundary setting
  - business invariant definition
- **Technical Details**:
  ```text
  interface Aggregate {
    root: Entity;
    entities: Entity[];
    valueObjects: ValueObject[];
    invariants: BusinessInvariant[];
    events: DomainEvent[];
  }
  ```

#### 5.3 Domain Service Design
- **Function**: Extract business logic that should not live inside a single entity.
- **Typical Cases**:
  - multi-entity operations
  - external-system coordination
  - complex business rules spanning aggregate boundaries

### 🔧 Technical Implementation

#### Domain Modeling Task Adapter
```text
class DomainModelingTaskAdapter {
  async generateDomainModel(stories: UserStory[]): Promise<DomainModel> {
    const entities = await this.extractEntities(stories);
    const relationships = await this.analyzeRelationships(entities);
    const aggregates = await this.designAggregates(entities, relationships);
    const services = await this.designDomainServices(aggregates, stories);
    const valueObjects = await this.extractValueObjects(entities);
    return {
      entities,
      aggregates,
      services,
      valueObjects,
      relationships,
      boundedContexts: await this.identifyBoundedContexts(aggregates),
    };
  }
}
```

#### Domain Generator Engine
- pattern application for DDD and implementation patterns
- code generation for major languages when relevant
- schema generation for persistence models

### 📊 Phase 5 Quality Metrics
- entity extraction coverage: >=95%
- relationship accuracy: >=90%
- aggregate appropriateness: >=85%
- code quality targets: complexity <10, maintainability >80

### 🛡️ Coverage Guard Integration
- domain logic coverage: >=90%
- business-rule coverage: 100%
- explicit abnormal-path tests for aggregate and service behavior

---

## Phase 6: UI/UX & Frontend Delivery

### 🎨 Purpose and Overview

Phase 6 generates React + Next.js frontend deliverables from domain models. The target is not a toy prototype, but a delivery-ready baseline that considers accessibility, internationalization, testing, and performance.

### 📌 Key Features

#### 6.1 UI Component Generation
- **Function**: Generate forms, lists, detail views, and search surfaces from entities.
- **Outputs**:
  - CRUD forms
  - list and table views
  - detail pages
  - search and filter surfaces

#### 6.2 Design System Integration
- **Function**: Apply a consistent design system.
- **Elements**:
  - design tokens
  - Tailwind CSS
  - Class Variance Authority
  - Radix UI / shadcn primitives

#### 6.3 Accessibility First
- **Function**: Encode WCAG 2.1 AA considerations by default.
- **Checks**:
  - ARIA and semantic labeling
  - keyboard navigation
  - color contrast
  - screen-reader-friendly ordering

#### 6.4 Internationalization
- **Function**: Support multi-language delivery through `next-intl` style message separation.
- **Outputs**:
  - translation keys
  - message JSON
  - typed translation access patterns

#### 6.5 Test Generation
- **Function**: Generate tests for the produced UI.
- **Test Types**:
  - unit tests with Vitest and Testing Library
  - end-to-end tests with Playwright
  - visual tests with Storybook
  - accessibility checks with `jest-axe`-style tooling

### 🔧 Technical Implementation

#### UI Generation Pipeline
```text
class UIGenerationPipeline {
  async generateUIComponents(domainModel: DomainModel): Promise<GeneratedUI> {
    const uiSpec = await this.analyzeEntities(domainModel.entities);
    const components = await this.processTemplates(uiSpec);
    const styledComponents = await this.applyDesignSystem(components);
    const accessibleComponents = await this.enhanceAccessibility(styledComponents);
    const i18nComponents = await this.addInternationalization(accessibleComponents);
    const tests = await this.generateTests(i18nComponents);
    return {
      components: i18nComponents,
      tests,
      stories: await this.generateStorybook(i18nComponents),
      translations: await this.generateTranslations(i18nComponents),
    };
  }
}
```

#### Handlebars Template Engine
- template-driven component generation for predictable scaffolding
- consistent handling of labels, validation, and message keys
- reusable rendering patterns for forms and detail screens

### 📊 Phase 6 Quality Metrics
- generation time: <30 seconds for baseline component output
- accessibility conformance: >=95% toward WCAG 2.1 AA
- performance targets:
  - LCP <2.5s
  - FID/INP equivalent interaction budgets <100ms where measured
  - CLS <0.1
- code quality targets:
  - TypeScript errors: 0
  - ESLint errors: 0
  - test coverage: >=80%

### 🛡️ Quality Guards Integration
- accessibility guard
- performance guard
- security guard
- i18n guard

---

## 🔄 Inter-Phase Integration and Data Flow

### 📊 Inter-Phase Data Transformation

```text
type PhaseDataFlow = {
  Phase1: { input: UserInput; output: Intent; };
  Phase2: { input: Intent; output: Requirements; };
  Phase3: { input: Requirements; output: UserStory[]; };
  Phase4: { input: UserStory[]; output: ValidatedStories; };
  Phase5: { input: ValidatedStories; output: DomainModel; };
  Phase6: { input: DomainModel; output: GeneratedUI; };
};
```

### 🔄 Quality Assurance Process
1. Phase 1-2 secure input and requirements quality.
2. Phase 3 introduces TDD-oriented delivery structure.
3. Phase 4 performs cross-perspective validation.
4. Phase 5 enforces architecture and domain quality.
5. Phase 6 verifies UI/UX, accessibility, and delivery readiness.

### 📈 Continuous Improvement
- telemetry collection across phases
- feedback loops from later phases into earlier artifacts
- pattern learning from previous projects where reuse is justified

---

## 🎯 Summary

The six-phase architecture provides a structured path from ambiguous natural-language intent to validated domain models and frontend delivery artifacts.

### ✨ Characteristics
- phased decomposition with explicit handoff artifacts
- quality metrics and guardrails at every stage
- traceable transformation from intent to delivery output
- compatibility with AI-assisted analysis and deterministic validation

### 🚀 Innovation Points
- combines AI-assisted authoring with contract-aware validation
- keeps business-readable artifacts alongside implementation-oriented outputs
- makes quality gates and recovery points explicit instead of implicit

---

[Content continues with Japanese section...]

---

## Japanese

**AI-Enhanced Development Framework の各フェーズにおける機能、実現方法、技術的詳細**

## 📋 目次

1. [Phase 1: Intent Analysis (意図解析)](#phase-1-intent-analysis-意図解析)
2. [Phase 2: Natural Language Requirements (自然言語要求)](#phase-2-natural-language-requirements-自然言語要求)
3. [Phase 3: User Stories Creation (ユーザーストーリー作成)](#phase-3-user-stories-creation-ユーザーストーリー作成)
4. [Phase 4: Validation (検証)](#phase-4-validation-検証)
5. [Phase 5: Domain Modeling (ドメインモデリング)](#phase-5-domain-modeling-ドメインモデリング)
6. [Phase 6: UI/UX & Frontend Delivery (UI/UX・フロントエンド配信)](#phase-6-uiux--frontend-delivery-uiuxフロントエンド配信)

---

## Phase 1: Intent Analysis (意図解析)

### 🎯 目的と概要

Phase 1では、ユーザーからの自然言語による入力を解析し、開発意図を明確化します。曖昧な要求を構造化された意図に変換し、後続フェーズで処理可能な形式に整理します。

### 📌 主要機能

#### 1.1 自然言語解析 (Natural Language Processing)
- **機能**: ユーザーの自然言語入力を解析し、開発意図を抽出
- **実現方法**: 
  - Claude APIを活用した意図理解
  - 文脈理解による要求の分類
  - キーワード抽出とセマンティック解析
- **技術詳細**:
  ```text
  class IntentAnalyzer {
    async analyzeIntent(userInput: string): Promise<IntentResult> {
      const context = this.extractContext(userInput);
      const keywords = this.extractKeywords(userInput);
      const intent = await this.claudeAPI.analyzeIntent({
        input: userInput,
        context,
        keywords
      });
      return this.structureIntent(intent);
    }
  }
  ```

#### 1.2 意図分類 (Intent Classification)
- **機能**: 解析された意図をカテゴリ別に分類
- **実現方法**:
  - 機能開発意図 (Feature Development)
  - バグ修正意図 (Bug Fix)
  - リファクタリング意図 (Refactoring)
  - 品質改善意図 (Quality Improvement)
- **分類基準**:
  - 緊急度: High, Medium, Low
  - 複雑度: Simple, Moderate, Complex
  - スコープ: Component, Module, System

#### 1.3 要求優先度付け (Requirement Prioritization)
- **機能**: MoSCoW法による要求の優先度設定
- **実現方法**:
  - Must have: 必須要求
  - Should have: 重要要求
  - Could have: あると良い要求
  - Won't have: 対象外要求

### 🔧 技術的実装

#### Intent Agent アーキテクチャ
```text
interface IntentAgent {
  // 意図解析の核となるエージェント
  analyzeUserIntent(input: UserInput): Promise<Intent>;
  
  // 意図の妥当性検証
  validateIntent(intent: Intent): ValidationResult;
  
  // 意図の構造化
  structureIntent(rawIntent: RawIntent): StructuredIntent;
}

interface Intent {
  id: string;
  category: IntentCategory;
  priority: Priority;
  complexity: Complexity;
  scope: Scope;
  requirements: string[];
  constraints: string[];
  acceptanceCriteria: string[];
}
```

#### Hybrid Intent System 統合
- **Claude Code Task Tool**: 自然言語処理の高度化
- **MCP Server**: 意図解析結果の永続化
- **CLI Integration**: コマンドライン経由での意図入力

### 📊 Phase 1 品質メトリクス
- **意図理解精度**: ≥95%
- **分類正確性**: ≥90%
- **処理時間**: <5秒
- **誤解釈率**: <5%

---

## Phase 2: Natural Language Requirements (自然言語要求)

### 📝 目的と概要

Phase 2では、Phase 1で抽出された意図を詳細な自然言語要求仕様書に展開します。技術的な実装詳細は含まず、ビジネス要求として明確で理解しやすい形式で文書化します。

### 📌 主要機能

#### 2.1 要求仕様書生成 (Requirements Specification Generation)
- **機能**: 意図を詳細な要求仕様書に展開
- **実現方法**:
  - テンプレートベースの要求書生成
  - 業界標準フォーマットの適用
  - ステークホルダー別の視点での要求整理
- **出力例**:
  ```text
  ## 機能要求: ユーザー認証システム
  
  ### 概要
  システムは安全で使いやすいユーザー認証機能を提供する
  
  ### 機能要求
  1. ユーザーはメールアドレスとパスワードでログインできる
  2. パスワードは8文字以上で複雑性要求を満たす必要がある
  3. ログイン試行回数制限による不正アクセス防止
  
  ### 非機能要求
  1. 認証処理は2秒以内に完了する
  2. 99.9%の可用性を保証する
  3. GDPR準拠のデータ保護を実装する
  ```

#### 2.2 要求トレーサビリティ (Requirements Traceability)
- **機能**: 要求間の関係性と依存関係を明確化
- **実現方法**:
  - 要求ID付与システム
  - 依存関係マトリックスの自動生成
  - 変更影響分析の実装
- **技術詳細**:
  ```text
  interface RequirementTrace {
    id: string;
    parentIntent: string;
    dependencies: string[];
    impactedBy: string[];
    traceabilityMatrix: TraceMatrix;
  }
  ```

#### 2.3 ステークホルダー別要求 (Stakeholder-specific Requirements)
- **機能**: 各ステークホルダーの視点での要求整理
- **対象ステークホルダー**:
  - エンドユーザー要求
  - ビジネス要求
  - 技術チーム要求
  - 運用チーム要求

### 🔧 技術的実装

#### Natural Language Task Adapter
```text
class NaturalLanguageTaskAdapter {
  async processIntent(intent: Intent): Promise<Requirements> {
    const context = await this.buildContext(intent);
    const templates = await this.loadTemplates(intent.category);
    
    return {
      functional: await this.generateFunctionalReqs(intent, context),
      nonFunctional: await this.generateNonFunctionalReqs(intent, context),
      constraints: await this.generateConstraints(intent, context),
      assumptions: await this.generateAssumptions(intent, context)
    };
  }
}
```

#### Requirements Extractor エンジン
- **自動抽出**: AIを活用した要求の自動抽出
- **検証機能**: 要求の完全性・整合性チェック
- **品質保証**: 曖昧さ・重複・矛盾の検出

### 📊 Phase 2 品質メトリクス
- **要求完全性**: ≥95%
- **曖昧性検出率**: ≥90%
- **要求カバレッジ**: 100%
- **ステークホルダー承認率**: ≥95%

---

## Phase 3: User Stories Creation (ユーザーストーリー作成)

### 📋 目的と概要

Phase 3では、自然言語要求をアジャイル開発に適したユーザーストーリー形式に変換します。実装可能な単位で分割し、受け入れ条件と優先度を明確化します。

### 📌 主要機能

#### 3.1 ユーザーストーリー自動生成 (User Story Generation)
- **機能**: 要求からユーザーストーリーを自動生成
- **実現方法**:
  - As a [role], I want [goal], so that [benefit] 形式の適用
  - INVEST原則 (Independent, Negotiable, Valuable, Estimable, Small, Testable) の遵守
  - エピック→フィーチャー→ストーリーの階層化
- **出力例**:
  ```text
  ## Epic: ユーザー管理システム
  
  ### Feature: ユーザー認証
  
  #### User Story #US001
  **As a** 一般ユーザー
  **I want** メールアドレスとパスワードでログインしたい
  **So that** 自分のアカウントにアクセスできる
  
  **Acceptance Criteria:**
  - [ ] 有効なメールアドレス形式でのみログイン可能
  - [ ] パスワードは8文字以上である必要がある
  - [ ] 3回連続失敗でアカウントロック
  - [ ] ログイン成功後ダッシュボードにリダイレクト
  
  **Priority:** High
  **Estimation:** 5 Story Points
  **Dependencies:** None
  ```

#### 3.2 受け入れ条件生成 (Acceptance Criteria Generation)
- **機能**: Given-When-Then形式の受け入れ条件自動生成
- **実現方法**:
  - BDD (Behavior Driven Development) パターンの適用
  - 境界値分析による条件網羅
  - 異常系シナリオの自動生成
- **技術詳細**:
  ```text
  interface AcceptanceCriteria {
    id: string;
    scenario: string;
    given: string[];
    when: string;
    then: string[];
    examples?: DataTable;
  }
  ```

#### 3.3 ストーリーポイント見積もり (Story Point Estimation)
- **機能**: 相対見積もりによるストーリーポイント算出
- **実現方法**:
  - フィボナッチ数列 (1, 2, 3, 5, 8, 13, 21) の使用
  - 複雑度・不確実性・作業量の総合評価
  - 過去データによる見積もり精度向上

### 🔧 技術的実装

#### User Stories Task Adapter
```text
class UserStoriesTaskAdapter {
  async generateUserStories(requirements: Requirements): Promise<UserStory[]> {
    const epics = await this.createEpics(requirements);
    const features = await this.createFeatures(epics);
    const stories = await this.createStories(features);
    
    return stories.map(story => ({
      ...story,
      acceptanceCriteria: this.generateAcceptanceCriteria(story),
      storyPoints: this.estimateStoryPoints(story),
      priority: this.calculatePriority(story)
    }));
  }
}
```

#### Story Generator エンジン
- **テンプレート管理**: 業界別・プロジェクト別テンプレート
- **品質チェック**: INVEST原則の自動検証
- **依存関係分析**: ストーリー間の依存関係自動検出

### 📊 Phase 3 品質メトリクス
- **INVEST準拠率**: ≥95%
- **受け入れ条件カバレッジ**: 100%
- **見積もり精度**: ±20%以内
- **ストーリー分割適切性**: ≥90%

### 🛡️ TDD Guard 統合
Phase 3からTDD強制機能が有効になります：
- **テスト先行**: 受け入れ条件からテストケース自動生成
- **テストカバレッジ**: 最低80%のカバレッジ要求
- **テスト品質**: 境界値・異常系テストの強制

---

## Phase 4: Validation (検証)

### 🔍 目的と概要

Phase 4では、生成されたユーザーストーリーの妥当性を多角的に検証します。ビジネス価値、技術的実現可能性、品質要求を総合的に評価し、実装前の最終確認を行います。

### 📌 主要機能

#### 4.1 クロスバリデーション (Cross Validation)
- **機能**: 複数の観点からストーリーの妥当性を検証
- **検証観点**:
  - **ビジネス価値検証**: ROI分析、市場価値評価
  - **技術的実現可能性**: アーキテクチャ制約、技術的リスク
  - **UX/UI検証**: ユーザビリティ、アクセシビリティ
  - **セキュリティ検証**: 脅威分析、脆弱性評価
- **実現方法**:
  ```text
  interface CrossValidator {
    validateBusiness(story: UserStory): BusinessValidation;
    validateTechnical(story: UserStory): TechnicalValidation;
    validateUX(story: UserStory): UXValidation;
    validateSecurity(story: UserStory): SecurityValidation;
    validateIntegration(stories: UserStory[]): IntegrationValidation;
  }
  ```

#### 4.2 整合性チェック (Consistency Check)
- **機能**: ストーリー間の整合性と依存関係の検証
- **検証項目**:
  - **論理的整合性**: 矛盾する要求の検出
  - **データ整合性**: データフロー・スキーマの一貫性
  - **インターフェース整合性**: API・UI間の整合性
  - **時系列整合性**: 実装順序の妥当性
- **技術詳細**:
  ```text
  class ConsistencyChecker {
    async checkLogicalConsistency(stories: UserStory[]): Promise<ConsistencyResult> {
      const conflicts = [];
      for (const story1 of stories) {
        for (const story2 of stories) {
          if (this.hasLogicalConflict(story1, story2)) {
            conflicts.push({ story1: story1.id, story2: story2.id, type: 'logical' });
          }
        }
      }
      return { isValid: conflicts.length === 0, conflicts };
    }
  }
  ```

#### 4.3 品質ゲート評価 (Quality Gate Assessment)
- **機能**: 事前定義された品質基準による合格判定
- **品質ゲート**:
  - **完全性ゲート**: すべての受け入れ条件が定義済み
  - **テスト性ゲート**: テスト可能な形での定義
  - **見積もりゲート**: 適切なサイズでの分割
  - **依存関係ゲート**: 循環依存の不存在

### 🔧 技術的実装

#### Validation Task Adapter
```text
class ValidationTaskAdapter {
  async performValidation(stories: UserStory[]): Promise<ValidationReport> {
    const results = await Promise.all([
      this.crossValidator.validateAll(stories),
      this.consistencyChecker.checkAll(stories),
      this.qualityGateAssessor.assess(stories),
      this.riskAnalyzer.analyze(stories)
    ]);
    
    return this.generateValidationReport(results);
  }
}
```

#### Cross Validator エンジン
- **AI駆動検証**: Claude APIを活用した高度な妥当性判定
- **ルールベース検証**: 事前定義ルールによる自動検証
- **履歴ベース検証**: 過去プロジェクトデータとの比較検証

### 📊 Phase 4 品質メトリクス
- **検証カバレッジ**: 100% (全観点での検証実施)
- **検証精度**: ≥95% (人間によるレビューとの一致率)
- **誤検知率**: <5% (false positive)
- **検出率**: ≥90% (実際の問題検出率)

### 🛡️ Test Guard 統合
Phase 4でテスト品質の検証を強化：
- **テストケース生成**: 受け入れ条件からの自動テスト生成
- **境界値テスト**: 境界値分析によるテストケース拡充
- **異常系テスト**: エラーハンドリングの完全性検証

---

## Phase 5: Domain Modeling (ドメインモデリング)

### 🏗️ 目的と概要

Phase 5では、検証済みユーザーストーリーから実装可能なドメインモデルを構築します。DDD (Domain-Driven Design) 原則に基づき、ビジネスロジックを適切に表現する設計モデルを生成します。

### 📌 主要機能

#### 5.1 ドメインエンティティ抽出 (Domain Entity Extraction)
- **機能**: ユーザーストーリーからドメインエンティティを自動抽出
- **実現方法**:
  - **エンティティ識別**: 名詞句解析によるエンティティ候補抽出
  - **関係性分析**: エンティティ間の関係性マッピング
  - **属性推論**: エンティティの属性とその型の推論
- **出力例**:
  ```text
  interface DomainEntity {
    name: string;
    attributes: Attribute[];
    relationships: Relationship[];
    invariants: BusinessRule[];
    lifecycle: EntityLifecycle;
  }
  
  // 例: ユーザーエンティティ
  const UserEntity: DomainEntity = {
    name: "User",
    attributes: [
      { name: "id", type: "UUID", required: true, unique: true },
      { name: "email", type: "Email", required: true, unique: true },
      { name: "password", type: "HashedPassword", required: true },
      { name: "createdAt", type: "DateTime", required: true },
      { name: "lastLoginAt", type: "DateTime", required: false }
    ],
    relationships: [
      { type: "OneToMany", target: "UserSession", foreignKey: "userId" }
    ],
    invariants: [
      "Email must be unique across the system",
      "Password must meet complexity requirements"
    ],
    lifecycle: {
      states: ["Created", "Active", "Suspended", "Deleted"],
      transitions: [
        { from: "Created", to: "Active", trigger: "activate" },
        { from: "Active", to: "Suspended", trigger: "suspend" }
      ]
    }
  };
  ```

#### 5.2 集約設計 (Aggregate Design)
- **機能**: DDD集約パターンに基づく境界設定
- **実現方法**:
  - **集約ルート識別**: エンティティ間の所有関係分析
  - **境界定義**: トランザクション境界と整合性境界の設定
  - **不変条件**: 集約内で保証すべきビジネスルールの定義
- **技術詳細**:
  ```text
  interface Aggregate {
    root: Entity;
    entities: Entity[];
    valueObjects: ValueObject[];
    invariants: BusinessInvariant[];
    events: DomainEvent[];
  }
  ```

#### 5.3 ドメインサービス設計 (Domain Service Design)
- **機能**: エンティティに属さないビジネスロジックの抽出
- **識別基準**:
  - 複数エンティティにまたがる操作
  - 外部システムとの連携が必要な処理
  - 複雑なビジネスルールの実装

### 🔧 技術的実装

#### Domain Modeling Task Adapter
```text
class DomainModelingTaskAdapter {
  async generateDomainModel(stories: UserStory[]): Promise<DomainModel> {
    // 1. エンティティ抽出
    const entities = await this.extractEntities(stories);
    
    // 2. 関係性分析
    const relationships = await this.analyzeRelationships(entities);
    
    // 3. 集約設計
    const aggregates = await this.designAggregates(entities, relationships);
    
    // 4. ドメインサービス設計
    const services = await this.designDomainServices(aggregates, stories);
    
    // 5. 値オブジェクト抽出
    const valueObjects = await this.extractValueObjects(entities);
    
    return {
      entities,
      aggregates,
      services,
      valueObjects,
      relationships,
      boundedContexts: await this.identifyBoundedContexts(aggregates)
    };
  }
}
```

#### Domain Generator エンジン
- **パターン適用**: GoF、DDDパターンの自動適用
- **コード生成**: TypeScript/Java/C#でのドメインモデルコード生成
- **スキーマ生成**: データベーススキーマの自動生成

### 📊 Phase 5 品質メトリクス
- **エンティティ網羅性**: ≥95% (要求からのエンティティ抽出率)
- **関係性正確性**: ≥90% (関係性マッピング精度)
- **集約適切性**: ≥85% (DDD原則準拠率)
- **コード品質**: Complexity < 10, Maintainability > 80

### 🛡️ Coverage Guard 統合
Phase 5でコードカバレッジの検証を強化：
- **ドメインロジックカバレッジ**: ≥90%
- **ビジネスルールカバレッジ**: 100%
- **エラーパステスト**: 全異常パターンのテスト

---

## Phase 6: UI/UX & Frontend Delivery (UI/UX・フロントエンド配信)

### 🎨 目的と概要

Phase 6では、ドメインモデルに基づいてモダンなReact + Next.js UIを自動生成します。アクセシビリティ、国際化、パフォーマンスを考慮した高品質なフロントエンド実装を提供します。

### 📌 主要機能

#### 6.1 UIコンポーネント自動生成 (UI Component Generation)
- **機能**: ドメインエンティティからUIコンポーネントを自動生成
- **生成コンポーネント**:
  - **フォームコンポーネント**: エンティティCRUD操作用
  - **リストコンポーネント**: エンティティ一覧表示用
  - **詳細コンポーネント**: エンティティ詳細表示用
  - **検索コンポーネント**: エンティティ検索・フィルター用
- **実現方法**:
  ```text
  interface ComponentGenerator {
    generateForm(entity: DomainEntity): FormComponent;
    generateList(entity: DomainEntity): ListComponent;
    generateDetail(entity: DomainEntity): DetailComponent;
    generateSearch(entity: DomainEntity): SearchComponent;
  }
  
  // 例: ユーザーフォームコンポーネント生成
  const userForm = generator.generateForm(UserEntity);
  // 出力: UserForm.tsx with validation, accessibility, i18n support
  ```

#### 6.2 デザインシステム統合 (Design System Integration)
- **機能**: 一貫性のあるデザインシステムの適用
- **構成要素**:
  - **Design Tokens**: カラー、タイポグラフィ、スペーシング定義
  - **Tailwind CSS**: ユーティリティファーストCSS
  - **Class Variance Authority**: バリアント管理
  - **Radix UI + shadcn/ui**: アクセシブルなプリミティブ
- **技術詳細**:
  ```text
  // Design Tokens定義
  export const designTokens = {
    colors: {
      primary: {
        50: '#eff6ff',
        500: '#3b82f6',
        900: '#1e3a8a'
      }
    },
    typography: {
      fontFamily: {
        sans: ['Inter', 'system-ui', 'sans-serif']
      }
    },
    spacing: {
      xs: '0.25rem',
      sm: '0.5rem',
      md: '1rem'
    }
  };
  ```

#### 6.3 アクセシビリティファースト (Accessibility First)
- **機能**: WCAG 2.1 AA準拠の自動実装
- **実現要素**:
  - **ARIA属性**: 自動的なaria-label、aria-describedby設定
  - **キーボードナビゲーション**: 完全なキーボード操作対応
  - **カラーコントラスト**: 4.5:1以上のコントラスト比保証
  - **スクリーンリーダー**: 適切な読み上げ順序と内容
- **自動生成例**:
  ```tsx
  // 自動生成されるアクセシブルフォーム
  export function UserForm() {
    return (
      <form role="form" aria-labelledby="user-form-title">
        <h2 id="user-form-title">ユーザー登録</h2>
        
        <div className="field-group">
          <label htmlFor="email" className="required">
            メールアドレス
          </label>
          <input
            id="email"
            type="email"
            aria-required="true"
            aria-describedby="email-help email-error"
            aria-invalid={hasError ? 'true' : 'false'}
          />
          <div id="email-help" className="help-text">
            有効なメールアドレスを入力してください
          </div>
          {hasError && (
            <div id="email-error" role="alert" className="error-text">
              メールアドレス形式が正しくありません
            </div>
          )}
        </div>
      </form>
    );
  }
  ```

#### 6.4 国際化対応 (Internationalization)
- **機能**: next-intlによる多言語対応実装
- **対応言語**: 日本語、英語（拡張可能）
- **自動化要素**:
  - **翻訳キー生成**: コンポーネントから翻訳キー自動抽出
  - **メッセージファイル**: JSON形式での翻訳リソース管理
  - **型安全性**: TypeScriptによる翻訳キーの型チェック

#### 6.5 テスト自動生成 (Test Generation)
- **機能**: コンポーネント用テストの自動生成
- **テスト種別**:
  - **Unit Tests**: Vitest + Testing Libraryによる単体テスト
  - **E2E Tests**: Playwrightによるエンドツーエンドテスト
  - **Visual Tests**: Storybookによるビジュアルリグレッションテスト
  - **Accessibility Tests**: jest-axeによるアクセシビリティテスト

### 🔧 技術的実装

#### UI Generation Pipeline
```text
class UIGenerationPipeline {
  async generateUIComponents(domainModel: DomainModel): Promise<GeneratedUI> {
    // 1. エンティティ分析
    const uiSpec = await this.analyzeEntities(domainModel.entities);
    
    // 2. テンプレート処理
    const components = await this.processTemplates(uiSpec);
    
    // 3. デザインシステム適用
    const styledComponents = await this.applyDesignSystem(components);
    
    // 4. アクセシビリティ拡張
    const accessibleComponents = await this.enhanceAccessibility(styledComponents);
    
    // 5. 国際化対応
    const i18nComponents = await this.addInternationalization(accessibleComponents);
    
    // 6. テスト生成
    const tests = await this.generateTests(i18nComponents);
    
    return {
      components: i18nComponents,
      tests,
      stories: await this.generateStorybook(i18nComponents),
      translations: await this.generateTranslations(i18nComponents)
    };
  }
}
```

#### Handlebars Template Engine
```text
// テンプレート例: フォームコンポーネント
const formTemplate = `
'use client';

import { useState } from 'react';
import { useTranslations } from 'next-intl';
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Label } from '@/components/ui/label';

interface {{entityName}}FormProps {
  onSubmit: (data: {{entityName}}Data) => void;
  initialData?: Partial<{{entityName}}Data>;
}

export function {{entityName}}Form({ onSubmit, initialData }: {{entityName}}FormProps) {
  const t = useTranslations('{{entityName.toLowerCase}}');
  
  return (
    <form onSubmit={handleSubmit} className="space-y-4">
      <h2 className="text-2xl font-bold">{t('title')}</h2>
      
      {{#each attributes}}
      <div>
        <Label htmlFor="{{name}}" {{#if required}}className="required"{{/if}}>
          {t('fields.{{name}}')}
        </Label>
        <Input
          id="{{name}}"
          type="{{inputType}}"
          {{#if required}}required{{/if}}
          aria-describedby="{{name}}-help"
        />
      </div>
      {{/each}}
      
      <Button type="submit">{t('submit')}</Button>
    </form>
  );
}
`;
```

### 📊 Phase 6 品質メトリクス
- **生成効率**: <30秒でのコンポーネント生成
- **アクセシビリティ**: WCAG 2.1 AA ≥95%準拠
- **パフォーマンス**: 
  - LCP < 2.5秒
  - FID < 100ms
  - CLS < 0.1
- **コード品質**: 
  - TypeScript Errors: 0
  - ESLint Errors: 0
  - Test Coverage: ≥80%

### 🛡️ Quality Guards 統合
Phase 6で最終品質保証：
- **A11y Guard**: アクセシビリティ基準の強制
- **Performance Guard**: Core Web Vitalsの監視
- **Security Guard**: XSS、CSRF対策の確認
- **i18n Guard**: 国際化対応の完全性検証

---

## 🔄 フェーズ間統合・データフロー

### 📊 フェーズ間データ変換

```text
// Phase間データフロー型定義
type PhaseDataFlow = {
  Phase1: {
    input: UserInput;
    output: Intent;
  };
  Phase2: {
    input: Intent;
    output: Requirements;
  };
  Phase3: {
    input: Requirements;
    output: UserStory[];
  };
  Phase4: {
    input: UserStory[];
    output: ValidatedStories;
  };
  Phase5: {
    input: ValidatedStories;
    output: DomainModel;
  };
  Phase6: {
    input: DomainModel;
    output: GeneratedUI;
  };
};
```

### 🔄 品質保証プロセス

各フェーズで段階的に品質を向上：

1. **Phase 1-2**: 要求品質の確保
2. **Phase 3**: TDD強制開始
3. **Phase 4**: 多面的検証実施
4. **Phase 5**: アーキテクチャ品質保証
5. **Phase 6**: UI/UX品質とアクセシビリティ保証

### 📈 継続的改善

- **テレメトリ収集**: 各フェーズでの品質メトリクス収集
- **フィードバックループ**: 後続フェーズから前フェーズへの改善提案
- **学習機能**: 過去プロジェクトからのパターン学習と適用

---

## 🎯 まとめ

ae-frameworkの6フェーズアーキテクチャは、AI-Enhanced Developmentを実現する包括的なソリューションです：

### ✨ 特徴
- **段階的品質向上**: 各フェーズで品質を積み上げ
- **TDD強制**: Phase 3からの品質保証機能
- **完全自動化**: Phase 6でのUI自動生成
- **アクセシビリティファースト**: WCAG 2.1 AA準拠の実装
- **国際化対応**: 多言語サポート標準搭載

### 🚀 革新性
- **自然言語から完成品まで**: ユーザーの言葉から動作するUIまで完全自動化
- **品質保証組み込み**: 各段階での自動品質チェック
- **モダン技術スタック**: React 18 + Next.js 14の最新技術採用
- **開発効率**: 従来の開発サイクルを大幅短縮

**🎉 ae-frameworkで、次世代の開発体験を実現しましょう！**