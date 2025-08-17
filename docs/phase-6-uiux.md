# Phase 6: UI/UX & Frontend Delivery

> 包括的UI/UX設計・実装・品質保証フェーズ

**Parent EPIC**: [#53 Phase 6 (UI/UX & Frontend Delivery) 推進ロードマップ](https://github.com/itdojp/ae-framework/issues/53)  
**Related Issues**: [#52 Frontend Development Enhancement](https://github.com/itdojp/ae-framework/issues/52)

## 📋 概要

Phase 6は、Phase 3（ユーザーストーリー）とPhase 5（ドメインモデル）の成果を受けて、**実用的なUI/UXを自動生成・検証・承認**するフェーズです。

Design Systems統合、アクセシビリティ確保、パフォーマンス最適化、品質ゲートを通じて、**Production Ready**なフロントエンド成果物を提供します。

## 🔄 Phase境界定義

| Phase | スコープ | 入力 | 出力 | 品質ゲート |
|-------|---------|------|------|-----------|
| **Phase 6<br>UI/UX & Frontend Delivery** | • UI Component設計<br>• Design Token統合<br>• State Architecture設計<br>• Accessibility検証<br>• UI Quality Gates | • Phase 3: User Stories & AC<br>• Phase 5: Domain Model & Constraints | • Component Specifications<br>• Design Tokens<br>• State Architecture<br>• A11y/E2E/VR Reports<br>• CRUD UI Scaffolds | • A11y: 重大=0, 警告≤5<br>• E2E: 100% pass<br>• Coverage: ≥80%<br>• Web Vitals Budget |
| **Phase 7<br>Code Generation/Impl** | • Backend API生成<br>• Database Schema生成<br>• Full-Stack統合<br>• E2E Test生成 | • Phase 6: Component Specs<br>• Domain Models | • Full-Stack Application<br>• API Implementations<br>• Integration Tests | • API Response Time<br>• Database Performance<br>• Integration Coverage |
| **Phase 8<br>Operate** | • DevOps Pipeline設定<br>• Monitoring設定<br>• Security Policy適用<br>• 運用Governance | • Phase 7: Full-Stack App | • Production Deployment<br>• Monitoring Dashboard<br>• Security Reports<br>• Operations Runbook | • Security Scans<br>• Performance SLA<br>• Compliance Checks |

## 📥 Inputs (フェーズ入力)

### Phase 3 成果物
- **User Stories**: INVEST原則準拠のユーザーストーリー
- **Acceptance Criteria**: Given-When-Then形式の受入基準
- **Epic階層**: ユーザージャーニーとエピック構造
- **依存関係**: ストーリー間の依存関係マップ

### Phase 5 成果物  
- **Domain Model**: DDD準拠のエンティティとAggregateRoot
- **Bounded Context**: ドメイン境界とコンテキストマップ
- **Business Rules**: ビジネスルールと制約
- **Ubiquitous Language**: ドメイン共通言語辞書

### 外部リソース（オプション）
- **Design System**: Figma/Sketch design tokens
- **Component Library**: 既存UIコンポーネントライブラリ
- **Brand Guidelines**: ブランドガイドラインとスタイルガイド

## 📤 Outputs (フェーズ出力)

### 1. Design Tokens
```json
{
  "colors": {
    "primary": { "50": "#eff6ff", "500": "#3b82f6", "900": "#1e3a8a" },
    "semantic": { "success": "#10b981", "error": "#ef4444", "warning": "#f59e0b" }
  },
  "typography": {
    "fontFamily": { "sans": ["Inter", "system-ui"], "mono": ["Fira Code"] },
    "fontSize": { "xs": "0.75rem", "sm": "0.875rem", "base": "1rem", "xl": "1.25rem" }
  },
  "spacing": { "1": "0.25rem", "2": "0.5rem", "4": "1rem", "8": "2rem" },
  "borderRadius": { "none": "0", "sm": "0.125rem", "md": "0.375rem", "lg": "0.5rem" }
}
```

### 2. UI Component Specifications
```typescript
interface ComponentSpec {
  name: string;
  type: 'form' | 'list' | 'detail' | 'navigation' | 'layout';
  props: ComponentProps[];
  states: ComponentState[];
  accessibility: A11yRequirements;
  responsiveBreakpoints: BreakpointSpec[];
  businessRules: string[];
}

interface ComponentProps {
  name: string;
  type: string;
  required: boolean;
  validation: ValidationRule[];
  description: string;
}

interface ComponentState {
  name: 'loading' | 'error' | 'empty' | 'success';
  description: string;
  visualBehavior: string;
  userInteraction: string;
}
```

### 3. State Architecture
```typescript
interface StateArchitecture {
  pattern: 'redux' | 'zustand' | 'context' | 'swr' | 'tanstack-query';
  stores: StoreDefinition[];
  globalState: GlobalStateSchema;
  localState: LocalStateSchema[];
  sideEffects: SideEffectDefinition[];
}

interface StoreDefinition {
  name: string;
  domain: string; // Bounded Context from Phase 5
  entities: string[]; // Domain Entities from Phase 5
  actions: ActionDefinition[];
  selectors: SelectorDefinition[];
}
```

### 4. CRUD UI Scaffolds
```typescript
// Auto-generated from Domain Model + User Stories
interface CRUDScaffold {
  entity: string; // from Phase 5 Domain Model
  screens: {
    list: ComponentSpec;     // Entity List View
    detail: ComponentSpec;   // Entity Detail View  
    create: ComponentSpec;   // Entity Create Form
    edit: ComponentSpec;     // Entity Edit Form
  };
  routing: RouteDefinition[];
  validation: ValidationSchema;
  accessibility: A11yCompliance;
}
```

### 5. Storybook カタログ
- **Component Stories**: 全UIコンポーネントのStorybookストーリー
- **Design System Documentation**: Design Tokenの使用例とガイドライン
- **Interaction Testing**: ユーザーインタラクションのテストシナリオ
- **Accessibility Testing**: アクセシビリティテストと検証結果

### 6. Quality Reports
- **A11y Report**: アクセシビリティ検証結果（axe-core）
- **E2E Test Report**: End-to-Endテスト結果（Playwright）
- **Visual Regression Report**: ビジュアル回帰テスト結果（Chromatic）
- **Lighthouse Report**: パフォーマンス・SEO・PWA検証結果

## 🚪 Quality Gates

### v1 初期閾値（MVP段階）
```yaml
accessibility:
  critical_violations: 0        # Critical A11y violations must be 0
  warning_violations: ≤5        # Warning violations should be ≤5
  
end_to_end_testing:
  pass_rate: 100%              # All E2E tests must pass
  test_coverage: ≥80%          # Minimum 80% test coverage
  
performance:
  lighthouse_performance: ≥75   # Lighthouse Performance score ≥75
  lighthouse_accessibility: ≥95 # Lighthouse Accessibility score ≥95
  lighthouse_seo: ≥90          # Lighthouse SEO score ≥90
  
code_quality:
  test_coverage: ≥80%          # Unit test coverage ≥80%
  eslint_errors: 0             # ESLint errors must be 0
  typescript_errors: 0         # TypeScript compilation errors must be 0
```

### v2 監視目標（成熟段階）
```yaml
enhanced_quality:
  test_coverage: ≥90%          # Enhanced test coverage ≥90%
  a11y_score: ≥95%            # Enhanced accessibility score ≥95%
  performance_score: ≥90%      # Enhanced performance score ≥90%
  
efficiency_metrics:
  scaffold_generation_time: <30s  # UI scaffold generation <30 seconds
  e2e_test_execution_time: <5m    # E2E test suite execution <5 minutes
  build_time: <2m                 # Production build time <2 minutes
  
maintainability:
  component_complexity: <10       # Cyclomatic complexity per component <10
  css_unused_rate: <5%           # Unused CSS rate <5%
  design_token_coverage: ≥95%    # Design token usage coverage ≥95%
```

### 品質ゲート引き上げ戦略
1. **v1 (Initial)**: 基本品質の確保、開発フローの確立
2. **v1.5 (Intermediate)**: CI/CDパイプラインの安定化、メトリクス収集
3. **v2 (Mature)**: 高品質基準の達成、継続的改善の実現

## 📝 UI User Story テンプレート

### レスポンシブ対応ストーリー
```gherkin
Feature: Responsive Product Catalog
  As a [mobile/tablet/desktop] user
  I want to browse products optimally on my device
  So that I can have a seamless shopping experience

  UI Acceptance Criteria:
  - Renders correctly on 320px-1920px screen widths
  - Touch targets are ≥44px for mobile accessibility (WCAG 2.1 AA)
  - Images use responsive loading with srcset
  - Typography scales appropriately across breakpoints
  - Navigation transforms to mobile hamburger menu on <768px
  
  Technical Acceptance Criteria:
  - Uses CSS Grid/Flexbox for layout
  - Implements skeleton loading states
  - Supports keyboard navigation
  - Passes Lighthouse mobile performance audit
  - Maintains design token consistency
```

### アクセシビリティ重視ストーリー
```gherkin
Feature: Accessible Form Interaction
  As a user with assistive technology
  I want to complete forms independently
  So that I can access all application features

  UI Acceptance Criteria:
  - All form fields have descriptive labels (visible or aria-label)
  - Error messages are announced to screen readers
  - Focus indicators are clearly visible (3:1 contrast ratio)
  - Tab order follows logical reading sequence
  - Required fields are clearly marked and announced
  
  Technical Acceptance Criteria:
  - Form validation uses aria-describedby for error association
  - Live regions announce dynamic content changes
  - Supports high contrast mode
  - Passes axe-core automated accessibility testing
  - Keyboard-only navigation works without mouse
```

### State Management統合ストーリー
```gherkin
Feature: Optimistic UI Updates
  As a user performing data operations
  I want immediate visual feedback
  So that the application feels responsive

  UI Acceptance Criteria:
  - Create/Edit operations show optimistic updates
  - Loading states display skeleton screens or progress indicators
  - Error states provide clear recovery options
  - Success states confirm completed operations
  - Network failures are gracefully handled
  
  Technical Acceptance Criteria:
  - Uses TanStack Query for server state management
  - Implements optimistic updates with rollback on failure
  - Error boundaries catch and display React errors
  - Loading states are managed consistently across components
  - Network status is reflected in UI state
```

## 🏗️ Phase6TaskAdapter 仕様

### Interface Definition
```typescript
export interface Phase6TaskAdapter {
  generateComponentHierarchy(domainModel: DomainModel): ComponentTree;
  designStateArchitecture(userStories: UserStory[]): StateArchitecture;
  integrateDesignTokens(designSystemUrl: string): DesignTokens;
  validateAccessibility(componentSpecs: ComponentSpec[]): A11yReport;
}

export interface ComponentTree {
  entities: EntityComponent[];
  layouts: LayoutComponent[];
  forms: FormComponent[];
  navigation: NavigationComponent[];
  feedback: FeedbackComponent[];
}

export interface StateArchitecture {
  pattern: StateManagementPattern;
  globalStores: StoreDefinition[];
  localStates: LocalStateDefinition[];
  dataFetching: DataFetchingStrategy;
  caching: CacheStrategy;
}

export interface DesignTokens {
  colors: ColorTokens;
  typography: TypographyTokens;
  spacing: SpacingTokens;
  borders: BorderTokens;
  shadows: ShadowTokens;
  breakpoints: BreakpointTokens;
}

export interface A11yReport {
  summary: A11ySummary;
  violations: A11yViolation[];
  recommendations: A11yRecommendation[];
  compliance: WCAGCompliance;
}
```

### Implementation Skeleton
```typescript
// src/agents/phase6-ui-task-adapter.ts
import { FormalAgent, FormalAgentConfig } from './formal-agent.js';
import { TaskRequest, TaskResponse } from './task-types.js';

export class Phase6UITaskAdapter implements Phase6TaskAdapter {
  private agent: FormalAgent;

  constructor() {
    const config: FormalAgentConfig = {
      outputFormat: 'react-component',
      validationLevel: 'comprehensive',
      generateDiagrams: true,
      enableModelChecking: true,
    };
    this.agent = new FormalAgent(config);
  }

  async handleUITask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    
    switch (taskType) {
      case 'generate-components':
        return this.handleComponentGeneration(request);
      case 'design-state':
        return this.handleStateArchitectureDesign(request);
      case 'integrate-design-tokens':
        return this.handleDesignTokenIntegration(request);
      case 'validate-accessibility':
        return this.handleAccessibilityValidation(request);
      default:
        return this.handleGenericUIProcessing(request);
    }
  }

  async generateComponentHierarchy(domainModel: DomainModel): Promise<ComponentTree> {
    // Implementation: Convert domain entities to UI component specifications
    // - Analyze domain aggregates and entities
    // - Generate CRUD components for each entity
    // - Create navigation and layout components
    // - Design form components with validation
    // - Include feedback and error handling components
  }

  async designStateArchitecture(userStories: UserStory[]): Promise<StateArchitecture> {
    // Implementation: Analyze user stories to design state management
    // - Identify state patterns from user interactions
    // - Design global vs local state boundaries
    // - Plan data fetching and caching strategies
    // - Define optimistic update patterns
    // - Integrate with domain model constraints
  }

  async integrateDesignTokens(designSystemUrl: string): Promise<DesignTokens> {
    // Implementation: Extract and integrate design tokens
    // - Fetch design tokens from Figma API or design system
    // - Convert to standard format (Style Dictionary compatible)
    // - Validate token consistency and completeness
    // - Generate CSS custom properties and TypeScript types
    // - Create documentation for token usage
  }

  async validateAccessibility(componentSpecs: ComponentSpec[]): Promise<A11yReport> {
    // Implementation: Comprehensive accessibility validation
    // - Static analysis of component specifications
    // - WCAG 2.1 AA compliance checking
    // - Color contrast ratio validation
    // - Keyboard navigation verification
    // - Screen reader compatibility assessment
    // - Generate remediation recommendations
  }
}

// Export for Claude Code Task tool integration
export const createPhase6UITaskHandler = () => {
  const adapter = new Phase6UITaskAdapter();
  return {
    handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
      return adapter.handleUITask(request);
    },
  };
};
```

## 📁 ディレクトリ構成

```
src/
├── agents/
│   ├── phase6-ui-task-adapter.ts        # Phase 6 Task Adapter implementation
│   ├── task-types.ts                    # Shared types with UI-specific extensions
│   └── ...existing adapters...
├── ui/                                  # UI/UX generation output
│   ├── components/
│   │   ├── generated/                   # Auto-generated components
│   │   │   ├── {Entity}List.tsx
│   │   │   ├── {Entity}Form.tsx
│   │   │   ├── {Entity}Detail.tsx
│   │   │   └── ...
│   │   ├── base/                        # Base reusable components
│   │   │   ├── Button.tsx
│   │   │   ├── Input.tsx
│   │   │   ├── Modal.tsx
│   │   │   └── ...
│   │   └── layout/                      # Layout components
│   │       ├── Header.tsx
│   │       ├── Sidebar.tsx
│   │       ├── Footer.tsx
│   │       └── MainLayout.tsx
│   ├── hooks/                           # Custom React hooks
│   │   ├── useEntity.ts
│   │   ├── useFormValidation.ts
│   │   └── useAccessibility.ts
│   ├── stores/                          # State management
│   │   ├── {entity}Store.ts
│   │   ├── globalStore.ts
│   │   └── ...
│   ├── styles/                          # Styling and design tokens
│   │   ├── tokens.css                   # CSS custom properties from design tokens
│   │   ├── globals.css                  # Global styles
│   │   └── components.css               # Component-specific styles
│   └── types/                           # UI-specific TypeScript types
│       ├── components.ts
│       ├── state.ts
│       └── design-tokens.ts
├── cli/
│   └── index.ts                         # Extended with ui-scaffold commands
└── ...

policies/                                # OPA policies for UI governance
├── ui/
│   ├── component-standards.rego         # Component naming and structure standards
│   ├── accessibility-rules.rego         # Accessibility compliance rules
│   ├── design-token-compliance.rego     # Design token usage validation
│   └── performance-budgets.rego         # Performance budget enforcement
└── ...

.github/
└── workflows/
    ├── phase6-validation.yml            # Phase 6 CI/CD pipeline
    └── ...

scripts/                                 # Quality gate validation scripts
├── check-a11y-threshold.js             # Accessibility threshold validation
├── check-opa-compliance.js             # OPA policy compliance check
├── generate-a11y-report.js             # Accessibility report generation
├── generate-visual-report.js           # Visual regression report generation
└── ...

examples/
└── inventory/                           # Phase 6 demonstration example
    ├── domain-model.json                # Domain model from Phase 5
    ├── user-stories.json                # User stories from Phase 3
    ├── generated-ui/                    # Generated UI components
    └── README.md                        # End-to-end walkthrough
```

## 🔧 命名規則

### Component命名
- **EntityComponents**: `{Entity}List`, `{Entity}Form`, `{Entity}Detail`
- **BaseComponents**: `Button`, `Input`, `Modal`, `Card`, `Badge`
- **LayoutComponents**: `Header`, `Sidebar`, `Footer`, `MainLayout`
- **FeatureComponents**: `UserProfile`, `ProductCatalog`, `ShoppingCart`

### Method命名
- **Task Adapter**: `generateComponentHierarchy`, `designStateArchitecture`, `integrateDesignTokens`, `validateAccessibility`
- **State Management**: `useEntityStore`, `useFormState`, `useApiQuery`
- **Validation**: `validateA11yCompliance`, `checkDesignTokenUsage`, `enforcePerformanceBudget`

### File命名
- **Generated Files**: `{entity}.generated.tsx`, `{entity}.stories.generated.ts`
- **Configuration**: `phase6.config.ts`, `design-tokens.config.js`, `a11y.config.ts`
- **Reports**: `a11y-report.json`, `visual-regression-report.json`, `lighthouse-report.json`

## 🚀 実装優先順位

### Phase 6.1: Foundation（基盤確立）
1. **Phase6TaskAdapter骨格実装**
2. **基本的なComponent生成**
3. **Design Token統合（最小実装）**
4. **A11y基本検証**

### Phase 6.2: Quality Gates（品質ゲート）
1. **CI/CD パイプライン統合**
2. **OPA Policy実装**
3. **Lighthouse CI統合**
4. **Visual Regression Testing**

### Phase 6.3: Advanced Features（高度機能）
1. **State Management自動設計**
2. **Figma API統合**
3. **Performance最適化**
4. **Enhanced A11y Testing**

### Phase 6.4: Production Ready（本格運用）
1. **Comprehensive Example Application**
2. **Documentation完備**
3. **メトリクス監視ダッシュボード**
4. **継続的改善プロセス**

## 📚 関連ドキュメント

- **[Phase 2: Natural Language Requirements](./PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md)** - 要件分析フェーズ
- **[Phase 3: User Stories Creation](./PHASE-3-USER-STORIES-CREATION.md)** - ユーザーストーリー生成フェーズ  
- **[Phase 5: Domain Modeling](./PHASE-5-DOMAIN-MODELING.md)** - ドメインモデリングフェーズ
- **[Claude Code自動実行ガイド](./CLAUDE-CODE-AUTOMATION-GUIDE.md)** - 自動実行手順
- **[Frontend Development Enhancement (#52)](https://github.com/itdojp/ae-framework/issues/52)** - フロントエンド強化提案

## 🎯 Success Metrics

### Technical Success
- **Quality Gates**: v1閾値を100%満たす
- **Performance**: Lighthouse Performance Score ≥75
- **Accessibility**: WCAG 2.1 AA準拠（重大違反0）
- **Maintainability**: Component複雑度 <10

### Business Success  
- **Development Efficiency**: UI scaffold生成時間 <30秒
- **Quality Assurance**: 自動品質検証による手戻り削減
- **Team Productivity**: Design-Development間のハンドオフ効率化
- **User Experience**: Production ReadyなUI/UXの自動生成

### Process Success
- **CI/CD Integration**: 品質ゲートの自動実行とレポート生成
- **Documentation**: 実装チームが独立して利用可能な文書化
- **Scalability**: 小規模から大規模プロジェクトまでの対応
- **Continuous Improvement**: メトリクス基盤による継続的品質向上

---

**Phase 6: UI/UX & Frontend Delivery** - Production Ready フロントエンドの自動生成と品質保証 🎨

*最終更新: 2025年8月*