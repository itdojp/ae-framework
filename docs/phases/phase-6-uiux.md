---
docRole: ssot
lastVerified: 2026-06-02
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 6: UI/UX & Frontend Delivery

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Phase 6 turns user stories and domain models into production‑ready UI/UX via automated scaffolding, design system integration, a11y/perf quality gates, and telemetry. Inputs: Phase 3/5 outputs. Outputs: components, tokens, state architecture, and reports.

> Status note (2026-02-18): adapter thresholds in `.github/workflows/adapter-thresholds.yml` run only when the PR includes `run-adapters`. Within those runs, a11y/perf/lighthouse are report-only by default and become blocking only with `enforce-*` labels. Treat threshold values in this document as targets unless explicitly tied to a specific workflow policy.
> Security note (2026-06-02): `.github/workflows/phase6-validation.yml` runs pull-request Lighthouse collection without `LHCI_GITHUB_APP_TOKEN`; token-backed upload/status posting must stay in a trusted-ref follow-up lane, not in PR-controlled validation code.

## English (Detailed)

### Scope
- UI component design and scaffolding
- Design token integration
- State architecture (forms, data fetching, server state)
- Accessibility verification and quality gates
- E2E/visual/coverage/performance reports

### Inputs / Outputs
- Inputs: Phase 3 (User Stories + AC), Phase 5 (Domain Model & Constraints)
- Outputs: Component specs, tokens, state architecture, a11y/E2E/visual reports, CRUD scaffolds

### Quality Gates
- Accessibility: critical=0, warnings ≤ 5
- E2E: 100% pass
- Coverage: ≥ 80%
- Web Vitals budget maintained

> Implementation note: default CI does not always enforce every gate above. Refer to `docs/quality/adapter-thresholds.md` and workflow files for current enforcement scope.

### A11y Checklist (quick)
- Landmarks: main/nav/footer/accessible headings present
- Labels: form controls have programmatic labels
- Focus: visible focus ring; no focus traps
- Color: contrast AA (4.5:1); avoid color-only meaning
- ARIA: use sparingly; roles/name/value correct
- Keyboard: full flow usable with keyboard only

### Performance Hints
- Code split routes and heavy components; avoid blocking renders
- Use `next/image` with proper sizes; lazy-load below the fold
- Cache fetches with SWR/TanStack Query; prefer server components for data
- Minimize re-renders: memoize lists; stable keys; avoid inline objects in props
- Lighthouse CI budget: LCP ≤ 2.5s, TBT ≤ 200ms, CLS ≤ 0.1

### Suggested Thresholds
- Coverage ≥ 80%
- A11y score ≥ 95%
- Perf (Lighthouse) ≥ 75%

### Operational Hints
```text
# Scaffold components/state/tokens
ae-framework ui-scaffold --components
ae-framework ui-scaffold --state
ae-framework ui-scaffold --tokens

# Run E2E (apps/web)
pnpm --filter @ae-framework/web exec playwright test --reporter=list

# Optional: Lighthouse CI (page URL env)
lhci autorun --upload.target=temporary-public-storage
```

> 包括的UI/UX設計・実装・品質保証フェーズ

**Parent EPIC**: [#53 Phase 6 (UI/UX & Frontend Delivery) 推進ロードマップ](https://github.com/itdojp/ae-framework/issues/53)  
**Related Issues**: [#52 Frontend Development Enhancement](https://github.com/itdojp/ae-framework/issues/52)

## 📋 概要

Phase 6は、Phase 3（ユーザーストーリー）とPhase 5（ドメインモデル）の成果を受けて、**実用的なUI/UXを自動生成・検証・承認**するフェーズです。

> 現行ステータス（2026-02-18）: `.github/workflows/adapter-thresholds.yml` のアダプタしきい値は PR に `run-adapters` ラベルがある場合のみ実行されます。実行時は a11y/perf/lighthouse が既定 report-only で、`enforce-*` ラベル付与時のみブロッキングです。本書のしきい値は、個別workflowで明示しない限り目標値として扱ってください。
> セキュリティ注記（2026-06-02）: `.github/workflows/phase6-validation.yml` の pull-request Lighthouse collection は `LHCI_GITHUB_APP_TOKEN` を使用しません。token-backed upload/status posting は PR-controlled validation code ではなく trusted-ref follow-up lane に限定してください。

Design Systems統合、アクセシビリティ確保、パフォーマンス最適化、品質ゲートを通じて、**Production Ready**なフロントエンド成果物を提供します。

## 🔄 Phase境界定義

### Phase 6: UI/UX & Frontend Delivery

**スコープ**
- UI Component設計
- Design Token統合
- State Architecture設計
- Accessibility検証
- UI Quality Gates

**入力**
- Phase 3: User Stories & AC
- Phase 5: Domain Model & Constraints

**出力**
- Component Specifications
- Design Tokens
- State Architecture
- Accessibility/E2E/VR Reports
- CRUD UI Scaffolds

**品質ゲート**
- Accessibility: 重大=0, 警告≤5
- E2E: 100% pass
- Coverage: ≥80%
- Web Vitals Budget

> 実装注記: 上記を常時すべて強制しているわけではありません。現在の強制範囲は `docs/quality/adapter-thresholds.md` と各workflow定義を参照してください。

### A11y チェックリスト（簡易）
- ランドマーク: main/nav/footer/見出しの構造化
- ラベル: フォーム要素にプログラム的ラベルを付与
- フォーカス: 可視フォーカスリング、トラップ無し
- 色: コントラストAA(4.5:1)、色のみの意味付けを避ける
- ARIA: 最小限の使用。roles/name/value が正しいこと
- キーボード: キーボードのみで一連の操作が可能

### パフォーマンスヒント
- ルート/重量コンポーネントの分割。初期レンダを阻害しない
- `next/image` を適切なサイズで使用。視界外は遅延読込
- SWR/TanStack Query でフェッチ結果をキャッシュ。データは Server Components 優先
- 再レンダ最小化: リストは memo、安定キー、props のインラインオブジェクト回避
- Lighthouse 目安: LCP ≤ 2.5s, TBT ≤ 200ms, CLS ≤ 0.1

### 推奨しきい値
- Coverage ≥ 80%
- A11y スコア ≥ 95%
- Perf（Lighthouse）≥ 75%

### 運用ヒント（コマンド）
```text
# コンポーネント/状態/トークンのスキャフォールド
ae-framework ui-scaffold --components
ae-framework ui-scaffold --state
ae-framework ui-scaffold --tokens

# 実装済みの semantic UI E2E lane
pnpm run ui-e2e:semantic

# 従来の Playwright 実験系
pnpm --filter @ae-framework/web exec playwright test --reporter=list

# 任意: Lighthouse CI（ページURLを環境で指定）
lhci autorun --upload.target=temporary-public-storage
```
 
### Repository Layout (excerpt)
```
ae-framework/
├─ packages/
│  ├─ design-tokens/
│  └─ ui/
├─ apps/web/
│  ├─ app/{entity}/page.tsx            # Index
│  ├─ app/{entity}/[id]/page.tsx       # Show
│  ├─ messages/{ja,en}.json            # i18n
│  └─ __e2e__/{entity}.spec.ts         # E2E
└─ templates/ui/                       # Handlebars
```

### Technology
- Framework: Next.js 14 App Router
- UI: Radix UI + Tailwind CSS + shadcn/ui
- Forms/Validation: React Hook Form + Zod
- State: TanStack Query 5
- Testing: Playwright E2E + Storybook + Vitest
- i18n: next-intl (ja/en)
- A11y: WCAG 2.1 AA + eslint-plugin-jsx-a11y
- Telemetry: OpenTelemetry metrics for quality

### Typical Flow
1) Generate components from Phase State
2) Run a11y/E2E/coverage/performance gates
3) Inspect telemetry and reports; iterate tokens/state/config

### Telemetry & Gate Examples
- Telemetry: OTel metrics emitted with scaffold time, E2E duration, coverage
- Pass examples:
  - Coverage: 84% (>=80) — PASS
  - A11y: 96% (>=95) — PASS
  - Performance: 78% (>=75) — PASS
- Fail examples:
  - Coverage: 76% (<80) — FAIL → add tests for critical flows (forms, lists)
  - A11y: 92% (<95) — FAIL → add alt/aria, increase contrast

### Observability Checklist
- Export OTel to local collector (`OTEL_EXPORTER_OTLP_ENDPOINT`) in development
- Correlate E2E runs with UI scaffold time to spot regressions
- Track component complexity (targets <10) and unused CSS (<5%)

### Gate Tuning Notes
- Raise thresholds gradually after stabilizing: Coverage 80→85, A11y 95→97, Perf 75→78
- Keep a short CHANGELOG note in PRs when adjusting thresholds, with one-line rationale

### Suggested Thresholds (starter)
```
Coverage: 80%
A11y:     95%
Perf:     75%
```

### A11y Checklist (quick)
- All images have meaningful `alt` (or `role="presentation"` when purely decorative)
- Form controls have associated labels (`<label for>` or `aria-label`)
- Visible keyboard focus ring on interactive elements
- Sufficient color contrast for text and UI components (WCAG AA)
- Proper landmarks/roles (header/main/nav) to aid navigation

### Fix Recipes (quick)
- Coverage: add tests for form validation, list filters, and error states
- A11y: ensure `alt`/`aria-*`, improve contrast tokens, visible focus rings
- Perf: optimize images (`next/image`, lazy), reduce CSS/JS, remove unused deps

### Lighthouse-specific Hints
- LCP: optimize hero image, preconnect to origins, reduce render-blocking CSS
- CLS: reserve space for images/media, avoid layout-shifting banners
- TBT: code-split heavy modules, reduce long tasks, defer non-critical work

### Performance Recipes (quick)
- Fonts: preload critical fonts, use `font-display: swap`, subset where possible
- Preconnect/Preload: `rel=preconnect` for third-party origins; preload hero image if needed
- Code splitting: lazy-load non-critical components and routes
- Images: use modern formats (WebP/AVIF), provide srcset/sizes, compress aggressively
- Critical CSS: inline only truly critical CSS; defer non-critical styles
- Font subset: generate locale-specific subsets to reduce TTF size

### Font Preload Example
```html
<link rel="preload" href="https://example.com/fonts/Inter-roman.var.woff2" as="font" type="font/woff2" crossorigin>
<style>
  @font-face {
    font-family: Inter;
    src: url('https://example.com/fonts/Inter-roman.var.woff2') format('woff2');
    font-display: swap;
  }
</style>
```

---

### Phase 7: Code Generation/Impl

**スコープ**
- Backend API生成
- Database Schema生成
- Full-Stack統合
- E2E Test生成

**入力**
- Phase 6: Component Specs
- Domain Models

**出力**
- Full-Stack Application
- API Implementations
- Integration Tests

**品質ゲート**
- API Response Time
- Database Performance
- Integration Coverage

---

### Phase 8: Operate

**スコープ**
- DevOps Pipeline設定
- Monitoring設定
- Security Policy適用
- 運用Governance

**入力**
- Phase 7: Full-Stack App

**出力**
- Production Deployment
- Monitoring Dashboard
- Security Reports
- Operations Runbook

**品質ゲート**
- Security Scans
- Performance SLA
- Compliance Checks

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
```text
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
```text
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
```text
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
```text
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
```text
accessibility:
  critical_violations: 0        # Critical Accessibility violations must be 0
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
```text
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

## 🏗️ Phase6TaskAdapter 仕様（将来拡張案）

> 重要: この節の `Phase6TaskAdapter` / `Phase6UITaskAdapter` は設計スケッチです。  
> 現在の実装パスは `src/cli/index.ts` の `ui-scaffold` コマンドと  
> `src/generators/ui-scaffold-generator.ts`（テンプレート駆動生成）です。

### 現行実装マッピング（2026-02-18）

- CLI: `src/cli/index.ts` (`ae-framework ui-scaffold`)
- Alias: `src/cli/ae-ui-alias.ts` (`ae-ui scaffold`)
- Generator: `src/generators/ui-scaffold-generator.ts`
- Templates: `templates/ui/*.template`（現在 7 テンプレート）
- CI workflow: `.github/workflows/phase6-validation.yml`

### Interface Definition
```text
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

### Implementation Skeleton (proposal)
```text
// src/agents/phase6-ui-task-adapter.ts
// NOTE: This is a future-phase proposal and not the current production path.
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

## 📁 ディレクトリ構成（目標案）

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
- **[Claude Code自動実行ガイド](../guides/CLAUDE-CODE-AUTOMATION-GUIDE.md)** - 自動実行手順
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
