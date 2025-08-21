# AE Framework Development Instructions Guide

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Phase 6 Implementation Edition: Concrete instruction methods for using ae-framework in actual development projects**

### 📋 Overview

This guide explains **specific instruction methods** for actual development using ae-framework with Phase 6 UI/UX & Frontend Delivery implementation. From natural language instructions in Claude Code to CLI commands, explained with practical scenario-based examples.

#### 🎯 Target Audience
- **Project Managers**: How to communicate requirements effectively
- **Developers**: Efficient implementation instruction techniques
- **Quality Assurance**: Instruction methods for high-quality deliverables
- **UI/UX Designers**: Design system integration instruction methods

## 🤖 Development Instructions in Claude Code

### Basic Development Request Patterns

#### 1. Comprehensive Project Request

```
"Please create an e-commerce product management system using ae-framework.

Requirements:
- Product listing, detail, create, edit functionality
- Category management
- Inventory management
- Administrator dashboard
- Japanese/English support
- Accessibility compliance

Technical Requirements:
- React + Next.js 14
- TypeScript strict mode
- Responsive design
- Test coverage 80%+
- OpenTelemetry telemetry monitoring

Quality Requirements:
- WCAG 2.1 AA compliance
- Performance score 75%+
- A11y score 95%+"
```

**Expected Automatic Execution Flow:**
```bash
📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ecommerce-management v1.0.0
   Environment: development

✅ Phase 1-5 Complete - Analysis, Requirements, Stories, Validation, Domain Model
✅ Generated 32 files for 5/5 entities

📊 Quality Metrics:
  • Test Coverage: 87% (threshold: 80%) ✅
  • A11y Score: 96% (threshold: 95%) ✅  
  • Performance Score: 78% (threshold: 75%) ✅
  • i18n Coverage: 100% (ja/en) ✅

🎨 Generated Components:
  • React Components: 20 files
  • Next.js Pages: 15 files  
  • Storybook Stories: 5 files
  • E2E Tests: 10 files
  • Database Migrations: 5 files
```

#### 2. Stepwise Development Instructions

```
Phase 1: "Please start with requirements analysis"
→ Intent Agent structures and analyzes requirements

Phase 2: "Please convert requirements to formal specifications"  
→ Natural Language Agent generates structured requirements

Phase 3: "Please generate user stories and tests"
→ User Stories Agent creates stories and tests

Phase 4: "Please verify requirements and story consistency"
→ Validation Agent performs quality verification

Phase 5: "Please design the domain model"
→ Domain Modeling Agent designs entities and relationships

Phase 6: "Please generate UI components"
→ UI Task Adapter auto-generates React components
```

## 🎯 Scenario-Based Instruction Examples

### Scenario 1: New Project Development

```
"I want to create an inventory management system with ae-framework.

【Functional Requirements】
- Product master management (name, price, category, stock quantity)
- Stock movement management (inbound, outbound, adjustments)
- Order management (reorder point management, automatic order proposals)
- Reporting functionality (inventory list, sales analysis)

【Non-functional Requirements】
- Response time: Within 3 seconds
- Concurrent users: 100 people
- Availability: 99.9%
- Database: PostgreSQL

【UI Requirements】
- Modern design (Material Design 3 style)
- Mobile responsive design
- Japanese UI
- WCAG 2.1 AA compliance

【Monitoring Requirements】
- Please enable quality monitoring with OpenTelemetry telemetry
- Core Web Vitals monitoring
- Custom business metrics tracking"
```

**Expected Output:**
```bash
📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: inventory-management v1.0.0
   Environment: development

✅ Phase 1-5 Complete - Analysis, Requirements, Stories, Validation, Domain Model
✅ Generated 28 files for 4/4 entities (Product, Stock, Order, Report)

📊 Quality Metrics:
  • Test Coverage: 94% (threshold: 80%) ✅
  • A11y Score: 97% (threshold: 95%) ✅  
  • Performance Score: 82% (threshold: 75%) ✅
  • i18n Coverage: 100% (ja) ✅

🎨 Generated Components:
  • React Components: 16 files
  • Next.js Pages: 12 files  
  • Storybook Stories: 4 files
  • E2E Tests: 8 files
  • Database Migrations: 4 files

🌐 Material Design 3 integration: ✅
📱 Responsive design: ✅
🔍 PostgreSQL schema: ✅
```

### Scenario 2: Adding Features to Existing Project

```
"Please add review functionality to an existing e-commerce site.

【Additional Requirements】
- Product review posting and display
- 5-star rating system
- Reviews with images
- Review approval functionality (administrator)
- Review search and filtering

【Constraints】
- Extend existing Product entity
- Minimize impact scope
- Ensure existing tests don't break
- Enable staged deployment design

【Quality Requirements】
- No impact on existing functionality
- New feature test coverage 90%+
- Review posting performance optimization"
```

**Expected Output:**
```bash
🔍 Impact Analysis Complete:
  • Modified Entities: Product (added review-related fields)
  • New Entities: Review, ReviewImage
  • Affected Components: ProductCard, ProductDetail
  • Database Changes: 2 new tables, 1 FK constraint

📊 Risk Assessment: LOW
  • Existing tests: 94% remain unchanged
  • Breaking changes: None detected
  • Migration strategy: Safe incremental deployment

✅ Generated Review System:
  • Review Components: 6 files
  • API Endpoints: 4 files
  • Database Migrations: 2 files
  • Tests: 12 files (96% coverage)

🚀 Deployment Strategy:
  • Phase 1: Database migration (backward compatible)
  • Phase 2: API endpoints deployment
  • Phase 3: UI components activation
  • Phase 4: Feature flag enabled rollout
```

### Scenario 3: Specific Component Generation

```
"Please generate only a product card component.

【Design Requirements】
- Display product name, price, image, rating
- Add to cart button
- Favorite functionality
- Hover effects
- Responsive design

【Technical Requirements】
- TypeScript strict mode
- Include Storybook stories
- Include Playwright tests
- Accessibility compliance

【Entity Definition】
name: string (required)
price: number (required)
image: string (optional)
rating: number (0-5, optional)
inStock: boolean (required)
category: string (optional)"
```

**CLI Instruction:**
```bash
ae-framework ui-scaffold --entity=Product --components --storybook --tests
```

**Expected Output:**
```bash
✅ Generated ProductCard Component:
  • packages/ui/src/product-card.tsx
  • apps/storybook/stories/ProductCard.stories.tsx
  • apps/web/__tests__/ProductCard.test.tsx
  • apps/web/__e2e__/product-card.spec.ts

📊 Component Quality:
  • TypeScript compliance: ✅
  • A11y compliance: ✅ (WCAG 2.1 AA)
  • Responsive design: ✅
  • Test coverage: 95%
```

## 🛠️ Development Stage-Specific Instructions

### Phase 1-5: Planning & Design Stage

#### Requirements Analysis Only
```
"Please execute only requirements analysis. I want to review the results before proceeding."
```

**CLI Instruction:**
```bash
ae-framework intent --analyze --sources="requirements.md"
```

#### User Story Generation
```
"Please generate user stories from requirements. Organize by epic."
```

**CLI Instruction:**
```bash
ae-framework user-stories --generate --organize-epics
```

#### Domain Model Creation
```
"Please create domain model from user stories. Clarify relationships between entities."
```

**CLI Instruction:**
```bash
ae-framework domain-model --entities --relationships
```

### Phase 6: UI/UX Implementation Stage

#### Basic UI Component Generation
```
"Please generate basic UI components"
```

**CLI Instruction:**
```bash
ae-framework ui-scaffold --components
```

#### Storybook Integration
```
"Please generate including Storybook documentation"
```

**CLI Instruction:**
```bash
ae-framework ui-scaffold --components --storybook
```

#### Multi-language Support
```
"Please configure multi-language support (Japanese, English, Korean)"
```

**CLI Instruction:**
```bash
ae-framework ui-scaffold --components --i18n --locales=ja,en,ko
```

#### Full Feature Integration
```
"Please generate everything (components, Storybook, i18n, A11y)"
```

**CLI Instruction:**
```bash
ae-framework ui-scaffold --components --storybook --i18n --a11y
```

## 🎨 UI/UX Specialized Instructions

### Design System Integration

```
"Please create a product catalog with Material Design 3 style design system.

【Design Specifications】
- Google Material Design 3 compliance
- Primary color: #1976d2 (blue)
- Secondary color: #f57c00 (orange)  
- Typography: Roboto
- Border radius: 8px
- Shadow: elevation 2

【Component Requirements】
- ProductGrid (product listing grid)
- ProductCard (product card)
- SearchBar (search bar)
- FilterChips (filter chips)
- CategoryNav (category navigation)

【Responsive Requirements】
- Desktop: 4-column grid
- Tablet: 3-column grid
- Mobile: 2-column grid"
```

### Accessibility Focus

```
"Please create a product search screen that's accessible to visually impaired users.

【A11y Requirements】
- WCAG 2.1 AAA compliance (highest level)
- Complete screen reader support
- Keyboard navigation
- High contrast display support
- Voice reading optimization
- Focus management optimization

【Additional Features】
- Voice search functionality
- Keyboard shortcuts
- Skip links
- ARIA live regions
- Custom focus indicators"
```

### Mobile-First Design

```
"Please design an e-commerce app with mobile-first approach.

【Mobile Optimization】
- Touch-friendly UI sizes (44px+)
- Swipe gesture support
- Progressive Web App features
- Offline support
- Push notifications

【Performance Requirements】
- First Contentful Paint < 2 seconds
- Largest Contentful Paint < 3 seconds  
- Cumulative Layout Shift < 0.1
- Image lazy loading
- Bundle size optimization"
```

## 📊 Quality & Monitoring Focused Instructions

### Telemetry Monitoring Focus

```
"Please create a dashboard focused on performance monitoring.

【Monitoring Requirements】
- Real-time metrics display
- Response time monitoring
- Error rate tracking
- User behavior analysis
- A/B testing functionality

【OpenTelemetry Telemetry Monitoring Items】
- Core Web Vitals (LCP, FID, CLS)
- Custom business metrics
- User journey tracking
- Conversion rates
- API response times
- Database query performance

【Alert Configuration】
- Automatic alerts on performance degradation
- Notifications on error rate threshold exceeded
- Usability issue detection"
```

**Expected Output:**
```bash
📊 OpenTelemetry Dashboard Generated:
  • Real-time metrics display
  • Performance monitoring widgets  
  • Custom business metrics integration
  • Alert configuration: ✅

🔔 Alert Thresholds:
  • Response time > 3s: WARNING
  • Error rate > 5%: CRITICAL
  • A11y score < 95%: WARNING
  • Performance score < 75%: CRITICAL
```

### High Quality Requirements

```
"Please create a customer management system with enterprise-level quality.

【Quality Requirements】
- Test coverage: 95%+
- TypeScript strict mode
- ESLint errors: 0
- Performance score: 90%+  
- A11y score: 98%+
- Security scan: Clean

【Security Requirements】
- API Rate Limiting
- CSRF Protection  
- XSS Prevention
- SQL Injection protection
- Input value sanitization
- Enhanced session management

【Code Quality Requirements】
- Clean Architecture application
- SOLID principles compliance
- DRY principle application
- Comprehensive documentation
- Code review checklist"
```

## 🔧 Customization & Extension Instructions

### Design Token Customization

```
"Please change design tokens to company brand colors.

【Brand Specifications】
- Primary: #2E86AB (corporate blue)
- Secondary: #A23B72 (corporate pink)  
- Accent: #F18F01 (corporate orange)
- Neutral: #C73E1D (corporate red)

【Typography】
- Headline: 'Noto Sans JP', sans-serif
- Body: 'Roboto', sans-serif
- Code: 'Fira Code', monospace

【Spacing】
- Base unit: 8px
- Between components: 16px
- Between sections: 32px"
```

### Multi-language Support Extension

```
"Please add Korean and Chinese (Simplified/Traditional) to multi-language support.

【Supported Languages】
- Japanese (ja): Default
- English (en): Secondary
- Korean (ko): New addition
- Chinese Simplified (zh-CN): New addition
- Chinese Traditional (zh-TW): New addition

【Translation Requirements】
- Product/category information translation
- UI text translation
- Error message translation
- Date/currency format localization
- RTL support (future Arabic support)

【Technical Requirements】
- next-intl configuration extension
- Translation key systematization
- Automatic translation gap detection"
```

### Custom Component Addition

```
"Please add custom chart components to existing UI library.

【Chart Requirements】
- Bar chart
- Line chart
- Pie chart
- Donut chart
- Area chart

【Technical Specifications】
- Chart.js or D3.js based
- Complete TypeScript support
- Responsive design
- Accessible (screen reader support)
- Custom theme support

【Storybook Integration】
- Stories for each chart type
- Interactive configuration examples
- Data format examples"
```

## 🚨 Troubleshooting Instructions

### Stepwise Verification Instructions

```
"I want to review Phase 1 requirements analysis results before proceeding"
→ Review each phase results before next stage

"Please verify if the domain model is correct"
→ Check design validity

"Please review the generated components"
→ Verify code quality
```

### Quality Issue Fix Instructions

```
"Build errors are occurring. Please fix them"
→ Resolve TypeScript type errors, dependency issues

"Accessibility tests are failing. Please fix to comply with WCAG 2.1 AA"
→ Identify and fix A11y issues

"Performance is below threshold. Please optimize"
→ Execute bundle size, image optimization, code splitting

"Test coverage is below 80%"
→ Add missing test cases
```

### Debug & Investigation Instructions

```
"Please investigate why OpenTelemetry telemetry is not displaying"
→ Configuration check, log analysis

"Please identify the cause of slow response times"
→ Performance analysis, bottleneck investigation

"Please resolve UI component display issues"
→ CSS, layout, browser compatibility check
```

## 🎯 Tips for Effective Instructions

### 1. Clear Requirement Specification

```
❌ Bad example:
"Create a product management screen"

✅ Good example:
"Create a product management screen. Need list display (with pagination), detail display, create/edit forms, delete confirmation dialog. Responsive design with accessibility compliance"
```

### 2. Explicit Technical Constraints

```
❌ Bad example:
"Please use a database"

✅ Good example:
"Use PostgreSQL 14 with Prisma ORM for schema management, migrations implemented in TypeScript"
```

### 3. Concrete Quality Standards

```
❌ Bad example:
"Make it high quality"

✅ Good example:
"Test coverage 90%+, 0 ESLint errors, WCAG 2.1 AA compliance, Lighthouse performance score 85%+"
```

### 4. Stepwise Verification Instructions

```
✅ Recommended pattern:
"Review requirements analysis results before proceeding to next phase"
"Verify domain model entity relationships are correct"  
"Check quality of generated UI components"
```

## 🔗 Related Documentation

- **[Phase 6 UI/UX Getting Started](./PHASE-6-GETTING-STARTED.md)** - Phase 6 dedicated quick start
- **[Claude Code Task Tool Integration](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - Task Tool integration specs
- **[Claude Code Workflow](./CLAUDECODE-WORKFLOW.md)** - Basic workflow
- **[Quick Start Guide](./QUICK-START-GUIDE.md)** - General quick start
- **[CLI Commands Reference](./CLI-COMMANDS-REFERENCE.md)** - CLI command reference

## 💡 Summary

For effective development with ae-framework, the following are important:

1. **Clear requirement specification** - Be specific about functional, technical, and quality requirements
2. **Stepwise approach** - Review and approval for each phase
3. **Explicit quality standards** - Quantifiable quality metrics
4. **Technical constraint specification** - Specify technologies and architecture
5. **Monitoring & telemetry utilization** - Quality monitoring with OpenTelemetry

**🤖 Natural language instructions in Claude Code are most effective**. The key to success is clearly communicating "what you want to build" and "what quality you require" rather than technical details.

---

## Japanese

**Phase 6実装版：実際の開発プロジェクトでae-frameworkを使う具体的な指示方法**

### 📋 概要

Phase 6 UI/UX & Frontend Delivery実装済みのae-frameworkで実際に開発を行う場合の**具体的な指示方法**を説明します。Claude Codeでの自然言語指示から、CLI コマンドまで、実用的なシナリオベースで解説。

#### 🎯 このガイドの対象
- **プロジェクトマネージャー**: 要件を適切に伝える方法
- **開発者**: 効率的な実装指示のテクニック
- **品質担当者**: 高品質な成果物を得るための指示方法
- **UI/UXデザイナー**: デザインシステム統合の指示方法

## 🤖 Claude Code での開発指示

### 基本的な開発依頼パターン

#### 1. 包括的プロジェクト依頼

```
「ae-frameworkを使ってECサイトの商品管理システムを作ってください。

要件:
- 商品の一覧・詳細・新規作成・編集機能
- カテゴリ管理
- 在庫管理
- 管理者向けダッシュボード
- 日本語・英語対応
- アクセシビリティ準拠

技術要件:
- React + Next.js 14
- TypeScript strict mode
- レスポンシブデザイン
- テストカバレッジ80%以上
- OpenTelemetryテレメトリ監視

品質要件:
- WCAG 2.1 AA準拠
- パフォーマンススコア75%以上
- A11yスコア95%以上」
```

**期待される自動実行フロー:**
```bash
📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ecommerce-management v1.0.0
   Environment: development

✅ Phase 1-5 Complete - Analysis, Requirements, Stories, Validation, Domain Model
✅ Generated 32 files for 5/5 entities

📊 Quality Metrics:
  • Test Coverage: 87% (threshold: 80%) ✅
  • A11y Score: 96% (threshold: 95%) ✅  
  • Performance Score: 78% (threshold: 75%) ✅
  • i18n Coverage: 100% (ja/en) ✅

🎨 Generated Components:
  • React Components: 20 files
  • Next.js Pages: 15 files  
  • Storybook Stories: 5 files
  • E2E Tests: 10 files
  • Database Migrations: 5 files
```

#### 2. 段階的開発指示

```
Phase 1: 「まず要件分析から始めてください」
→ Intent Agentが要件を構造化・分析

Phase 2: 「要件を形式仕様に変換してください」  
→ Natural Language Agentが構造化要件を生成

Phase 3: 「ユーザーストーリーとテストを生成してください」
→ User Stories Agentがストーリーとテストを作成

Phase 4: 「要件とストーリーの整合性を検証してください」
→ Validation Agentが品質検証を実行

Phase 5: 「ドメインモデルを設計してください」
→ Domain Modeling Agentがエンティティと関係を設計

Phase 6: 「UIコンポーネントを生成してください」
→ UI Task AdapterがReactコンポーネントを自動生成
```

[Japanese content continues with all remaining sections following the same structure as English...]

---

**🚀 Experience efficient, high-quality software development with ae-framework! / ae-framework で、効率的で高品質なソフトウェア開発を今すぐ始めましょう！**