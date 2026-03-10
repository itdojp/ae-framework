---
docRole: derived
canonicalSource:
  - docs/phases/phase-6-uiux.md
lastVerified: '2026-03-10'
---

# 🎨 Phase 6: UI/UX & Frontend Delivery Quick Start

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Build a frontend baseline with React + Next.js through the currently implemented flow**

### ✅ Implemented / Reproducible Path

```text
pnpm install
pnpm run build
pnpm run verify:lite
pnpm run codex:quickstart
```

> Metrics and transcript blocks in this document are example outputs unless explicitly noted as measured results.
>
> Current enforcement status (as of 2026-02-18):
> - Adapter threshold jobs in `.github/workflows/adapter-thresholds.yml` run only when the PR has the `run-adapters` label.
> - Within `run-adapters` runs, a11y/perf/lighthouse are **report-only by default** and become blocking only with labels (`enforce-a11y`, `enforce-perf`, `enforce-lh`).
> - Coverage is validated by dedicated workflows (for example `coverage-check.yml`) and policy may differ by workflow/label.
> - See `docs/quality/adapter-thresholds.md` for the exact gate behavior.

### 📋 Overview

Phase 6 automatically generates React + Next.js 14 based frontend applications from domain models, featuring OpenTelemetry telemetry for quality monitoring.

#### 🎯 Key Features
- **Auto React Component Generation** - Button, Input, Form, Card, etc.
- **Next.js 14 App Router** - SEO-optimized page generation
- **Design System Integration** - Design Tokens + Tailwind CSS + shadcn/ui
- **Multi-language Support (i18n)** - Japanese/English support
- **Accessibility Checks (report-based)** - WCAG 2.1 AA guideline checks (label-gated enforcement)
- **Storybook Integration** - Auto component documentation
- **E2E Testing** - Automated Playwright test generation
- **OpenTelemetry Telemetry** - Real-time quality metrics monitoring

### ⚡ Quick Start

#### 1. Execute in Claude Code

```
User: I want to create an e-commerce app UI. Please generate admin panels for products, orders, and users using ae-framework.

Claude Code: Generating UI components using Phase 6 UI Task Adapter...

📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ae-framework v1.0.0
   Environment: development

✅ Generated UI files for detected entities
📊 Test Coverage: 96% (threshold: 80%) ✅
♿ A11y Score: 97% (threshold: 95%) ✅  
⚡ Performance Score: 79% (threshold: 75%) ✅
🏗️ Scaffold Time: 18243ms ✅

🎨 UI Analysis:
  • Generated files: depends on entity count and template set
  • Current template set: 7 files per entity (as of 2026-02-18)
  • Design Tokens: integrated ✅
  • i18n Support: ja/en ✅
```

#### 2. CLI Execution

```bash
# Main command
ae-framework ui-scaffold --components --tokens --a11y

# ae-ui alias (equivalent functionality)
ae-ui scaffold --components --tokens --a11y

# Enable OpenTelemetry telemetry
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components
```

### 🏗️ Generated Architecture

#### Package Structure
```
ae-framework/
├── packages/
│   ├── design-tokens/                       # Design tokens
│   │   ├── src/index.ts                     # Token definitions
│   │   └── src/tailwind.ts                  # Tailwind integration
│   └── ui/                                  # UI component library
│       ├── src/button.tsx                   # Button
│       ├── src/input.tsx                    # Input
│       ├── src/textarea.tsx                 # Textarea
│       ├── src/select.tsx                   # Select
│       ├── src/checkbox.tsx                 # Checkbox
│       └── src/dialog.tsx                   # Dialog
├── apps/
│   ├── web/                                 # Next.js web application
│   │   ├── app/[locale]/layout.tsx          # i18n layout
│   │   ├── app/[locale]/products/page.tsx   # Product list page
│   │   ├── app/[locale]/products/[id]/page.tsx # Product detail page
│   │   ├── app/[locale]/products/new/page.tsx  # Product creation
│   │   ├── components/ProductForm.tsx       # Product form
│   │   ├── components/ProductCard.tsx       # Product card
│   │   ├── messages/ja.json                 # Japanese translations
│   │   ├── messages/en.json                 # English translations
│   │   └── __e2e__/products.spec.ts         # E2E tests
│   └── storybook/                           # Storybook documentation
│       └── stories/Product.stories.tsx      # Component stories
└── templates/ui/                            # Handlebars templates
    ├── component-form.tsx.template          # Form template
    ├── component-card.tsx.template          # Card template
    └── page-list.tsx.template               # Page template
```

#### Technology Stack
- **Framework**: Next.js 14 App Router
- **UI Library**: Radix UI + Tailwind CSS + shadcn/ui
- **Design System**: Design Tokens + Class Variance Authority (CVA)
- **Forms**: React Hook Form + Zod validation
- **State Management**: TanStack Query 5
- **Testing**: Playwright E2E + Storybook + Vitest
- **i18n**: next-intl (ja/en)
- **A11y**: WCAG 2.1 AA + eslint-plugin-jsx-a11y
- **Telemetry**: OpenTelemetry
- **Icons**: Lucide React

### 🚀 Development Workflow

#### 1. Project Initialization
```bash
# Install dependencies
pnpm install

# Build design tokens
pnpm run build:tokens

# Build UI components
pnpm run build:ui
```

#### 2. Start Development Server
```bash
# Web application
pnpm run dev:web

# Storybook (separate terminal)
pnpm run dev:storybook
```

#### 3. Quality Checks
```bash
# ESLint + TypeScript
pnpm run lint:frontend
pnpm run type-check:frontend

# Run tests
pnpm run test:visual
pnpm run test:e2e

# Build
pnpm run build:frontend
```

### 📊 OpenTelemetry Telemetry Monitoring

#### Configuration
```bash
# Development (Console export)
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components

# Production (OTLP export)  
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 ae-framework ui-scaffold --components

# Disable telemetry
DISABLE_TELEMETRY=true ae-framework ui-scaffold --components
```

#### Monitoring Metrics
- **Quality Metrics (example targets)**: Test coverage (≥80%), A11y score (≥95%), Performance score (≥75%)
- **Efficiency Metrics**: Scaffold time (<30s), E2E test time (<5min), Build time
- **Maintainability Metrics**: Component complexity (<10), Unused CSS rate (<5%), Design token usage (≥95%)

#### Telemetry Output Example
```bash
📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ae-framework v1.0.0
   Environment: development
   OTLP Export: ✅ Enabled

📊 Test Coverage: 85% (threshold: 80%) ✅
♿ A11y Score: 96% (threshold: 95%) ✅  
⚡ Performance Score: 78% (threshold: 75%) ✅
🏗️ Scaffold Time: 25000ms ✅
⚠️ E2E Test Time: 320000ms (threshold: 300000ms)
🎨 Component Complexity: avg 6.2 (threshold: 10) ✅
🌐 i18n Coverage: 98% (ja/en) ✅
📐 Design Token Usage: 95% ✅
```

### 🌍 Multi-language Support (i18n)

#### Supported Languages
- **Japanese (ja)**: Default
- **English (en)**: Fallback

#### Translation File Examples
```text
// messages/ja.json
{
  "Navigation": {
    "home": "ホーム",
    "products": "商品",
    "orders": "注文"
  },
  "Product": {
    "title": "商品名",
    "price": "価格",
    "description": "説明",
    "add_to_cart": "カートに追加"
  }
}

// messages/en.json
{
  "Navigation": {
    "home": "Home",
    "products": "Products", 
    "orders": "Orders"
  },
  "Product": {
    "title": "Product Name",
    "price": "Price",
    "description": "Description",
    "add_to_cart": "Add to Cart"
  }
}
```

### ♿ Accessibility (A11y)

#### WCAG 2.1 AA Compliance
- **Color Contrast**: Minimum 4.5:1 (normal text), 3:1 (large text)
- **Focus Indicators**: 2px minimum visual focus display
- **Keyboard Navigation**: All interactive elements keyboard accessible
- **Screen Readers**: Proper ARIA labels and semantic HTML

#### Automated Testing
```bash
# Accessibility tests
pnpm run test:a11y

# Threshold check (critical=0, warnings≤5)
node scripts/check-a11y-threshold.js --critical=0 --warnings=5
```

### 📚 Storybook Integration

#### Auto-generated Stories
```text
// stories/Product.stories.tsx
import type { Meta, StoryObj } from '@storybook/react';
import { ProductForm } from '../apps/web/components/ProductForm';

const meta: Meta<typeof ProductForm> = {
  title: 'Forms/ProductForm',
  component: ProductForm,
  parameters: {
    a11y: {
      config: {
        rules: [
          { id: 'color-contrast', enabled: true },
          { id: 'keyboard-navigation', enabled: true }
        ]
      }
    }
  }
};

export default meta;
type Story = StoryObj<typeof meta>;

export const Default: Story = {
  args: {
    initialData: undefined,
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: false
  }
};

export const WithInitialData: Story = {
  args: {
    initialData: {
      name: 'Sample Product',
      price: 99.99,
      description: 'This is a sample product description'
    },
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: false
  }
};
```

### 🧪 E2E Testing

#### Auto-generated Tests
```text
// __e2e__/products.spec.ts
import { test, expect } from '@playwright/test';

test.describe('Product Management', () => {
  test('should create a new product', async ({ page }) => {
    await page.goto('/products/new');
    
    // Form input
    await page.fill('[data-testid="product-name"]', 'Test Product');
    await page.fill('[data-testid="product-price"]', '99.99');
    await page.fill('[data-testid="product-description"]', 'Test Description');
    
    // Submit
    await page.click('[data-testid="submit-button"]');
    
    // Verify result
    await expect(page).toHaveURL('/products');
    await expect(page.locator('[data-testid="product-card"]')).toContainText('Test Product');
  });

  test('should be accessible', async ({ page }) => {
    await page.goto('/products');
    
    // Accessibility check
    const accessibilityScanResults = await new AxeBuilder({ page }).analyze();
    expect(accessibilityScanResults.violations).toEqual([]);
  });
});
```

### 🎯 Quality Gates

#### Required Checklist
- ✅ **TypeScript**: Zero type errors, strict mode compliance
- ✅ **ESLint**: Zero syntax errors, minimized warnings
- ✅ **Test Coverage**: ≥80%
- ✅ **A11y Score**: ≥95% (WCAG 2.1 AA compliance)
- ✅ **Performance Score**: ≥75% (Lighthouse CI)
- ✅ **Build Success**: Successful build of all packages

#### Automated Quality Monitoring
```text
# Run all quality gates
pnpm run quality:gates

# Individual checks
pnpm run lint:frontend
pnpm run type-check:frontend
pnpm run test:coverage
pnpm run test:a11y
pnpm run build:frontend
```

### 🔧 Customization

#### Design Tokens
```typescript
// packages/design-tokens/src/index.ts
export const designTokens = {
  colors: {
    primary: {
      50: '#eff6ff',
      500: '#3b82f6',
      900: '#1e3a8a'
    }
  },
  spacing: {
    xs: '0.5rem',
    sm: '1rem',
    md: '1.5rem'
  },
  typography: {
    fontFamily: {
      sans: ['Inter', 'system-ui', 'sans-serif']
    }
  }
};
```

#### Custom Components
```bash
# Create custom template
cp templates/ui/component-form.tsx.template templates/ui/my-component.tsx.template

# Generate with customization
ae-framework ui-scaffold --template=my-component --entity=CustomEntity
```

### 🚨 Troubleshooting

#### Common Issues and Solutions

**1. Build Errors**
```bash
# TypeScript type errors
pnpm run type-check:frontend

# Dependency issues
rm -rf node_modules && pnpm install
```

**2. Telemetry Not Displaying**
```bash
# Enable debug mode
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components

# Set log level
OTEL_LOG_LEVEL=debug ae-framework ui-scaffold --components
```

**3. Accessibility Test Failures**
```bash
# Generate detailed report
pnpm run test:a11y:report

# Fix specific issues
pnpm run test:a11y -- --fix
```

### 🎉 Next Steps

1. **Extend Component Library**: Add custom components
2. **Theme System**: Dark mode support
3. **Performance Optimization**: Bundle size reduction
4. **Internationalization Extension**: Additional language support
5. **CI/CD Integration**: GitHub Actions integration

---

## Japanese

**現在実装されている導線で、React + Next.js フロントエンド基盤を構築**

### ✅ 現在実装に整合する手順

```bash
pnpm install
pnpm run build
pnpm run verify:lite
pnpm run codex:quickstart
```

> この文書中のメトリクス/ログは、明示がない限り実行例です（実測値の保証ではありません）。
>
> 現行の強制ポリシー（2026-02-18時点）:
> - `.github/workflows/adapter-thresholds.yml` のアダプタしきい値ジョブは、PRに `run-adapters` ラベルがある場合のみ実行されます。
> - `run-adapters` 実行時、a11y/perf/lighthouse は既定で **report-only** であり、ラベル（`enforce-a11y`/`enforce-perf`/`enforce-lh`）付与時のみブロッキングになります。
> - Coverage は専用workflow（例: `coverage-check.yml`）側で判定され、workflow/ラベルにより挙動が変わります。
> - 詳細は `docs/quality/adapter-thresholds.md` を参照してください。

### 📋 概要

Phase 6では、ドメインモデルから**React + Next.js 14**ベースのフロントエンドアプリケーションを自動生成します。OpenTelemetryテレメトリによる品質監視機能付き。

#### 🎯 主要機能
- **React コンポーネント自動生成** - Button, Input, Form, Card等
- **Next.js 14 App Router** - SEO最適化されたページ生成
- **デザインシステム統合** - Design Tokens + Tailwind CSS + shadcn/ui
- **多言語対応 (i18n)** - 日本語/英語対応
- **アクセシビリティ検証（レポート主体）** - WCAG 2.1 AAガイドライン検証（強制はラベル制御）
- **Storybook統合** - コンポーネントドキュメント自動生成
- **E2Eテスト** - Playwright自動テスト生成
- **OpenTelemetryテレメトリ** - リアルタイム品質メトリクス監視

### ⚡ クイックスタート

#### 1. Claude Code での実行

```
User: eコマースアプリのUIを作りたいです。商品、注文、ユーザーの管理画面をae-frameworkで生成してください。

Claude Code: Phase 6 UI Task Adapterを使用してUIコンポーネントを生成します...

📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ae-framework v1.0.0
   Environment: development

✅ エンティティに応じたUIファイルを生成
📊 Test Coverage: 96% (threshold: 80%) ✅
♿ A11y Score: 97% (threshold: 95%) ✅  
⚡ Performance Score: 79% (threshold: 75%) ✅
🏗️ Scaffold Time: 18243ms ✅

🎨 UI Analysis:
  • 生成ファイル数: エンティティ数とテンプレート数に依存
  • 現在のテンプレート: 1エンティティあたり7ファイル（2026-02-18時点）
  • Design Tokens: integrated ✅
  • i18n Support: ja/en ✅
```

#### 2. CLI での実行

```bash
# メインコマンド
ae-framework ui-scaffold --components --tokens --a11y

# ae-ui エイリアス (同等の動作)
ae-ui scaffold --components --tokens --a11y

# OpenTelemetryテレメトリ有効化
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components
```

### 🏗️ 生成されるアーキテクチャ

#### パッケージ構造
```
ae-framework/
├── packages/
│   ├── design-tokens/                       # デザイントークン
│   │   ├── src/index.ts                     # トークン定義
│   │   └── src/tailwind.ts                  # Tailwind統合
│   └── ui/                                  # UIコンポーネントライブラリ
│       ├── src/button.tsx                   # Button
│       ├── src/input.tsx                    # Input
│       ├── src/textarea.tsx                 # Textarea
│       ├── src/select.tsx                   # Select
│       ├── src/checkbox.tsx                 # Checkbox
│       └── src/dialog.tsx                   # Dialog
├── apps/
│   ├── web/                                 # Next.js Webアプリケーション
│   │   ├── app/[locale]/layout.tsx          # i18nレイアウト
│   │   ├── app/[locale]/products/page.tsx   # 商品一覧ページ
│   │   ├── app/[locale]/products/[id]/page.tsx # 商品詳細ページ
│   │   ├── app/[locale]/products/new/page.tsx  # 商品新規作成
│   │   ├── components/ProductForm.tsx       # 商品フォーム
│   │   ├── components/ProductCard.tsx       # 商品カード
│   │   ├── messages/ja.json                 # 日本語翻訳
│   │   ├── messages/en.json                 # 英語翻訳
│   │   └── __e2e__/products.spec.ts         # E2Eテスト
│   └── storybook/                           # Storybookドキュメント
│       └── stories/Product.stories.tsx      # コンポーネントストーリー
└── templates/ui/                            # Handlebarsテンプレート
    ├── component-form.tsx.template          # フォームテンプレート
    ├── component-card.tsx.template          # カードテンプレート
    └── page-list.tsx.template               # ページテンプレート
```

#### 技術スタック
- **Framework**: Next.js 14 App Router
- **UI Library**: Radix UI + Tailwind CSS + shadcn/ui
- **Design System**: Design Tokens + Class Variance Authority (CVA)
- **Forms**: React Hook Form + Zod validation
- **State Management**: TanStack Query 5
- **Testing**: Playwright E2E + Storybook + Vitest
- **i18n**: next-intl (ja/en)
- **A11y**: WCAG 2.1 AA + eslint-plugin-jsx-a11y
- **Telemetry**: OpenTelemetry
- **Icons**: Lucide React

### 🚀 開発ワークフロー

#### 1. プロジェクト初期化
```bash
# 依存関係インストール
pnpm install

# デザイントークンビルド
pnpm run build:tokens

# UIコンポーネントビルド
pnpm run build:ui
```

#### 2. 開発サーバー起動
```bash
# Webアプリケーション
pnpm run dev:web

# Storybook (別ターミナル)
pnpm run dev:storybook
```

#### 3. 品質チェック
```bash
# ESLint + TypeScript
pnpm run lint:frontend
pnpm run type-check:frontend

# テスト実行
pnpm run test:visual
pnpm run test:e2e

# ビルド
pnpm run build:frontend
```

### 📊 OpenTelemetryテレメトリ監視

#### 設定方法
```bash
# Development (Console export)
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components

# Production (OTLP export)  
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 ae-framework ui-scaffold --components

# Disable telemetry
DISABLE_TELEMETRY=true ae-framework ui-scaffold --components
```

#### 監視メトリクス
- **品質メトリクス（目安値）**: テストカバレッジ(≥80%)、A11yスコア(≥95%)、パフォーマンススコア(≥75%)
- **効率性メトリクス**: スキャフォールド時間(<30秒)、E2Eテスト時間(<5分)、ビルド時間
- **保守性メトリクス**: コンポーネント複雑度(<10)、未使用CSS率(<5%)、デザイントークン使用率(≥95%)

#### テレメトリ出力例
```bash
📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ae-framework v1.0.0
   Environment: development
   OTLP Export: ✅ Enabled

📊 Test Coverage: 85% (threshold: 80%) ✅
♿ A11y Score: 96% (threshold: 95%) ✅  
⚡ Performance Score: 78% (threshold: 75%) ✅
🏗️ Scaffold Time: 25000ms ✅
⚠️ E2E Test Time: 320000ms (threshold: 300000ms)
🎨 Component Complexity: avg 6.2 (threshold: 10) ✅
🌐 i18n Coverage: 98% (ja/en) ✅
📐 Design Token Usage: 95% ✅
```

### 🌍 多言語対応 (i18n)

#### サポート言語
- **日本語 (ja)**: デフォルト
- **英語 (en)**: フォールバック

#### 翻訳ファイル例
```text
// messages/ja.json
{
  "Navigation": {
    "home": "ホーム",
    "products": "商品",
    "orders": "注文"
  },
  "Product": {
    "title": "商品名",
    "price": "価格",
    "description": "説明",
    "add_to_cart": "カートに追加"
  }
}

// messages/en.json
{
  "Navigation": {
    "home": "Home",
    "products": "Products", 
    "orders": "Orders"
  },
  "Product": {
    "title": "Product Name",
    "price": "Price",
    "description": "Description",
    "add_to_cart": "Add to Cart"
  }
}
```

### ♿ アクセシビリティ (A11y)

#### WCAG 2.1 AA準拠
- **カラーコントラスト**: 最小4.5:1 (通常テキスト)、3:1 (大きなテキスト)
- **フォーカスインジケーター**: 2px最小の視覚的フォーカス表示
- **キーボードナビゲーション**: 全インタラクティブ要素がキーボード操作可能
- **スクリーンリーダー**: 適切なARIAラベルとセマンティックHTML

#### 自動テスト
```bash
# アクセシビリティテスト
pnpm run test:a11y

# 閾値チェック (重大=0, 警告≤5)
node scripts/check-a11y-threshold.js --critical=0 --warnings=5
```

### 📚 Storybook統合

#### 自動生成されるストーリー
```text
// stories/Product.stories.tsx
import type { Meta, StoryObj } from '@storybook/react';
import { ProductForm } from '../apps/web/components/ProductForm';

const meta: Meta<typeof ProductForm> = {
  title: 'Forms/ProductForm',
  component: ProductForm,
  parameters: {
    a11y: {
      config: {
        rules: [
          { id: 'color-contrast', enabled: true },
          { id: 'keyboard-navigation', enabled: true }
        ]
      }
    }
  }
};

export default meta;
type Story = StoryObj<typeof meta>;

export const Default: Story = {
  args: {
    initialData: undefined,
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: false
  }
};

export const WithInitialData: Story = {
  args: {
    initialData: {
      name: 'Sample Product',
      price: 99.99,
      description: 'This is a sample product description'
    },
    onSubmit: (data) => console.log('Form submitted:', data),
    isLoading: false
  }
};
```

### 🧪 E2Eテスト

#### 自動生成されるテスト
```text
// __e2e__/products.spec.ts
import { test, expect } from '@playwright/test';

test.describe('Product Management', () => {
  test('should create a new product', async ({ page }) => {
    await page.goto('/products/new');
    
    // フォーム入力
    await page.fill('[data-testid="product-name"]', 'Test Product');
    await page.fill('[data-testid="product-price"]', '99.99');
    await page.fill('[data-testid="product-description"]', 'Test Description');
    
    // 送信
    await page.click('[data-testid="submit-button"]');
    
    // 結果確認
    await expect(page).toHaveURL('/products');
    await expect(page.locator('[data-testid="product-card"]')).toContainText('Test Product');
  });

  test('should be accessible', async ({ page }) => {
    await page.goto('/products');
    
    // アクセシビリティチェック
    const accessibilityScanResults = await new AxeBuilder({ page }).analyze();
    expect(accessibilityScanResults.violations).toEqual([]);
  });
});
```

### 🎯 品質ゲート

#### 必須チェック項目
- ✅ **TypeScript**: 型エラー0、strict mode準拠
- ✅ **ESLint**: 構文エラー0、警告最小化
- ✅ **テストカバレッジ**: ≥80%
- ✅ **A11yスコア**: ≥95% (WCAG 2.1 AA準拠)
- ✅ **パフォーマンススコア**: ≥75% (Lighthouse CI)
- ✅ **ビルド成功**: 全パッケージのビルド成功

#### 自動品質監視
```bash
# 全品質ゲート実行
pnpm run quality:gates

# 個別チェック
pnpm run lint:frontend
pnpm run type-check:frontend
pnpm run test:coverage
pnpm run test:a11y
pnpm run build:frontend
```

### 🔧 カスタマイズ

#### デザイントークン
```typescript
// packages/design-tokens/src/index.ts
export const designTokens = {
  colors: {
    primary: {
      50: '#eff6ff',
      500: '#3b82f6',
      900: '#1e3a8a'
    }
  },
  spacing: {
    xs: '0.5rem',
    sm: '1rem',
    md: '1.5rem'
  },
  typography: {
    fontFamily: {
      sans: ['Inter', 'system-ui', 'sans-serif']
    }
  }
};
```

#### カスタムコンポーネント
```bash
# カスタムテンプレート作成
cp templates/ui/component-form.tsx.template templates/ui/my-component.tsx.template

# カスタマイズ後の生成
ae-framework ui-scaffold --template=my-component --entity=CustomEntity
```

### 🚨 トラブルシューティング

#### よくある問題と解決法

**1. ビルドエラー**
```bash
# TypeScript型エラー
pnpm run type-check:frontend

# 依存関係の問題
rm -rf node_modules && pnpm install
```

**2. テレメトリが表示されない**
```bash
# デバッグモード有効化
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components

# ログレベル設定
OTEL_LOG_LEVEL=debug ae-framework ui-scaffold --components
```

**3. アクセシビリティテスト失敗**
```bash
# 詳細レポート生成
pnpm run test:a11y:report

# 特定の問題を修正
pnpm run test:a11y -- --fix
```

### 🎉 次のステップ

1. **コンポーネントライブラリ拡張**: カスタムコンポーネントの追加
2. **テーマシステム**: ダークモード対応
3. **パフォーマンス最適化**: バンドルサイズ削減
4. **国際化拡張**: 他言語サポート追加
5. **CI/CD統合**: GitHub Actionsとの連携

---

**🤖 Experience modern frontend development with ae-framework Phase 6 today! / ae-framework Phase 6で、モダンなフロントエンド開発を今すぐ体験してください！**
