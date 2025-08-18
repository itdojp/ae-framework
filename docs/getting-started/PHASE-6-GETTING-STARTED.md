# 🎨 Phase 6: UI/UX & Frontend Delivery クイックスタート

> React + Next.js 14でモダンなフロントエンド基盤を15分で構築

## 📋 概要

Phase 6では、ドメインモデルから**React + Next.js 14**ベースのフロントエンドアプリケーションを自動生成します。OpenTelemetryテレメトリによる品質監視機能付き。

### 🎯 主要機能
- **React コンポーネント自動生成** - Button, Input, Form, Card等
- **Next.js 14 App Router** - SEO最適化されたページ生成
- **デザインシステム統合** - Design Tokens + Tailwind CSS + shadcn/ui
- **多言語対応 (i18n)** - 日本語/英語対応
- **アクセシビリティ準拠** - WCAG 2.1 AA基準
- **Storybook統合** - コンポーネントドキュメント自動生成
- **E2Eテスト** - Playwright自動テスト生成
- **OpenTelemetryテレメトリ** - リアルタイム品質メトリクス監視

## ⚡ クイックスタート

### 1. Claude Code での実行

```
User: eコマースアプリのUIを作りたいです。商品、注文、ユーザーの管理画面をae-frameworkで生成してください。

Claude Code: Phase 6 UI Task Adapterを使用してUIコンポーネントを生成します...

📊 OpenTelemetry initialized for ae-framework Phase 6
   Service: ae-framework v1.0.0
   Environment: development

✅ Generated 21 files for 3/3 entities
📊 Test Coverage: 96% (threshold: 80%) ✅
♿ A11y Score: 97% (threshold: 95%) ✅  
⚡ Performance Score: 79% (threshold: 75%) ✅
🏗️ Scaffold Time: 18243ms ✅

🎨 UI Analysis:
  • React Components: 12 files
  • Next.js Pages: 9 files  
  • Storybook Stories: 3 files
  • E2E Tests: 3 files
  • Design Tokens: integrated ✅
  • i18n Support: ja/en ✅
```

### 2. CLI での実行

```bash
# メインコマンド
ae-framework ui-scaffold --components --tokens --a11y

# ae-ui エイリアス (同等の動作)
ae-ui scaffold --components --state --storybook

# OpenTelemetryテレメトリ有効化
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components

# 特定エンティティのみ生成
ae-framework ui-scaffold --entity=Product --components
```

## 🏗️ 生成されるアーキテクチャ

### パッケージ構造
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

### 技術スタック
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

## 🚀 開発ワークフロー

### 1. プロジェクト初期化
```bash
# 依存関係インストール
pnpm install

# デザイントークンビルド
pnpm run build:tokens

# UIコンポーネントビルド
pnpm run build:ui
```

### 2. 開発サーバー起動
```bash
# Webアプリケーション
pnpm run dev:web

# Storybook (別ターミナル)
pnpm run dev:storybook
```

### 3. 品質チェック
```bash
# ESLint + TypeScript
pnpm run lint:frontend
pnpm run type-check:frontend

# テスト実行
pnpm run test:frontend
pnpm run test:e2e

# ビルド
pnpm run build:frontend
```

## 📊 OpenTelemetryテレメトリ監視

### 設定方法
```bash
# Development (Console export)
DEBUG_TELEMETRY=true ae-framework ui-scaffold --components

# Production (OTLP export)  
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 ae-framework ui-scaffold --components

# Disable telemetry
DISABLE_TELEMETRY=true ae-framework ui-scaffold --components
```

### 監視メトリクス
- **品質メトリクス**: テストカバレッジ(≥80%)、A11yスコア(≥95%)、パフォーマンススコア(≥75%)
- **効率性メトリクス**: スキャフォールド時間(<30秒)、E2Eテスト時間(<5分)、ビルド時間
- **保守性メトリクス**: コンポーネント複雑度(<10)、未使用CSS率(<5%)、デザイントークン使用率(≥95%)

### テレメトリ出力例
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

## 🌍 多言語対応 (i18n)

### サポート言語
- **日本語 (ja)**: デフォルト
- **英語 (en)**: フォールバック

### 翻訳ファイル例
```json
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

## ♿ アクセシビリティ (A11y)

### WCAG 2.1 AA準拠
- **カラーコントラスト**: 最小4.5:1 (通常テキスト)、3:1 (大きなテキスト)
- **フォーカスインジケーター**: 2px最小の視覚的フォーカス表示
- **キーボードナビゲーション**: 全インタラクティブ要素がキーボード操作可能
- **スクリーンリーダー**: 適切なARIAラベルとセマンティックHTML

### 自動テスト
```bash
# アクセシビリティテスト
npm run test:a11y

# 閾値チェック (重大=0, 警告≤5)
node scripts/check-a11y-threshold.js --critical=0 --warnings=5
```

## 📚 Storybook統合

### 自動生成されるストーリー
```typescript
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

## 🧪 E2Eテスト

### 自動生成されるテスト
```typescript
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

## 🎯 品質ゲート

### 必須チェック項目
- ✅ **TypeScript**: 型エラー0、strict mode準拠
- ✅ **ESLint**: 構文エラー0、警告最小化
- ✅ **テストカバレッジ**: ≥80%
- ✅ **A11yスコア**: ≥95% (WCAG 2.1 AA準拠)
- ✅ **パフォーマンススコア**: ≥75% (Lighthouse CI)
- ✅ **ビルド成功**: 全パッケージのビルド成功

### 自動品質監視
```bash
# 全品質ゲート実行
npm run quality:check

# 個別チェック
npm run lint:frontend
npm run type-check:frontend
npm run test:coverage
npm run test:a11y
npm run build:frontend
```

## 🔧 カスタマイズ

### デザイントークン
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

### カスタムコンポーネント
```bash
# カスタムテンプレート作成
cp templates/ui/component-form.tsx.template templates/ui/my-component.tsx.template

# カスタマイズ後の生成
ae-framework ui-scaffold --template=my-component --entity=CustomEntity
```

## 🚨 トラブルシューティング

### よくある問題と解決法

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
npm run test:a11y:report

# 特定の問題を修正
npm run test:a11y -- --fix
```

## 🎉 次のステップ

1. **コンポーネントライブラリ拡張**: カスタムコンポーネントの追加
2. **テーマシステム**: ダークモード対応
3. **パフォーマンス最適化**: バンドルサイズ削減
4. **国際化拡張**: 他言語サポート追加
5. **CI/CD統合**: GitHub Actionsとの連携

---

**🤖 ae-framework Phase 6で、モダンなフロントエンド開発を今すぐ体験してください！**