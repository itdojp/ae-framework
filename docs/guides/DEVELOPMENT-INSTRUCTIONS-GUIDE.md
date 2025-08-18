# 🚀 ae-framework 開発指示ガイド

> Phase 6実装版：実際の開発プロジェクトでae-frameworkを使う具体的な指示方法

## 📋 概要

Phase 6 UI/UX & Frontend Delivery実装済みのae-frameworkで実際に開発を行う場合の**具体的な指示方法**を説明します。Claude Codeでの自然言語指示から、CLI コマンドまで、実用的なシナリオベースで解説。

### 🎯 このガイドの対象
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

## 🎯 実用シナリオ別指示例

### シナリオ1: 新規プロジェクト開発

```
「ae-frameworkで在庫管理システムを作りたいです。

【機能要件】
- 商品マスタ管理（商品名、価格、カテゴリ、在庫数）
- 入出庫管理（入庫、出庫、調整）
- 発注管理（発注点管理、自動発注提案）
- レポート機能（在庫一覧、売上分析）

【非機能要件】
- レスポンス時間: 3秒以内
- 同時ユーザー: 100人
- 可用性: 99.9%
- データベース: PostgreSQL

【UI要件】
- モダンなデザイン（Material Design 3風）
- モバイル対応（レスポンシブ）
- 日本語UI
- WCAG 2.1 AA準拠

【監視要件】
- OpenTelemetryテレメトリで品質監視を有効にしてください
- Core Web Vitals監視
- カスタムビジネスメトリクス追跡」
```

**期待される出力:**
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

### シナリオ2: 既存プロジェクトへの機能追加

```
「既存のECサイトにレビュー機能を追加してください。

【追加要件】
- 商品レビュー投稿・表示
- 5段階評価
- 画像付きレビュー
- レビューの承認機能（管理者）
- レビューの検索・フィルタリング

【制約条件】
- 既存のProductエンティティを拡張
- 影響範囲を最小限に抑制
- 既存テストが壊れないように
- 段階的デプロイメント可能な設計

【品質要件】
- 既存機能への影響なし
- 新機能のテストカバレッジ90%以上
- レビュー投稿のパフォーマンス最適化」
```

**期待される出力:**
```bash
🔍 Impact Analysis Complete:
  • Modified Entities: Product (review関連フィールド追加)
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

### シナリオ3: 特定コンポーネントの生成

```
「商品カードコンポーネントだけを生成してください。

【デザイン要件】
- 商品名、価格、画像、レーティング表示
- カートに追加ボタン
- お気に入り機能
- ホバーエフェクト
- レスポンシブ対応

【技術要件】
- TypeScript strict mode
- Storybookストーリー含む
- Playwrightテスト含む
- アクセシビリティ準拠

【エンティティ定義】
name: string (required)
price: number (required)
image: string (optional)
rating: number (0-5, optional)
inStock: boolean (required)
category: string (optional)」
```

**CLI指示:**
```bash
ae-framework ui-scaffold --entity=Product --components --storybook --tests
```

**期待される出力:**
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

## 🛠️ 開発段階別の指示方法

### Phase 1-5: 企画・設計段階

#### 要件分析のみ実行
```
「要件分析だけ実行してください。結果を確認してから次に進みたいです。」
```

**CLI指示:**
```bash
ae-framework intent --analyze --sources="requirements.md"
```

#### ユーザーストーリー生成
```
「要件からユーザーストーリーを生成してください。エピック単位で整理してください。」
```

**CLI指示:**
```bash
ae-framework user-stories --generate --organize-epics
```

#### ドメインモデル作成
```
「ユーザーストーリーからドメインモデルを作成してください。エンティティ間の関係性も明確にしてください。」
```

**CLI指示:**
```bash
ae-framework domain-model --entities --relationships
```

### Phase 6: UI/UX実装段階

#### 基本UIコンポーネント生成
```
「基本的なUIコンポーネントを生成してください」
```

**CLI指示:**
```bash
ae-framework ui-scaffold --components
```

#### Storybook統合
```
「Storybookドキュメントも含めて生成してください」
```

**CLI指示:**
```bash
ae-framework ui-scaffold --components --storybook
```

#### 多言語対応
```
「多言語対応も設定してください（日本語・英語・韓国語）」
```

**CLI指示:**
```bash
ae-framework ui-scaffold --components --i18n --locales=ja,en,ko
```

#### 全機能統合
```
「全部含めて生成してください（コンポーネント・Storybook・i18n・A11y）」
```

**CLI指示:**
```bash
ae-framework ui-scaffold --components --storybook --i18n --a11y
```

## 🎨 UI/UX特化の指示例

### デザインシステム統合

```
「Material Design 3風のデザインシステムで商品カタログを作ってください。

【デザイン仕様】
- Google Material Design 3準拠
- プライマリカラー: #1976d2 (blue)
- セカンダリカラー: #f57c00 (orange)  
- タイポグラフィ: Roboto
- 角丸: 8px
- シャドウ: elevation 2

【コンポーネント要件】
- ProductGrid (商品一覧グリッド)
- ProductCard (商品カード)
- SearchBar (検索バー)
- FilterChips (フィルターチップ)
- CategoryNav (カテゴリナビゲーション)

【レスポンシブ要件】
- Desktop: 4カラムグリッド
- Tablet: 3カラムグリッド
- Mobile: 2カラムグリッド」
```

### アクセシビリティ重視

```
「視覚障害者にも使いやすい商品検索画面を作ってください。

【A11y要件】
- WCAG 2.1 AAA準拠（最高レベル）
- スクリーンリーダー完全対応
- キーボードナビゲーション
- 高コントラスト表示対応
- 音声読み上げ最適化
- フォーカス管理の最適化

【追加機能】
- 音声検索機能
- キーボードショートカット
- スキップリンク
- ARIA live regions
- カスタムフォーカスインジケーター」
```

### モバイルファースト設計

```
「モバイルファーストでECアプリを設計してください。

【モバイル最適化】
- タッチフレンドリーなUIサイズ（44px以上）
- スワイプジェスチャー対応
- プログレッシブWebアプリ機能
- オフライン対応
- プッシュ通知

【パフォーマンス要件】
- First Contentful Paint < 2秒
- Largest Contentful Paint < 3秒  
- Cumulative Layout Shift < 0.1
- 画像の遅延読み込み
- バンドルサイズ最適化」
```

## 📊 品質・監視重視の指示

### テレメトリ監視重視

```
「パフォーマンス監視を重視したダッシュボードを作ってください。

【監視要件】
- リアルタイムメトリクス表示
- レスポンス時間監視
- エラー率トラッキング
- ユーザー行動分析
- A/Bテスト機能

【OpenTelemetryテレメトリ監視項目】
- Core Web Vitals (LCP, FID, CLS)
- カスタムビジネスメトリクス
- ユーザージャーニー追跡
- コンバージョン率
- APIレスポンス時間
- データベースクエリパフォーマンス

【アラート設定】
- パフォーマンス劣化時の自動アラート
- エラー率閾値超過時の通知
- ユーザビリティ問題の検出」
```

**期待される出力:**
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

### 高品質要件

```
「エンタープライズレベルの品質で顧客管理システムを作ってください。

【品質要件】
- テストカバレッジ: 95%以上
- TypeScript strict mode
- ESLint error: 0件
- パフォーマンススコア: 90%以上  
- A11yスコア: 98%以上
- セキュリティスキャン: クリーン

【セキュリティ要件】
- API Rate Limiting
- CSRF Protection  
- XSS Prevention
- SQL Injection対策
- 入力値サニタイゼーション
- セッション管理の強化

【コード品質要件】
- Clean Architecture適用
- SOLID原則遵守
- DRY原則適用
- 包括的なドキュメント
- コードレビューチェックリスト」
```

## 🔧 カスタマイズ・拡張指示

### デザイントークンカスタマイズ

```
「デザイントークンを会社のブランドカラーに変更してください。

【ブランド仕様】
- プライマリ: #2E86AB (企業青)
- セカンダリ: #A23B72 (企業ピンク)  
- アクセント: #F18F01 (企業オレンジ)
- ニュートラル: #C73E1D (企業赤)

【タイポグラフィ】
- ヘッドライン: 'Noto Sans JP', sans-serif
- ボディ: 'Roboto', sans-serif
- コード: 'Fira Code', monospace

【スペーシング】
- ベースユニット: 8px
- コンポーネント間: 16px
- セクション間: 32px」
```

### 多言語対応拡張

```
「多言語対応に韓国語と中国語（簡体字・繁体字）を追加してください。

【対応言語】
- 日本語 (ja): デフォルト
- 英語 (en): セカンダリ
- 韓国語 (ko): 新規追加
- 中国語簡体字 (zh-CN): 新規追加
- 中国語繁体字 (zh-TW): 新規追加

【翻訳要件】
- 商品・カテゴリ情報の翻訳
- UI文言の翻訳
- エラーメッセージの翻訳
- 日時・通貨フォーマットの地域化
- RTLサポート（アラビア語将来対応）

【技術要件】
- next-intl設定拡張
- 翻訳キーの体系化
- 翻訳漏れの自動検出」
```

### カスタムコンポーネント追加

```
「既存のUIライブラリにカスタムチャートコンポーネントを追加してください。

【チャート要件】
- バーチャート
- ラインチャート
- パイチャート
- ドーナツチャート
- エリアチャート

【技術仕様】
- Chart.js または D3.js ベース
- TypeScript完全対応
- レスポンシブデザイン
- アクセシブル（スクリーンリーダー対応）
- カスタムテーマ対応

【Storybook統合】
- 各チャートタイプのストーリー
- インタラクティブな設定例
- データフォーマット例」
```

## 🚨 トラブルシューティング指示

### 段階的な確認指示

```
「Phase 1の要件分析結果を確認してから次に進みたいです」
→ 各フェーズの結果をレビューしてから次段階へ

「ドメインモデルが正しいか確認してください」
→ 設計の妥当性をチェック

「生成されたコンポーネントをレビューしてください」
→ コード品質の確認
```

### 品質問題の修正指示

```
「ビルドエラーが発生しています。修正してください」
→ TypeScript型エラー、依存関係問題の解決

「アクセシビリティテストが失敗しています。WCAG 2.1 AA準拠になるよう修正してください」
→ A11y問題の特定と修正

「パフォーマンスが閾値を下回っています。最適化してください」
→ バンドルサイズ、画像最適化、コード分割の実行

「テストカバレッジが80%を下回っています」
→ 不足しているテストケースの追加
```

### デバッグ・調査指示

```
「OpenTelemetryテレメトリが表示されない理由を調査してください」
→ 設定確認、ログ分析

「レスポンス時間が遅い原因を特定してください」
→ パフォーマンス分析、ボトルネック調査

「UIコンポーネントが正しく表示されない問題を解決してください」
→ CSS、レイアウト、ブラウザ互換性の確認
```

## 🎯 効果的な指示のコツ

### 1. 明確な要件指定

```
❌ 悪い例:
「商品管理画面を作ってください」

✅ 良い例:
「商品管理画面を作ってください。一覧表示（ページネーション付き）、詳細表示、新規作成・編集フォーム、削除確認ダイアログが必要です。レスポンシブ対応で、アクセシビリティ準拠してください」
```

### 2. 技術制約の明示

```
❌ 悪い例:
「データベースを使ってください」

✅ 良い例:
「PostgreSQL 14を使用し、Prisma ORMでスキーマ管理、マイグレーションはTypeScript実装でお願いします」
```

### 3. 品質基準の具体化

```
❌ 悪い例:
「高品質にしてください」

✅ 良い例:
「テストカバレッジ90%以上、ESLintエラー0件、WCAG 2.1 AA準拠、Lighthouseパフォーマンススコア85%以上でお願いします」
```

### 4. 段階的な確認指示

```
✅ 推奨パターン:
「要件分析の結果を確認してから、次のフェーズに進んでください」
「ドメインモデルのエンティティ関係が正しいか検証してください」  
「生成されたUIコンポーネントの品質をチェックしてください」
```

## 🔗 関連ドキュメント

- **[Phase 6 UI/UX Getting Started](../getting-started/PHASE-6-GETTING-STARTED.md)** - Phase 6専用クイックスタート
- **[Claude Code Task Tool Integration](../integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - Task Tool統合仕様
- **[Claude Code Workflow](../integrations/CLAUDECODE-WORKFLOW.md)** - 基本ワークフロー
- **[Quick Start Guide](../getting-started/QUICK-START-GUIDE.md)** - 全般的なクイックスタート
- **[CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)** - CLIコマンドリファレンス

## 💡 まとめ

ae-frameworkでの効果的な開発には以下が重要です：

1. **明確な要件指定** - 機能・技術・品質要件を具体的に
2. **段階的なアプローチ** - フェーズごとの確認と承認
3. **品質基準の明示** - 数値化可能な品質メトリクス
4. **技術制約の明示** - 使用技術・アーキテクチャの指定
5. **監視・テレメトリ活用** - OpenTelemetryでの品質監視

**🤖 Claude Codeでの自然言語指示が最も効果的**。技術詳細よりも「何を作りたいか」と「どんな品質を求めるか」を明確に伝えることが成功の鍵です。

---

**🚀 ae-framework で、効率的で高品質なソフトウェア開発を今すぐ始めましょう！**