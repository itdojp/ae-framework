# 🚀 ae-framework クイックスタートガイド

Claude Code で今すぐ始める ae-framework！
**15分で最初のプロジェクトを完全自動化**

## ⚡ 5分で始める最短セットアップ

### 1. Claude Code で ae-framework を有効化

**Claude Code の設定画面で以下を追加:**

```json
{
  "mcpServers": {
    "ae-framework": {
      "command": "npx",
      "args": ["tsx", "/path/to/ae-framework/src/mcp-server/intent-server.ts"],
      "cwd": "/path/to/ae-framework"
    }
  }
}
```

### 2. 即座に使える基本コマンド

Claude Code で以下のように話しかけるだけ：

```
「ae-frameworkを使ってログイン機能を作ってください」
```

**→ 自動的に6フェーズで完全開発！**

---

## 📱 実践例：5分でTODOアプリ完成

### ステップ1: 要件を話すだけ
```
ユーザー: TODOアプリを作りたいです。基本的な機能で良いので、ae-frameworkで開発してください。

必要な機能:
- タスクの追加・削除
- 完了状態の切り替え
- シンプルなUI
```

### ステップ2: Claude Code が自動実行
```
Claude: ae-frameworkで段階的に開発します。

Phase 1: 要件分析中...
✓ 機能要件5件を特定
✓ 非機能要件3件を特定  
✓ ユーザーストーリー8件を生成

Phase 2: 形式仕様生成中...
✓ TLA+仕様を自動生成
✓ 状態遷移図を作成
✓ API仕様を定義

Phase 3: テスト自動生成中...
✓ ユニットテスト18件
✓ E2Eテスト8件  
✓ 視覚回帰テスト12件
✓ AI選択により実行時間2分30秒に最適化

Phase 4: コード自動生成中...
✓ React + TypeScript
✓ Express.js バックエンド
✓ SQLite データベース
✓ TDD完全準拠

Phase 5: 品質検証中...
✓ テストカバレッジ 92%
✓ セキュリティ監査 合格
✓ パフォーマンス検証 合格
✓ 品質スコア 96/100

Phase 6: デプロイ準備完了
✓ Docker設定自動生成
✓ CI/CD パイプライン設定
✓ 監視・アラート設定
```

### ステップ3: 完成したアプリの確認

**生成されるファイル構成:**
```
todo-app/
├── frontend/
│   ├── src/
│   │   ├── components/TodoList.tsx
│   │   ├── components/TodoItem.tsx
│   │   └── App.tsx
│   └── tests/
│       ├── TodoList.test.tsx
│       └── e2e/todo-flow.spec.ts
├── backend/
│   ├── src/
│   │   ├── routes/todos.ts
│   │   ├── models/Todo.ts
│   │   └── app.ts
│   └── tests/
│       └── todos.test.ts
├── docker-compose.yml
└── .github/workflows/ci.yml
```

**即座に起動:**
```bash
cd todo-app
npm install
npm run dev
```

**🎉 完成！ブラウザで http://localhost:3000 を開く**

---

## 🎯 よくある開発シナリオ

### シナリオ1: 既存プロジェクトに機能追加

```
ユーザー: 既存のECサイトにレビュー機能を追加したいです。ae-frameworkで影響範囲を分析して安全に追加してください。

Claude: Sequential推論エンジンで影響分析を実行します...

[分析結果]
影響を受けるコンポーネント:
- Product Service (中影響)
- User Service (低影響) 
- Database Schema (新テーブル追加)

推奨アプローチ:
1. 新しいReview Serviceとして独立実装
2. 既存APIとの疎結合設計
3. データベース移行は段階的実行

生成されるコード:
- ReviewService.ts (新規)
- ProductService.ts (最小限の変更)
- データベース移行スクリプト
- 38件の自動テスト (既存テストの94%は変更不要)

実装時間見積もり: 4時間
リスク評価: 低リスク
```

### シナリオ2: レガシーシステムの部分モダナイゼーション

```
ユーザー: 古いPHPシステムの認証部分だけをNode.jsでモダンにしたいです。

Claude: 段階的移行戦略を提案します...

Phase 1: 要件抽出
✓ 既存PHP認証システムの分析
✓ 移行範囲の特定
✓ データ連携方式の設計

Phase 2: 移行設計  
✓ Strangler Fig パターンでの設計
✓ データベース共有戦略
✓ セッション連携方式

Phase 3: 並行テスト戦略
✓ PHP/Node.js両方での検証
✓ データ整合性テスト
✓ パフォーマンス比較テスト

Phase 4: 段階的実装
✓ 新認証サービス (Node.js)
✓ 既存システム連携API
✓ ログイン画面の段階的切り替え

Phase 5: 品質保証
✓ 既存機能の回帰テスト
✓ セキュリティ監査
✓ パフォーマンス検証

移行完了までの見積もり: 2週間
リスク: 中リスク (適切な監視により軽減)
```

### シナリオ3: マイクロサービス分割

```
ユーザー: モノリスなWebアプリをマイクロサービスに分割したいです。どこから始めれば良いですか？

Claude: Sequential推論エンジンでマイクロサービス分割戦略を分析します...

[分析結果]
推奨分割順序:
1. User Service (独立度: 高, 影響: 低)
2. Notification Service (独立度: 高, 影響: 低)  
3. Payment Service (独立度: 中, 影響: 中)
4. Order Service (独立度: 低, 影響: 高)

第1段階: User Service分離
- 推定工数: 1週間
- リスク: 低
- 依存関係: 最小限
- 自動生成されるコンポーネント:
  * User microservice (独立実行)
  * API Gateway設定
  * データ同期機能
  * 包括的テストスイート

実装開始しますか？
```

---

## 🔧 便利なワンライナーコマンド

### 即座に使える便利コマンド

```bash
# 🔍 プロジェクト全体分析
「/ae:analyze . --depth=deep --security --performance」

# 📝 API文書自動生成  
「/ae:document ./src --type=api --include-examples」

# 🚀 パフォーマンス最適化提案
「/ae:improve ./src --focus=performance --auto-fix」

# 🧪 スマートテスト選択
「重要な変更があったファイルだけテストを実行してください」

# 🔒 セキュリティ監査
「/ae:verify security --full-scan --generate-report」

# 📊 品質レポート生成
「/ae:verify all --export=report.pdf」
```

---

## 🎨 カスタマイズ例

### プロジェクト固有の設定

```typescript
// ae-framework.config.ts
export default {
  phases: {
    intent: {
      domain: "e-commerce",
      templates: ["./templates/ecommerce-requirements.json"],
      aiModel: "claude-3-sonnet"
    },
    formal: {
      specFormat: "tla+",
      generateDiagrams: true,
      validationLevel: "strict"
    },
    test: {
      framework: "vitest",
      coverage: { target: 90 },
      intelligentSelection: {
        strategy: "risk_based",
        maxExecutionTime: 300
      }
    },
    code: {
      language: "typescript",
      framework: "next.js",
      architecture: "clean-architecture"
    }
  }
}
```

### チーム固有のコマンドエイリアス

```json
{
  "aliases": {
    "analyze-api": "/ae:analyze ./src/api --security --performance",
    "quick-test": "/ae:test select-intelligent --strategy=balanced --max-time=120",
    "deploy-check": "/ae:verify all --deployment-ready=true",
    "generate-docs": "/ae:document . --type=all --format=markdown"
  }
}
```

---

## 📊 成果の可視化

### 開発メトリクス自動収集

```
日次開発レポート (ae-framework使用):

📈 生産性指標:
- コード生成速度: 1,200行/時間 (従来: 200行/時間)
- バグ密度: 0.1件/1000行 (従来: 2.3件/1000行)
- テスト網羅率: 91% (従来: 67%)

⏱️ 時間短縮:
- 要件分析: 80%短縮 (2日→4時間)
- テスト作成: 90%短縮 (1日→1時間)
- コードレビュー: 70%短縮 (4時間→1.2時間)

🎯 品質向上:
- 形式仕様準拠率: 98%
- セキュリティ基準準拠: 100%  
- パフォーマンス要件達成: 95%
```

---

## 🚨 よくある質問とトラブルシューティング

### Q: 大規模プロジェクトでも使えますか？

**A:** はい！Phase 3.3の統合最適化システムが大規模対応しています。

```
実績例:
- 100万行超のプロジェクトで75%時間短縮
- マイクロサービス15個の並行開発
- チーム20人での協調開発
```

### Q: 既存のCIパイプラインと統合できますか？

**A:** 完全対応しています。

```yaml
# GitHub Actions例
- name: ae-framework Quality Check
  run: npx ae-verify all --ci-mode=true --export-junit
  
- name: Intelligent Test Selection  
  run: npx ae-test select-intelligent --changes="${{ github.event.commits }}"
```

### Q: 学習コストはどの程度ですか？

**A:** 非常に低く設定されています。

```
学習スケジュール:
Day 1: 基本的な対話でPhase 1-2を体験
Day 2: Phase 3のテスト生成を実践  
Day 3: Phase 4-6で完全サイクル体験
Week 2: チーム導入と本格運用開始

必要な前提知識:
- TypeScript基礎知識
- 基本的な開発プロセス理解
- Claude Code の使用経験
```

---

## 🎉 次のステップ

### 1. 今すぐ始める
```
Claude Code で以下を入力:
「ae-frameworkのサンプルプロジェクトを作成してください」
```

### 2. 本格導入
1. 既存プロジェクトの一部機能で試用
2. 開発プロセスに段階的統合  
3. チーム全体での本格運用

### 3. 上級活用
- SuperClaude Framework による70%効率化
- Phase 3.3 統合最適化の本格活用
- カスタムエージェント開発

---

## 💬 コミュニティ・サポート

**GitHub Issues**: バグ報告・機能要望  
**Discord**: リアルタイム質問・情報交換  
**定期Webinar**: 実践テクニック共有  

**🤖 ae-framework で、開発の未来を今すぐ体験してください！**