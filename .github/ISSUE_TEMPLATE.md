# Extended Commands Design Unification

## 概要
現在の拡張コマンド（analyze, document, improve, troubleshoot）の設計を統一し、メンテナンス性と一貫性を向上させる。

## 現在の問題点

### 設計の不統一
- 各コマンドが独自の結果型を持っている
- インターフェースが統一されていない
- エラーハンドリングが各コマンドで異なる

### コードの重複
- EvidenceValidator統合パターンが各コマンドで繰り返し
- 共通的なオプション解析が重複実装
- ファイル走査ロジックの重複

### メンテナンス性の課題
- 新機能追加時に4つのファイルを修正する必要
- 一貫性を保つのが困難
- テストコードも重複している

## 提案する統一設計

### 1. 基底クラスの導入
```typescript
export abstract class BaseExtendedCommand {
  // 共通機能
  // - 引数検証
  // - オプション解析  
  // - エラーハンドリング
  // - Evidence統合
  // - メトリクス収集
}
```

### 2. 統一データ型
```typescript
// 共通インターフェース
export interface UnifiedResult {
  target: AnalysisTarget;
  summary: string;
  issues: Issue[];
  suggestions: Suggestion[];
  metrics: Metrics;
  metadata: CommandMetadata;
}
```

### 3. 専門特化型
```typescript
// 各コマンド専用の拡張
export interface CodeAnalysis extends UnifiedResult { /* ... */ }
export interface DocumentationResult extends UnifiedResult { /* ... */ }
export interface ImprovementResult extends UnifiedResult { /* ... */ }
export interface TroubleshootResult extends UnifiedResult { /* ... */ }
```

## 期待される効果

### メンテナンス性の向上
- コードの重複を90%削減
- 統一されたエラーハンドリング
- 共通機能の一元管理

### 一貫性の向上
- 統一されたインターフェース
- 標準化されたデータ構造
- 予測可能な動作パターン

### 拡張性の向上
- 新しいコマンドの追加が容易
- 機能の横断的追加が簡単
- プラグイン形式での拡張が可能

## 実装計画

### Phase 1: 基盤の実装 ✅
- [x] BaseExtendedCommand基底クラス
- [x] 統一データ型（types.ts）
- [x] UnifiedAnalyzeCommandの実装例

### Phase 2: 段階的移行
- [ ] UnifiedDocumentCommandの実装
- [ ] UnifiedImproveCommandの実装  
- [ ] UnifiedTroubleshootCommandの実装
- [ ] テストの更新と実行

### Phase 3: 統合とクリーンアップ
- [ ] SlashCommandManagerの更新
- [ ] 旧コマンドの削除
- [ ] ドキュメントの更新
- [ ] 最終テストとリリース

## 技術仕様

### ファイル構成
```
src/commands/extended/
├── base-command.ts          # 基底クラス
├── types.ts                 # 統一データ型
├── analyze-command.ts       # 統一版
├── document-command.ts      # 統一版
├── improve-command.ts       # 統一版
├── troubleshoot-command.ts  # 統一版
└── index.ts                # エクスポート
```

### 互換性
- 既存のAPIとの後方互換性を維持
- 段階的移行による安定性確保
- 既存テストの継続実行

## 受け入れ基準

- [ ] 全コマンドが統一インターフェースを使用
- [ ] 既存機能の100%互換性
- [ ] コードカバレッジ90%以上維持
- [ ] パフォーマンス劣化なし
- [ ] ドキュメント更新完了

## リスク評価

### 低リスク
- 段階的実装により安定性確保
- 既存機能への影響を最小化

### 軽減策
- 包括的テストの実行
- 旧コードとの並行動作期間の設定
- レビュープロセスの強化

## 関連ISSUE
- Issue #17: Evidence-based Validation System
- PR #20: Phase 1-3 Evidence-based Validation System

## 優先度
High - メンテナンス性の大幅改善とコード品質向上