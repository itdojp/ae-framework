---
docRole: narrative
lastVerified: '2026-03-12'
---
# ae-framework 全体のエージェント/MCPサーバー化提案

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Proposal to implement all six phases as MCP servers/sub‑agents for AI‑native development workflows, enabling automation, intelligent validation, knowledge sharing, and real‑time feedback. See Japanese sections for detailed API sketches and design.

## 🎯 エグゼクティブサマリー

ae-frameworkの6フェーズすべてをMCPサーバー/サブエージェントとして実装することで、**AIネイティブな開発プロセス**を実現し、開発効率と品質を劇的に向上させることが可能です。

## 📊 現状分析と課題

### 現在のae-frameworkの課題
1. **手動プロセス依存**: 各フェーズの遷移が人手に依存
2. **検証の不完全性**: 成果物の品質チェックが不十分
3. **知識の属人化**: ベストプラクティスが共有されない
4. **フィードバック遅延**: 問題発見が後工程になりがち

### エージェント化による解決
- **自動化**: フェーズ遷移の自動判断と実行
- **知的検証**: AIによる成果物の品質保証
- **知識共有**: ベストプラクティスの自動適用
- **即時フィードバック**: リアルタイム問題検出

## 🏗️ フェーズ別エージェント設計

### Phase 1: Intent Agent (要件定義エージェント)

**役割**: 要件の明確化と仕様の自動生成

```typescript no-doctest
interface IntentAgent {
  // 自然言語から要件を抽出
  extractRequirements(userInput: string): Requirements;
  
  // 曖昧性を検出して質問生成
  detectAmbiguity(requirements: Requirements): ClarificationQuestions[];
  
  // API仕様を自動生成
  generateOpenAPISpec(requirements: Requirements): OpenAPISpec;
  
  // 非機能要件を推論
  inferNonFunctionalRequirements(context: ProjectContext): NFRs;
}
```

**MCPツール例**:
```json no-doctest
{
  "name": "analyze_requirements",
  "description": "Analyze and structure user requirements",
  "input": "I want to build a real-time chat application with end-to-end encryption"
}
```

**メリット**:
- ✅ 要件の曖昧性を早期発見
- ✅ 標準フォーマットへの自動変換
- ✅ 類似プロジェクトからの知見活用
- ✅ ステークホルダー間の認識齟齬防止

### Phase 2: Formal Agent (形式仕様エージェント)

**役割**: 形式仕様の自動生成と検証

```typescript no-doctest
interface FormalAgent {
  // TLA+仕様を生成
  generateTLASpec(requirements: Requirements): TLASpecification;
  
  // 状態遷移図を作成
  createStateMachine(behavior: BehaviorSpec): StateMachine;
  
  // 不変条件を検証
  verifyInvariants(spec: TLASpecification): VerificationResult;
  
  // デッドロック検出
  detectDeadlocks(stateMachine: StateMachine): DeadlockAnalysis;
}
```

**サブエージェント使用例**:
```
User: "ユーザー認証の状態遷移を設計して"

Formal Agent: "認証フローの形式仕様を作成します：

## 状態定義
- Unauthenticated (初期状態)
- Authenticating (認証中)
- Authenticated (認証済み)
- Failed (認証失敗)

## TLA+仕様生成中...
[TLA+コードを自動生成]

## 検証結果
✅ デッドロックなし
✅ 不変条件を満たす
⚠️ タイムアウト処理が未定義

修正を適用しますか？"
```

**メリット**:
- ✅ 形式手法の専門知識不要
- ✅ 自動的な仕様検証
- ✅ 設計段階でのバグ発見
- ✅ 数学的保証の獲得

### Phase 3: Test Agent (テスト設計エージェント) 

**役割**: 包括的なテスト戦略の立案と実装

```typescript no-doctest
interface TestAgent {
  // テストケースを自動生成
  generateTestCases(spec: Specification): TestCase[];
  
  // Property-Based Testingの設計
  designPropertyTests(contracts: Contract[]): PropertyTest[];
  
  // BDDシナリオを作成
  createBDDScenarios(userStories: UserStory[]): GherkinScenario[];
  
  // テストカバレッジ分析
  analyzeTestCoverage(tests: TestCase[]): CoverageReport;
  
  // ミューテーションテスト設計
  designMutationTests(code: SourceCode): MutationTest[];
}
```

**実装例**:
```typescript no-doctest
// テストエージェントが自動生成するテスト
describe('Payment Processing', () => {
  // 正常系
  it('should process valid payment', () => {
    // エージェントが要件から自動生成
  });
  
  // 異常系 - エージェントが推論
  it('should handle insufficient funds', () => {
    // エッジケースを自動検出
  });
  
  // Property-Based - エージェントが設計
  property('payment amount invariants', () => {
    // 数学的性質を自動導出
  });
});
```

**メリット**:
- ✅ テストケースの網羅性向上
- ✅ エッジケースの自動発見
- ✅ テスト設計の標準化
- ✅ 回帰テストの自動更新

### Phase 4: Code Agent (実装エージェント)

**役割**: 仕様準拠のコード生成と最適化

```typescript no-doctest
interface CodeAgent {
  // 仕様からコード生成
  generateCode(spec: Specification, tests: TestCase[]): SourceCode;
  
  // アーキテクチャパターン適用
  applyPatterns(code: SourceCode, patterns: Pattern[]): SourceCode;
  
  // パフォーマンス最適化
  optimizePerformance(code: SourceCode): OptimizedCode;
  
  // セキュリティ脆弱性検出
  detectVulnerabilities(code: SourceCode): SecurityIssue[];
  
  // リファクタリング提案
  suggestRefactoring(code: SourceCode): RefactoringPlan;
}
```

**対話型実装支援**:
```
Code Agent: "テストから以下の実装を推論しました：

```typescript no-doctest
class PaymentService {
  async processPayment(amount: number, cardToken: string) {
    // 1. 金額検証（テストから推論）
    if (amount <= 0) throw new InvalidAmountError();
    
    // 2. カード検証（セキュリティパターン適用）
    const card = await this.validateCard(cardToken);
    
    // 3. 決済処理（エラーハンドリング自動追加）
    try {
      return await this.gateway.charge(card, amount);
    } catch (error) {
      // 自動リトライロジック
      return this.handlePaymentError(error);
    }
  }
}
```

この実装で問題ありませんか？"
```

**メリット**:
- ✅ テスト駆動の確実な実装
- ✅ ベストプラクティスの自動適用
- ✅ セキュリティの組み込み
- ✅ 一貫したコーディングスタイル

### Phase 5: Verify Agent (検証エージェント)

**役割**: 包括的な品質検証と改善提案

```typescript no-doctest
interface VerifyAgent {
  // トレーサビリティ検証
  verifyTraceability(artifacts: ProjectArtifacts): TraceabilityMatrix;
  
  // 契約プログラミング検証
  verifyContracts(code: SourceCode): ContractViolation[];
  
  // パフォーマンステスト
  runPerformanceTests(system: System): PerformanceReport;
  
  // セキュリティ監査
  auditSecurity(system: System): SecurityAuditReport;
  
  // コンプライアンスチェック
  checkCompliance(system: System, regulations: Regulation[]): ComplianceReport;
}
```

**統合検証ダッシュボード**:
```
Verify Agent: "## 検証レポート

### ✅ 機能要件: 100% 達成
- 全ユーザーストーリー実装完了
- 受け入れテスト合格

### ⚠️ 非機能要件: 85% 達成
- パフォーマンス: 目標値の90%
- 可用性: SLA 99.9%達成
- スケーラビリティ: 要改善

### 🔒 セキュリティ
- 脆弱性: 0件
- OWASP Top 10: 対策済み
- ペネトレーションテスト: 合格

### 📊 品質メトリクス
- コードカバレッジ: 92%
- 循環的複雑度: 平均3.2
- 技術的負債: 2.3日分

改善提案を確認しますか？"
```

**メリット**:
- ✅ 360度の品質保証
- ✅ 早期問題発見
- ✅ 継続的改善サイクル
- ✅ 規制準拠の自動化

### Phase 6: Operate Agent (運用エージェント)

**役割**: 本番環境の自動管理と最適化

```typescript no-doctest
interface OperateAgent {
  // デプロイメント戦略決定
  planDeployment(system: System, environment: Environment): DeploymentPlan;
  
  // 監視設定の自動生成
  configureMonitoring(system: System): MonitoringConfig;
  
  // インシデント対応
  handleIncident(alert: Alert): IncidentResponse;
  
  // キャパシティプランニング
  planCapacity(metrics: Metrics, forecast: Forecast): CapacityPlan;
  
  // コスト最適化
  optimizeCosts(infrastructure: Infrastructure): CostOptimization;
}
```

**プロアクティブ運用支援**:
```
Operate Agent: "🚨 異常検知アラート

## 検出内容
- APIレスポンス時間が通常の3倍
- エラー率が閾値を超過

## 自動分析結果
- 原因: データベースのスロークエリ
- 影響: ユーザー体験の劣化

## 推奨アクション
1. 即時: クエリキャッシュ有効化 [実行]
2. 短期: インデックス追加 [計画]
3. 長期: データベース最適化 [検討]

自動修復を実行しますか？"
```

**メリット**:
- ✅ 24/7自動運用
- ✅ プロアクティブな問題解決
- ✅ コスト最適化
- ✅ SLA保証の向上

## 🎭 統合オーケストレーターエージェント

全フェーズを統括する**マスターエージェント**:

```typescript no-doctest
interface OrchestratorAgent {
  // プロジェクト全体の管理
  manageProject(requirements: string): ProjectPlan;
  
  // フェーズ間の調整
  coordinatePhases(currentPhase: Phase): NextAction;
  
  // 進捗追跡とレポート
  trackProgress(): ProgressReport;
  
  // リスク管理
  assessRisks(): RiskAssessment;
  
  // 意思決定支援
  recommendDecisions(context: Context): Decision[];
}
```

## 💡 実装アプローチ比較

| アプローチ | 実装難易度 | 効果 | 適用範囲 | 推奨度 |
|-----------|-----------|------|----------|--------|
| **個別MCPサーバー** | ⭐⭐ | ⭐⭐⭐ | 特定フェーズ | 中 |
| **統合MCPサーバー** | ⭐⭐⭐ | ⭐⭐⭐⭐ | 全フェーズ | 高 |
| **Claude Codeサブエージェント** | ⭐ | ⭐⭐⭐⭐⭐ | Claude限定 | 最高 |
| **ハイブリッド（MCP+サブ）** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 全環境 | 高 |
| **スタンドアロンAI** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | 独立環境 | 低 |

## 🚀 段階的導入ロードマップ

### Phase 1: Quick Wins (1-2ヶ月)
1. **TDD Agent** ✅ (実装済み)
2. **Test Agent** - テスト自動生成
3. **Intent Agent** - 要件整理支援

### Phase 2: Core Automation (3-4ヶ月)
4. **Code Agent** - 実装支援
5. **Verify Agent** - 品質検証
6. **Formal Agent** - 仕様生成

### Phase 3: Full Integration (5-6ヶ月)
7. **Operate Agent** - 運用自動化
8. **Orchestrator Agent** - 統合管理
9. **Analytics Agent** - 分析・改善

## 📈 期待される効果

### 定量的効果
- **開発速度**: 2-3倍向上
- **バグ削減**: 70-80%減少
- **ドキュメント作成**: 90%自動化
- **テストカバレッジ**: 95%以上達成
- **デプロイ頻度**: 10倍向上

### 定性的効果
- **開発者体験の向上**: AIペアプログラミング
- **品質の一貫性**: ベストプラクティスの確実な適用
- **知識の民主化**: 専門知識不要で高度な手法を活用
- **イノベーション促進**: ルーチン作業からの解放

## 🎯 優先実装推奨

### 最優先（即効性大）
1. **Test Agent**: テスト設計の自動化
2. **Code Agent**: 実装支援
3. **Verify Agent**: 品質保証

### 次優先（基盤強化）
4. **Intent Agent**: 要件管理
5. **Formal Agent**: 設計検証

### 将来展望
6. **Operate Agent**: 運用自動化
7. **Orchestrator**: 統合管理

## 🔮 将来ビジョン

### 自律的開発システム
```
Developer: "決済機能を追加したい"

AI Orchestra: "決済機能の実装を開始します。

Phase 1: 要件分析中... ✅
- PCI DSS準拠が必要
- 3Dセキュア対応を推奨

Phase 2: 形式仕様生成中... ✅
- 状態遷移モデル作成
- デッドロックなし確認

Phase 3: テスト設計中... ✅
- 42個のテストケース生成
- セキュリティテスト含む

Phase 4: 実装中... ✅
- テスト駆動で実装
- セキュリティパターン適用

Phase 5: 検証中... ✅
- 全テスト合格
- パフォーマンス基準達成

Phase 6: デプロイ準備完了 ✅
- ステージング環境でテスト済み
- 本番デプロイ可能

完了しました。レビューしますか？"
```

## 結論

ae-framework全体のエージェント化は、**開発プロセスの革命的な進化**をもたらします。特にClaude Codeのサブエージェントとしての実装は、即座に価値を提供でき、段階的な拡張が可能です。

**推奨アクション**:
1. Test Agentの即時実装
2. Code Agentのプロトタイプ開発
3. 段階的な統合と学習
