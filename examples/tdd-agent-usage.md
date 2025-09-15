# TDD Agent/Subagent Usage Examples

> 🌍 Language / 言語: English | 日本語

## 🤖 MCPサーバー vs サブエージェント vs CLI の比較

| 特徴 | MCP サーバー | Claude Code サブエージェント | CLI Tool |
|------|--------------|------------------------------|----------|
| **対話性** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ |
| **リアルタイム** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐ |
| **知的判断** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ |
| **自動化** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **スクリプタビリティ** | ⭐⭐ | ⭐ | ⭐⭐⭐⭐⭐ |

## 🚀 実装アプローチ

### 1. Claude Code Task Tool 統合 (推奨)

```typescript
// 使用例: Claude Code内での利用
const taskRequest: TaskRequest = {
  description: "TDD guidance for user authentication",
  prompt: "I need to implement user authentication with password hashing. Guide me through the TDD approach.",
  subagent_type: "tdd-guide"
};

const response = await handleTDDTask(taskRequest);
// Claude Code が自動的に段階的なTDD指導を提供
```

**利点:**
- Claude Codeの文脈理解と統合
- リアルタイム対話型ガイダンス
- プロジェクト状態の継続的把握
- 知的な判断と適応

### 2. MCP サーバー実装

```bash
# MCPサーバーとして起動
npm run mcp-server

# Claude Desktop等から利用
{
  "mcpServers": {
    "tdd-guard": {
      "command": "node",
      "args": ["dist/mcp-server/tdd-server.js"]
    }
  }
}
```

**利点:**
- Claude環境全体で利用可能
- 標準化されたインターフェース
- 他のツールとの統合が容易

### 3. ハイブリッドアプローチ (最強)

```typescript
const hybridSystem = createHybridTDDSystem({
  enableCLI: true,
  enableClaudeCodeIntegration: true,
  enforceRealTime: true,
  strictMode: true
});

// 自動的に最適な方法を選択
const result = await hybridSystem.handleTDDRequest({
  type: 'auto',
  data: { feature: 'user authentication' },
  context: { isClaudeCode: true, hasTaskTool: true }
});
```

## 📝 実際の使用シナリオ

### シナリオ 1: 新機能開発

**従来のCLIアプローチ:**
```bash
$ ae-framework check --phase 3-tests
❌ No test files found
$ ae-framework guard --name "TDD Guard"  
❌ TDD Guard failed: src/auth.ts has no corresponding test
```

**サブエージェント/MCPアプローチ:**
```
User: "認証機能を実装したい"

TDD Agent: "認証機能の実装をTDDアプローチで進めましょう。まず以下の段階で進めます：

## 🔴 RED Phase (現在)
1. **テストファイル作成**: `tests/auth.test.ts`
2. **失敗テスト作成**: 期待する認証動作を記述
3. **テスト実行**: 失敗することを確認

## 💡 推奨テストケース
- パスワードハッシュ化の検証
- 無効な認証情報の処理
- セッション管理
- レート制限

まず `tests/auth.test.ts` を作成しましょうか？"

User: "はい"

TDD Agent: [authService.test.ts を作成]

"テストファイルを作成しました。これらのテストは現在 **RED** (失敗) 状態です。
次に `npm test` を実行して、期待通りに失敗することを確認してください。"
```

### シナリオ 2: リアルタイム違反検出

**従来のアプローチ:**
```bash
# ユーザーがコードを書いた後に気づく
$ git commit
❌ Pre-commit hook failed: Tests required for new source files
```

**エージェント/MCPアプローチ:**
```
# ファイル作成の瞬間に介入
TDD Agent: "🚨 TDD違反を検出しました！

`src/payment.ts` が作成されましたが、対応するテストファイルがありません。

## 🛠️ 修正手順
1. まず `tests/payment.test.ts` を作成
2. 決済機能の期待動作をテストで記述
3. テストが失敗することを確認
4. その後で実装を開始

## 💡 提案するテスト構造
```typescript
describe('PaymentService', () => {
  it('should process valid payment', () => {
    // 正常な決済処理のテスト
  });
  
  it('should reject invalid card', () => {
    // 無効なカードの拒否テスト
  });
});
```

テストファイルを先に作成しますか？"
```

### シナリオ 3: コード分析と改善提案

**サブエージェント版:**
```
User: "このコードをレビューしてTDD観点から改善点を教えて"

TDD Agent: "コードを分析しました。TDD観点から以下の改善点があります：

## 📊 分析結果
- **テストカバレッジ**: 65% (推奨: 80%以上)
- **未テスト関数**: 3個
- **複雑度**: 高 (分割を推奨)

## 🎯 優先改善項目
1. **高優先度**: `validatePayment()` にテストを追加
2. **中優先度**: エラーハンドリングのテスト強化  
3. **低優先度**: エッジケースの追加テスト

## 💡 推奨テスト追加
```typescript
// 追加すべきテスト
it('should validate payment amount limits', () => {
  expect(() => validatePayment({ amount: -100 }))
    .toThrow('Invalid amount');
});
```

これらのテストを追加して、カバレッジを80%以上にしましょう。"
```

## 🔧 技術的実装の比較

### CLI実装
- **シンプル**: 既存ツールとの統合が容易
- **確実**: スクリプト化可能な確実性
- **限定的**: 文脈理解や適応力が制限される

### MCP サーバー実装  
- **標準化**: MCP規格による互換性
- **拡張性**: 他のツールとの連携が容易
- **ポータブル**: Claude環境全体で利用可能

### サブエージェント実装
- **知的**: 文脈理解と適応的な指導
- **対話的**: リアルタイム会話型ガイダンス
- **統合性**: Claude Codeとの深い統合

## 🎯 推奨戦略

### Phase 1: Immediate (サブエージェント)
Claude Code限定で、Task toolを使った対話型TDDガイダンスを実装。
ユーザーの開発フローに自然に統合。

### Phase 2: Expansion (MCP)
MCPサーバーとして実装し、Claude Desktop等の他環境でも利用可能に。
標準化されたインターフェースで拡張性を確保。

### Phase 3: Complete (Hybrid)
CLI、MCP、サブエージェントを統合したハイブリッドシステム。
環境とユーザー設定に応じて最適な方法を自動選択。

## 💫 期待される効果

1. **TDD遵守率**: 95%以上の向上
2. **開発効率**: リアルタイムガイダンスによる迷いの削減
3. **コード品質**: テストファーストによる設計改善
4. **学習効果**: 対話的指導による理解促進

このアプローチにより、TDDは「面倒なルール」から「自然な開発フロー」に変化します。
