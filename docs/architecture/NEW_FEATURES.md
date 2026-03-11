---
docRole: derived
canonicalSource:
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
lastVerified: '2026-03-11'
---
# ae-framework 新機能ガイド

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Highlights of recent features: Steering Documents, Phase State Management, Approval Workflow, and Slash Commands. Includes setup, directory structure, and example templates. See Japanese sections for detailed steps and code snippets.

## 🎉 最新アップデート（Issue #11）

ae-frameworkに以下の強力な新機能が追加されました：

1. **Steering Documents** - プロジェクト全体のコンテキスト管理
2. **Phase State Management** - フェーズ進捗と状態の追跡
3. **Approval Workflow** - 承認ワークフローシステム
4. **Slash Commands** - 統合コマンドインターフェース

---

## 📚 Steering Documents

### 概要
プロジェクトの方向性と共通理解を管理する中央集権的なドキュメントシステムです。

### セットアップ
```text
# Steering Documentsディレクトリの作成
mkdir -p .ae/steering

# コアドキュメントの作成
touch .ae/steering/product.md      # プロダクトビジョン
touch .ae/steering/architecture.md  # アーキテクチャ決定
touch .ae/steering/standards.md     # コーディング標準
```

### ドキュメント構造

#### product.md - プロダクトビジョン
```text
# Product Vision

## Vision Statement
[プロダクトの長期的なビジョン]

## Target Users
- [主要ターゲットユーザー]
- [セカンダリユーザー]

## Core Features
1. [コア機能1]
2. [コア機能2]

## Success Metrics
- [成功指標1]
- [成功指標2]
```

#### architecture.md - アーキテクチャ決定
```text
# Architecture Decisions

## Technology Stack
- Language: TypeScript
- Framework: [選択したフレームワーク]
- Database: [データベース選択]

## Architecture Pattern
- [選択したパターン: マイクロサービス、モノリス等]

## Key Design Decisions
1. [決定1とその理由]
2. [決定2とその理由]
```

#### standards.md - コーディング標準
```text
# Coding Standards

## Naming Conventions
- Classes: PascalCase
- Functions: camelCase
- Constants: UPPER_SNAKE_CASE

## Code Style
- Indentation: 2 spaces
- Line length: 100 characters max

## Testing Requirements
- Minimum coverage: 80%
- Test naming: describe/test structure
```

### カスタムドキュメント
プロジェクト固有のドキュメントも追加可能：

```text
# カスタムドキュメントの追加
echo "# Security Guidelines" > .ae/steering/security.md
echo "# API Design Principles" > .ae/steering/api-design.md
```

### プログラマティックアクセス
```text
import { SteeringLoader } from 'ae-framework/utils';

const loader = new SteeringLoader();

// 全ドキュメントの読み込み
const docs = await loader.loadAllDocuments();

// 特定ドキュメントの読み込み
const productVision = await loader.loadDocument('product');

// ステアリングコンテキストの取得
const context = await loader.getSteeringContext();
```

---

## 📊 Phase State Management

### 概要
6フェーズの進捗を自動追跡し、プロジェクトの状態を管理します。

### CLI使用方法

#### プロジェクトの初期化
```text
# 新規プロジェクトの開始
ae-phase init --name "My Awesome Project"

# 承認不要プロジェクト
ae-phase init --name "Quick Prototype" --no-approvals
```

#### 状態の確認
```text
# 簡易ステータス
ae-phase status

# 詳細レポート
ae-phase status --verbose

# タイムライン表示
ae-phase timeline
```

#### フェーズの管理
```text
# フェーズの開始
ae-phase start intent

# フェーズの完了（成果物を記録）
ae-phase complete intent --artifacts requirements.md user-stories.md

# フェーズの承認
ae-phase approve intent --user "Tech Lead" --notes "Requirements approved"

# 次のフェーズへ移行
ae-phase next

# 特定フェーズの成果物確認
ae-phase artifacts intent
```

#### リセット機能
```text
# 特定フェーズのリセット
ae-phase reset intent --force

# プロジェクト全体のリセット
ae-phase reset --force
```

### プログラマティックアクセス
```text
import { PhaseStateManager } from 'ae-framework/utils';

const manager = new PhaseStateManager();

// プロジェクトの初期化
await manager.initializeProject('My Project', true);

// フェーズの管理
await manager.startPhase('intent');
await manager.completePhase('intent', ['requirements.md']);
await manager.approvePhase('intent', 'John Doe');

// 次のフェーズへ移行
const nextPhase = await manager.transitionToNextPhase();

// 進捗の取得
const progress = await manager.getProgressPercentage();
const timeline = await manager.getPhaseTimeline();
```

---

## ✅ Approval Workflow

### 概要
フェーズ完了後の承認プロセスを管理し、品質ゲートを実装します。

### CLI使用方法

#### 承認リクエスト
```text
# 承認をリクエスト
ae-approve request intent --user "Developer" --summary "Requirements ready for review"

# 承認の実行
ae-approve approve intent --user "Tech Lead" --notes "LGTM"

# 承認の却下
ae-approve reject intent --user "Manager" --reason "Missing security requirements"
```

#### 承認状態の確認
```text
# 保留中の承認一覧
ae-approve pending

# 特定フェーズの承認状態
ae-approve status intent

# 承認履歴
ae-approve history intent
```

#### ポリシー設定
```text
# 複数承認者の要求
ae-approve set-policy code --multiple --min-approvers 2

# タイムアウト設定
ae-approve set-policy verify --timeout 24

# 自動承認条件の設定
ae-approve set-policy test --auto-test --auto-security
```

### 承認ポリシーの種類

#### 自動承認条件
- **test-coverage**: テストカバレッジが閾値を超えた場合
- **code-review**: コードレビューが完了した場合
- **security-scan**: セキュリティスキャンが通過した場合

#### デフォルトポリシー
```text
{
  'intent': { minApprovers: 1, timeoutHours: 48 },
  'formal': { minApprovers: 1, timeoutHours: 48 },
  'test': { 
    minApprovers: 1, 
    autoApproveConditions: [{ type: 'test-coverage', threshold: 80 }],
    timeoutHours: 24 
  },
  'code': { 
    requireMultipleApprovers: true,
    minApprovers: 2,
    timeoutHours: 48 
  },
  'verify': { 
    minApprovers: 1,
    autoApproveConditions: [{ type: 'security-scan' }],
    timeoutHours: 24 
  },
  'operate': { 
    requireMultipleApprovers: true,
    minApprovers: 2,
    timeoutHours: 72 
  }
}
```

### プログラマティックアクセス
```text
import { ApprovalService } from 'ae-framework/services';

const service = new ApprovalService();

// 承認のリクエスト
await service.requestApproval('intent', 'Developer', 'Ready for review');

// 承認の実行
await service.approve('intent', 'Manager', 'Approved with conditions');

// ポリシーの設定
service.setPolicy('code', {
  requireMultipleApprovers: true,
  minApprovers: 2,
  autoApproveConditions: [
    { type: 'test-coverage', threshold: 90 }
  ]
});

// イベントリスナー
service.on('approval:requested', ({ request }) => {
  console.log(`Approval requested for ${request.phase}`);
});

service.on('approval:completed', ({ phase, approvedBy }) => {
  console.log(`${phase} approved by ${approvedBy}`);
});
```

---

## 🚀 Slash Commands

### 概要
すべてのae-framework機能に統一されたコマンドインターフェースを提供します。

### インタラクティブモード
```text
# インタラクティブモードの起動
ae-slash interactive

# または短縮形
ae-slash i
```

インタラクティブモードでは：
- リアルタイムコマンド実行
- コマンド補完とヘルプ
- プロジェクト状態の可視化

### コマンド実行

#### 単一コマンド
```text
# コマンドの実行
ae-slash exec "/init My Project"
ae-slash exec "/status"
ae-slash exec "/intent User must be able to login"
```

#### コマンドシーケンス
```text
# 複数コマンドの連続実行
ae-slash sequence /init /status /next

# より複雑なワークフロー
ae-slash sequence "/init My App" /complete /approve /next
```

#### テキストからのコマンド抽出
```text
# 自然言語からコマンドを抽出
ae-slash parse "Please /init the project and then /status to check"
```

### 利用可能なコマンド

#### フェーズコマンド
| コマンド | エイリアス | 説明 |
|---------|-----------|------|
| `/intent` | `/i`, `/requirements` | 要件分析と意図の抽出 |
| `/formal` | `/f`, `/spec` | 形式仕様の生成 |
| `/test` | `/t`, `/generate-tests` | テストの生成 |
| `/code` | `/c`, `/implement` | コードの実装 |
| `/verify` | `/v`, `/check` | 実装の検証 |
| `/operate` | `/o`, `/deploy` | デプロイと運用 |

#### ワークフローコマンド
| コマンド | エイリアス | 説明 |
|---------|-----------|------|
| `/init` | - | プロジェクトの初期化 |
| `/complete` | - | 現在フェーズの完了 |
| `/approve` | `/a` | 現在フェーズの承認 |
| `/next` | `/n` | 次フェーズへの移行 |
| `/run` | - | 特定フェーズの実行 |

#### 情報コマンド
| コマンド | エイリアス | 説明 |
|---------|-----------|------|
| `/status` | `/s` | プロジェクト状態の表示 |
| `/context` | `/ctx` | 現在のコンテキスト表示 |
| `/timeline` | `/tl` | フェーズタイムライン表示 |

#### ユーティリティコマンド
| コマンド | エイリアス | 説明 |
|---------|-----------|------|
| `/help` | `/h`, `/?` | ヘルプの表示 |
| `/steering` | - | Steering Documents管理 |

### コマンド例

#### プロジェクト開始から実装まで
```text
# インタラクティブモードで
ae-slash i

ae> /init "E-Commerce Platform"
ae> /intent Users can browse products and add them to cart
ae> /complete requirements.md
ae> /approve
ae> /next
ae> /formal openapi
ae> /complete api-spec.yaml
ae> /approve
ae> /next
ae> /test src/cart.ts unit
ae> /complete cart.test.ts
ae> /next
ae> /code cart.test.ts
ae> /verify
```

#### Steering Documents活用
```text
ae> /steering load product
ae> /steering context
ae> /intent [要件がproduct.mdのビジョンに基づいて解析される]
```

### プログラマティックアクセス
```text
import { SlashCommandManager } from 'ae-framework/commands';

const manager = new SlashCommandManager();

// 単一コマンドの実行
const result = await manager.execute('/init My Project');

// コマンドシーケンスの実行
const results = await manager.executeSequence([
  '/init My Project',
  '/status',
  '/complete requirements.md',
  '/approve',
  '/next'
]);

// テキストからコマンドを抽出
const commands = manager.parseCommandFromText(
  'Please /init the project and /status'
);
```

---

## 🔄 統合ワークフロー例

### 完全なプロジェクトサイクル

```text
# 1. プロジェクトの初期化とSteering Documents作成
mkdir my-project && cd my-project
ae-phase init --name "My SaaS Platform"
mkdir -p .ae/steering
echo "# Product Vision\n\nSaaS platform for team collaboration" > .ae/steering/product.md
echo "# Architecture\n\nMicroservices with Node.js" > .ae/steering/architecture.md
echo "# Standards\n\n- TypeScript strict mode\n- 90% test coverage" > .ae/steering/standards.md

# 2. Slash Commandsで開発を進める
ae-slash i
ae> /intent Users can create and share documents in real-time
ae> /complete requirements.md user-stories.md
ae> /approve Development complete for intent phase
ae> /next

# 3. 承認ワークフローの活用
ae-approve request formal --summary "API specifications ready"
ae-approve approve formal --user "Tech Lead" --notes "API design approved"

# 4. 進捗の確認
ae-phase status --verbose
ae-phase timeline

# 5. 次のフェーズへ
ae-slash exec /next
```

### CI/CDパイプラインとの統合

```text
# .github/workflows/ae-framework.yml
name: ae-framework Workflow

on: [push, pull_request]

jobs:
  phase-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      
      - name: Check Phase Status
        run: |
          npx ae-phase status
          npx ae-phase timeline
      
      - name: Run Current Phase
        run: |
          PHASE=$(npx ae-phase status --json | jq -r '.currentPhase')
          npx ae-slash exec "/$PHASE"
      
      - name: Auto-approve if tests pass
        if: success()
        run: |
          npx ae-approve approve $PHASE --user "CI Bot" --notes "All checks passed"
```

---

## 📈 ベストプラクティス

### 1. Steering Documentsの活用
- プロジェクト開始時に必ず作成
- 定期的に更新とレビュー
- すべてのステークホルダーがアクセス可能に

### 2. Phase State Managementの運用
- 各フェーズで成果物を必ず記録
- 承認プロセスを省略しない
- タイムラインを定期的にレビュー

### 3. Approval Workflowの設定
- プロジェクトの重要度に応じてポリシー調整
- 自動承認条件を適切に設定
- タイムアウトを現実的な値に

### 4. Slash Commandsの効率的な使用
- よく使うコマンドシーケンスをスクリプト化
- エイリアスを活用して入力を短縮
- インタラクティブモードでの探索的開発

---

## 🆘 トラブルシューティング

### Phase State関連
```text
# 状態ファイルの確認
cat .ae/phase-state.json

# 破損した状態のリセット
ae-phase reset --force

# 特定フェーズのやり直し
ae-phase reset intent --force
ae-phase start intent
```

### Approval関連
```text
# 期限切れ承認のクリーンアップ
ae-approve check-expired

# 承認履歴の確認
ae-approve history intent

# ポリシーのリセット
ae-approve set-policy intent --timeout 48
```

### Slash Commands関連
```text
# コマンドリストの確認
ae-slash list

# 特定カテゴリのコマンドのみ表示
ae-slash list --category phase

# コマンドのヘルプ
ae-slash help /intent
```

---

## 📚 詳細情報

- [API リファレンス](../reference/API.md)
- [設定ガイド](../getting-started/SETUP.md)
- [コントリビューションガイド](../../CONTRIBUTING.md)
- [Issue #11 Implementation Details](https://github.com/itdojp/ae-framework/issues/11)
