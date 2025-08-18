# ae-framework API リファレンス

## 📦 パッケージ構成

```
ae-framework/
├── src/
│   ├── agents/           # AIエージェント
│   ├── cli/              # CLIツール
│   ├── commands/         # Slash Commands
│   ├── services/         # サービス層
│   ├── utils/            # ユーティリティ
│   └── mcp-server/       # MCPサーバー
└── tests/                # テストスイート
```

## 🔧 Core APIs

### SteeringLoader

Steering Documentsの読み込みと管理を行うクラス。

```typescript
import { SteeringLoader } from 'ae-framework/utils';

const loader = new SteeringLoader(projectRoot?: string);

// メソッド
await loader.loadDocument(documentName: string): Promise<string | null>
await loader.loadAllDocuments(): Promise<Record<string, string>>
await loader.loadCoreDocuments(): Promise<Record<string, string>>
await loader.loadCustomDocuments(): Promise<Record<string, string>>
await loader.getSteeringContext(): Promise<string>
await loader.hasSteeringDocuments(): Promise<boolean>
```

#### 使用例

```typescript
const loader = new SteeringLoader();

// 特定のドキュメントを読み込む
const productDoc = await loader.loadDocument('product');

// すべてのドキュメントを読み込む
const allDocs = await loader.loadAllDocuments();
console.log(allDocs.product);
console.log(allDocs.architecture);
console.log(allDocs.standards);

// ステアリングコンテキストを取得
const context = await loader.getSteeringContext();
```

### PhaseStateManager

プロジェクトのフェーズ状態を管理するクラス。

```typescript
import { PhaseStateManager, PhaseType } from 'ae-framework/utils';

const manager = new PhaseStateManager(projectRoot?: string);

// メソッド
await manager.initializeProject(projectName?: string, approvalsRequired?: boolean): Promise<PhaseState>
await manager.loadState(): Promise<PhaseState | null>
await manager.getCurrentState(): Promise<PhaseState | null>
await manager.startPhase(phase: PhaseType): Promise<void>
await manager.completePhase(phase: PhaseType, artifacts: string[]): Promise<void>
await manager.approvePhase(phase: PhaseType, approvedBy: string, notes?: string): Promise<void>
await manager.canTransitionToNextPhase(): Promise<boolean>
await manager.transitionToNextPhase(): Promise<PhaseType | null>
await manager.getProgressPercentage(): Promise<number>
await manager.getPhaseTimeline(): Promise<TimelineEntry[]>
await manager.addMetadata(key: string, value: any): Promise<void>
await manager.generateStatusReport(): Promise<string>
await manager.resetPhase(phase: PhaseType): Promise<void>
```

#### 型定義

```typescript
type PhaseType = 'intent' | 'formal' | 'test' | 'code' | 'verify' | 'operate';

interface PhaseState {
  projectId: string;
  projectName?: string;
  createdAt: Date;
  updatedAt: Date;
  currentPhase: PhaseType;
  phaseStatus: Record<PhaseType, PhaseStatus>;
  approvalsRequired: boolean;
  metadata?: Record<string, any>;
}

interface PhaseStatus {
  completed: boolean;
  approved: boolean;
  startedAt?: Date;
  completedAt?: Date;
  approvedAt?: Date;
  approvedBy?: string;
  artifacts: string[];
  notes?: string;
}
```

#### 使用例

```typescript
const manager = new PhaseStateManager();

// プロジェクトを初期化
const state = await manager.initializeProject('My Project', true);

// フェーズを管理
await manager.startPhase('intent');
await manager.completePhase('intent', ['requirements.md', 'user-stories.md']);
await manager.approvePhase('intent', 'Tech Lead', 'Requirements approved');

// 次のフェーズへ移行
if (await manager.canTransitionToNextPhase()) {
  const nextPhase = await manager.transitionToNextPhase();
  console.log(`Moved to phase: ${nextPhase}`);
}

// 進捗を確認
const progress = await manager.getProgressPercentage();
console.log(`Project progress: ${progress}%`);
```

### ApprovalService

承認ワークフローを管理するサービスクラス。

```typescript
import { ApprovalService } from 'ae-framework/services';

const service = new ApprovalService(projectRoot?: string, phaseStateManager?: PhaseStateManager);

// メソッド
service.setPolicy(phase: PhaseType, policy: ApprovalPolicy): void
await service.requestApproval(phase: PhaseType, requestedBy: string, summary?: string): Promise<ApprovalRequest>
await service.approve(phase: PhaseType, approvedBy: string, notes?: string, conditions?: string[]): Promise<void>
await service.reject(phase: PhaseType, rejectedBy: string, reason: string): Promise<void>
await service.getPendingApprovals(): Promise<PendingApproval[]>
await service.getApprovalHistory(phase: PhaseType): Promise<PendingApproval[]>
await service.getApprovalStatus(phase: PhaseType): Promise<ApprovalStatus>
await service.checkExpiredApprovals(): Promise<void>

// イベント
service.on('approval:requested', handler)
service.on('approval:completed', handler)
service.on('approval:rejected', handler)
service.on('approval:expired', handler)
service.on('approval:auto', handler)
service.on('approval:partial', handler)
```

#### 型定義

```typescript
interface ApprovalPolicy {
  requireMultipleApprovers?: boolean;
  minApprovers?: number;
  approverRoles?: string[];
  autoApproveConditions?: ApprovalCondition[];
  timeoutHours?: number;
  escalationPath?: string[];
}

interface ApprovalCondition {
  type: 'test-coverage' | 'code-review' | 'security-scan' | 'custom';
  threshold?: number;
  customCheck?: (artifacts: string[]) => Promise<boolean>;
}

interface ApprovalRequest {
  phase: PhaseType;
  projectId: string;
  projectName?: string;
  requestedBy: string;
  requestedAt: Date;
  artifacts: string[];
  summary?: string;
  metadata?: Record<string, any>;
}
```

#### 使用例

```typescript
const service = new ApprovalService();

// ポリシーを設定
service.setPolicy('code', {
  requireMultipleApprovers: true,
  minApprovers: 2,
  autoApproveConditions: [
    { type: 'test-coverage', threshold: 90 }
  ],
  timeoutHours: 48
});

// 承認をリクエスト
const request = await service.requestApproval(
  'code',
  'Developer',
  'Code implementation complete'
);

// イベントリスナーを設定
service.on('approval:completed', ({ phase, approvedBy }) => {
  console.log(`${phase} approved by ${approvedBy}`);
});

// 承認を実行
await service.approve('code', 'Tech Lead', 'LGTM');
```

### SlashCommandManager

Slash Commandsを管理・実行するクラス。

```typescript
import { SlashCommandManager } from 'ae-framework/commands';

const manager = new SlashCommandManager(projectRoot?: string);

// メソッド
await manager.execute(input: string): Promise<CommandResult>
await manager.executeSequence(commands: string[]): Promise<CommandResult[]>
manager.parseCommandFromText(text: string): string[]
manager.getCommands(): SlashCommand[]
```

#### 型定義

```typescript
interface SlashCommand {
  name: string;
  description: string;
  category: 'phase' | 'workflow' | 'info' | 'utility';
  usage: string;
  aliases?: string[];
  handler: CommandHandler;
  requiresPhase?: PhaseType;
  stopOnFailure?: boolean;
}

interface CommandResult {
  success: boolean;
  message?: string;
  data?: any;
  nextCommand?: string;
}

interface CommandContext {
  phaseStateManager: PhaseStateManager;
  steeringLoader: SteeringLoader;
  approvalService: ApprovalService;
  currentPhase?: PhaseType;
  projectRoot: string;
}
```

#### 使用例

```typescript
const manager = new SlashCommandManager();

// 単一コマンドを実行
const result = await manager.execute('/init My Project');
if (result.success) {
  console.log(result.message);
}

// コマンドシーケンスを実行
const results = await manager.executeSequence([
  '/init My Project',
  '/intent User authentication required',
  '/complete requirements.md',
  '/approve',
  '/next'
]);

// テキストからコマンドを抽出
const text = 'Please /init the project and /status to check';
const commands = manager.parseCommandFromText(text);
console.log(commands); // ['/init the project and', '/status to check']

// 利用可能なコマンドを取得
const allCommands = manager.getCommands();
allCommands.forEach(cmd => {
  console.log(`${cmd.name}: ${cmd.description}`);
});
```

## 🤖 Agent APIs

### IntentAgent

要件分析と意図抽出を行うエージェント。

```typescript
import { IntentAgent } from 'ae-framework/agents';

const agent = new IntentAgent();

// メソッド
await agent.analyzeIntent(request: IntentAnalysisRequest): Promise<IntentAnalysisResult>
await agent.extractFromNaturalLanguage(text: string): Promise<Requirement[]>
await agent.createUserStories(requirements: Requirement[]): Promise<UserStory[]>
await agent.buildDomainModelFromRequirements(requirements: Requirement[], context?: ProjectContext): Promise<DomainModel>
await agent.detectAmbiguities(sources: RequirementSource[]): Promise<Ambiguity[]>
await agent.validateCompleteness(requirements: Requirement[]): Promise<ValidationResult>
await agent.prioritizeRequirements(requirements: Requirement[], constraints: Constraint[]): Promise<Requirement[]>
await agent.generateAcceptanceCriteria(requirement: Requirement): Promise<AcceptanceCriteria[]>
```

### FormalAgent

形式仕様を生成・管理するエージェント。

```typescript
import { FormalAgent } from 'ae-framework/agents';

const agent = new FormalAgent();

// メソッド
await agent.generateOpenAPISpec(request: OpenAPIRequest): Promise<OpenAPISpec>
await agent.generateAsyncAPISpec(request: AsyncAPIRequest): Promise<AsyncAPISpec>
await agent.generateGraphQLSchema(request: GraphQLRequest): Promise<string>
await agent.generateTLAPlus(request: TLARequest): Promise<TLAModule>
await agent.createStateMachine(request: StateMachineRequest): Promise<StateMachine>
await agent.generateERDiagram(request: ERRequest): Promise<ERDiagram>
```

### TestGenerationAgent

テストを自動生成するエージェント。

```typescript
import { TestGenerationAgent } from 'ae-framework/agents';

const agent = new TestGenerationAgent();

// メソッド
await agent.generateTests(request: TestGenerationRequest): Promise<TestSuite>
await agent.generateFromRequirements(requirements: string[]): Promise<TestCase[]>
await agent.generatePropertyTests(request: PropertyTestRequest): Promise<PropertyTest[]>
await agent.generateBDDScenarios(userStories: UserStory[]): Promise<GherkinScenario[]>
await agent.generateSecurityTests(request: SecurityTestRequest): Promise<SecurityTest[]>
await agent.generatePerformanceTests(request: PerformanceTestRequest): Promise<PerformanceTest[]>
```

### CodeGenerationAgent

コードを生成するエージェント。

```typescript
import { CodeGenerationAgent } from 'ae-framework/agents';

const agent = new CodeGenerationAgent();

// メソッド
await agent.generateFromTests(request: CodeGenerationRequest): Promise<GeneratedCode>
await agent.generateFromSpec(spec: FormalSpec): Promise<GeneratedCode>
await agent.refactor(code: string, patterns: string[]): Promise<RefactoredCode>
await agent.optimizeCode(code: string): Promise<OptimizedCode>
```

### VerifyAgent

実装を検証するエージェント。

```typescript
import { VerifyAgent } from 'ae-framework/agents';

const agent = new VerifyAgent();

// メソッド
await agent.runFullVerification(): Promise<VerificationReport>
await agent.runTests(): Promise<TestResults>
await agent.checkCoverage(): Promise<CoverageReport>
await agent.runSecurityScan(): Promise<SecurityReport>
await agent.runPerformanceTests(): Promise<PerformanceReport>
await agent.validateContracts(): Promise<ContractValidation>
```

### OperateAgent

デプロイと運用を管理するエージェント。

```typescript
import { OperateAgent } from 'ae-framework/agents';

const agent = new OperateAgent();

// メソッド
await agent.deploy(request: DeploymentRequest): Promise<DeploymentResult>
await agent.rollback(version: string): Promise<RollbackResult>
await agent.getMetrics(): Promise<Metrics>
await agent.getHealthStatus(): Promise<HealthStatus>
await agent.runDiagnostics(): Promise<DiagnosticsReport>
```

## 🔌 MCP Server APIs

### Intent Server

```typescript
// MCPサーバーとして起動
npm run intent-agent

// 利用可能なツール
{
  "tool": "analyze_requirements",
  "args": {
    "requirements": ["User authentication", "Data persistence"]
  }
}

{
  "tool": "extract_user_stories",
  "args": {
    "feature": "Shopping Cart"
  }
}

{
  "tool": "detect_ambiguities",
  "args": {
    "text": "The system should be fast"
  }
}
```

### Test Generation Server

```typescript
// MCPサーバーとして起動
npm run mcp:test-gen

// 利用可能なツール
{
  "tool": "generate_tests_from_requirements",
  "args": {
    "requirements": ["User can login", "Password must be hashed"]
  }
}

{
  "tool": "generate_property_tests",
  "args": {
    "component": "Calculator",
    "properties": ["commutativity", "associativity"]
  }
}
```

## 🎨 カスタム拡張

### カスタムエージェントの作成

```typescript
import { BaseAgent } from 'ae-framework/agents';

export class CustomAgent extends BaseAgent {
  constructor() {
    super('intent'); // フェーズを指定
  }

  async executeTask(input: any): Promise<any> {
    // フェーズを初期化
    await this.initializePhase();

    // Steering Documentsを取得
    const steeringContext = await this.getSteeringContext();
    
    // 前のフェーズの成果物を取得
    const previousArtifacts = await this.getPreviousPhaseArtifacts();

    // タスクを実行
    const result = await this.processTask(input, steeringContext);

    // アクティビティをログ
    await this.logActivity('Task executed', { input, result });

    // フェーズを完了
    await this.completePhase(['output.md']);

    return result;
  }

  private async processTask(input: any, context: string): Promise<any> {
    // カスタムロジック
    return { processed: true };
  }
}
```

### カスタムSlashCommandの追加

```typescript
import { SlashCommandManager } from 'ae-framework/commands';

class ExtendedCommandManager extends SlashCommandManager {
  constructor(projectRoot?: string) {
    super(projectRoot);
    this.registerCustomCommands();
  }

  private registerCustomCommands(): void {
    this.registerCommand({
      name: '/custom',
      description: 'Custom command',
      category: 'utility',
      usage: '/custom <args>',
      aliases: ['/cst'],
      handler: this.handleCustomCommand.bind(this),
      stopOnFailure: false
    });
  }

  private async handleCustomCommand(
    args: string[],
    context: CommandContext
  ): Promise<CommandResult> {
    // カスタムロジック
    return {
      success: true,
      message: 'Custom command executed',
      data: { args }
    };
  }
}
```

### カスタム承認条件の実装

```typescript
import { ApprovalService } from 'ae-framework/services';

const service = new ApprovalService();

// カスタム承認条件を定義
service.setPolicy('custom-phase', {
  autoApproveConditions: [{
    type: 'custom',
    customCheck: async (artifacts: string[]) => {
      // カスタムチェックロジック
      const hasRequiredFiles = artifacts.includes('required.md');
      const passesValidation = await validateArtifacts(artifacts);
      
      return hasRequiredFiles && passesValidation;
    }
  }]
});

async function validateArtifacts(artifacts: string[]): Promise<boolean> {
  // バリデーションロジック
  return true;
}
```

## 📊 データフォーマット

### phase-state.json

```json
{
  "projectId": "uuid-v4",
  "projectName": "My Project",
  "createdAt": "2024-01-01T00:00:00.000Z",
  "updatedAt": "2024-01-01T00:00:00.000Z",
  "currentPhase": "intent",
  "phaseStatus": {
    "intent": {
      "completed": true,
      "approved": true,
      "startedAt": "2024-01-01T00:00:00.000Z",
      "completedAt": "2024-01-01T01:00:00.000Z",
      "approvedAt": "2024-01-01T02:00:00.000Z",
      "approvedBy": "Tech Lead",
      "artifacts": ["requirements.md"],
      "notes": "Requirements approved"
    }
  },
  "approvalsRequired": true,
  "metadata": {
    "custom_field": "value"
  }
}
```

### approval.json

```json
{
  "request": {
    "phase": "intent",
    "projectId": "uuid-v4",
    "requestedBy": "Developer",
    "requestedAt": "2024-01-01T00:00:00.000Z",
    "artifacts": ["requirements.md"],
    "summary": "Ready for review"
  },
  "policy": {
    "requireMultipleApprovers": false,
    "minApprovers": 1,
    "timeoutHours": 48
  },
  "status": "pending",
  "responses": [],
  "createdAt": "2024-01-01T00:00:00.000Z",
  "expiresAt": "2024-01-03T00:00:00.000Z"
}
```

## 🔗 関連リンク

- [クイックスタート](./QUICK_START.md)
- [新機能ガイド](./NEW_FEATURES.md)
- [設定ガイド](./CONFIGURATION.md)
- [トラブルシューティング](./TROUBLESHOOTING.md)