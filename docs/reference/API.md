---
docRole: ssot
lastVerified: '2026-03-10'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# AE Framework API Reference

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Complete API reference for ae-framework's 6-phase software development workflow system**

### Public API (npm)
The published package currently exposes a minimal surface:

```text
import { createServer, DomainServices, Infra } from 'ae-framework';
```

Other modules shown in this document are internal (source-level) APIs intended for use within this repository or via direct source access.

### 📦 Package Structure

```
ae-framework/
├── src/
│   ├── agents/           # AI Agents
│   ├── cli/              # CLI Tools
│   ├── commands/         # Slash Commands
│   ├── services/         # Service Layer
│   ├── utils/            # Utilities
│   └── mcp-server/       # MCP Server
└── tests/                # Test Suite
```

## 🔧 Core APIs

### SteeringLoader

Class for loading and managing Steering Documents.

```text
import { SteeringLoader } from 'ae-framework/utils';

const loader = new SteeringLoader(projectRoot?: string);

// Methods
await loader.loadDocument(documentName: string): Promise<string | null>
await loader.loadAllDocuments(): Promise<Record<string, string>>
await loader.loadCoreDocuments(): Promise<Record<string, string>>
await loader.loadCustomDocuments(): Promise<Record<string, string>>
await loader.getSteeringContext(): Promise<string>
await loader.hasSteeringDocuments(): Promise<boolean>
```

#### Usage Example

```text
const loader = new SteeringLoader();

// Load specific document
const productDoc = await loader.loadDocument('product');

// Load all documents
const allDocs = await loader.loadAllDocuments();
console.log(allDocs.product);
console.log(allDocs.architecture);
console.log(allDocs.standards);

// Get steering context
const context = await loader.getSteeringContext();
```

### PhaseStateManager

Class for managing project phase state.

```text
import { PhaseStateManager, PhaseType } from 'ae-framework/utils';

const manager = new PhaseStateManager(projectRoot?: string);

// Methods
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

#### Type Definitions

```text
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

#### Usage Example

```text
const manager = new PhaseStateManager();

// Initialize project
const state = await manager.initializeProject('My Project', true);

// Manage phases
await manager.startPhase('intent');
await manager.completePhase('intent', ['requirements.md', 'user-stories.md']);
await manager.approvePhase('intent', 'Tech Lead', 'Requirements approved');

// Transition to next phase
if (await manager.canTransitionToNextPhase()) {
  const nextPhase = await manager.transitionToNextPhase();
  console.log(`Moved to phase: ${nextPhase}`);
}

// Check progress
const progress = await manager.getProgressPercentage();
console.log(`Project progress: ${progress}%`);
```

### ApprovalService

Service class for managing approval workflows.

```text
import { ApprovalService } from 'ae-framework/services';

const service = new ApprovalService(projectRoot?: string, phaseStateManager?: PhaseStateManager);

// Methods
service.setPolicy(phase: PhaseType, policy: ApprovalPolicy): void
await service.requestApproval(phase: PhaseType, requestedBy: string, summary?: string): Promise<ApprovalRequest>
await service.approve(phase: PhaseType, approvedBy: string, notes?: string, conditions?: string[]): Promise<void>
await service.reject(phase: PhaseType, rejectedBy: string, reason: string): Promise<void>
await service.getPendingApprovals(): Promise<PendingApproval[]>
await service.getApprovalHistory(phase: PhaseType): Promise<PendingApproval[]>
await service.getApprovalStatus(phase: PhaseType): Promise<ApprovalStatus>
await service.checkExpiredApprovals(): Promise<void>

// Events
service.on('approval:requested', handler)
service.on('approval:completed', handler)
service.on('approval:rejected', handler)
service.on('approval:expired', handler)
service.on('approval:auto', handler)
service.on('approval:partial', handler)
```

#### Type Definitions

```text
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

#### Usage Example

```text
const service = new ApprovalService();

// Set policy
service.setPolicy('code', {
  requireMultipleApprovers: true,
  minApprovers: 2,
  autoApproveConditions: [
    { type: 'test-coverage', threshold: 90 }
  ],
  timeoutHours: 48
});

// Request approval
const request = await service.requestApproval(
  'code',
  'Developer',
  'Code implementation complete'
);

// Set event listeners
service.on('approval:completed', ({ phase, approvedBy }) => {
  console.log(`${phase} approved by ${approvedBy}`);
});

// Execute approval
await service.approve('code', 'Tech Lead', 'LGTM');
```

### SlashCommandManager

Class for managing and executing Slash Commands.

```text
import { SlashCommandManager } from 'ae-framework/commands';

const manager = new SlashCommandManager(projectRoot?: string);

// Methods
await manager.execute(input: string): Promise<CommandResult>
await manager.executeSequence(commands: string[]): Promise<CommandResult[]>
manager.parseCommandFromText(text: string): string[]
manager.getCommands(): SlashCommand[]
```

#### Type Definitions

```text
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

#### Usage Example

```text
const manager = new SlashCommandManager();

// Execute single command
const result = await manager.execute('/init My Project');
if (result.success) {
  console.log(result.message);
}

// Execute command sequence
const results = await manager.executeSequence([
  '/init My Project',
  '/intent User authentication required',
  '/complete requirements.md',
  '/approve',
  '/next'
]);

// Extract commands from text
const text = 'Please /init the project and /status to check';
const commands = manager.parseCommandFromText(text);
console.log(commands); // ['/init the project and', '/status to check']

// Get available commands
const allCommands = manager.getCommands();
allCommands.forEach(cmd => {
  console.log(`${cmd.name}: ${cmd.description}`);
});
```

## 🤖 Agent APIs

### IntentAgent

Agent for requirements analysis and intent extraction.

```text
import { IntentAgent } from 'ae-framework/agents';

const agent = new IntentAgent();

// Methods
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

Agent for generating and managing formal specifications.

```text
import { FormalAgent } from 'ae-framework/agents';

const agent = new FormalAgent();

// Methods
await agent.generateOpenAPISpec(request: OpenAPIRequest): Promise<OpenAPISpec>
await agent.generateAsyncAPISpec(request: AsyncAPIRequest): Promise<AsyncAPISpec>
await agent.generateGraphQLSchema(request: GraphQLRequest): Promise<string>
await agent.generateTLAPlus(request: TLARequest): Promise<TLAModule>
await agent.createStateMachine(request: StateMachineRequest): Promise<StateMachine>
await agent.generateERDiagram(request: ERRequest): Promise<ERDiagram>
```

### TestGenerationAgent

Agent for automatic test generation.

```text
import { TestGenerationAgent } from 'ae-framework/agents';

const agent = new TestGenerationAgent();

// Methods
await agent.generateTests(request: TestGenerationRequest): Promise<TestSuite>
await agent.generateFromRequirements(requirements: string[]): Promise<TestCase[]>
await agent.generatePropertyTests(request: PropertyTestRequest): Promise<PropertyTest[]>
await agent.generateBDDScenarios(userStories: UserStory[]): Promise<GherkinScenario[]>
await agent.generateSecurityTests(request: SecurityTestRequest): Promise<SecurityTest[]>
await agent.generatePerformanceTests(request: PerformanceTestRequest): Promise<PerformanceTest[]>
```

### CodeGenerationAgent

Agent for code generation.

```text
import { CodeGenerationAgent } from 'ae-framework/agents';

const agent = new CodeGenerationAgent();

// Methods
await agent.generateFromTests(request: CodeGenerationRequest): Promise<GeneratedCode>
await agent.generateFromSpec(spec: FormalSpec): Promise<GeneratedCode>
await agent.refactor(code: string, patterns: string[]): Promise<RefactoredCode>
await agent.optimizeCode(code: string): Promise<OptimizedCode>
```

### VerifyAgent

Agent for implementation verification.

```text
import { VerifyAgent } from 'ae-framework/agents';

const agent = new VerifyAgent();

// Methods
await agent.runFullVerification(): Promise<VerificationReport>
await agent.runTests(): Promise<TestResults>
await agent.checkCoverage(): Promise<CoverageReport>
await agent.runSecurityScan(): Promise<SecurityReport>
await agent.runPerformanceTests(): Promise<PerformanceReport>
await agent.validateContracts(): Promise<ContractValidation>
```

### OperateAgent

Agent for deployment and operations management.

```text
import { OperateAgent } from 'ae-framework/agents';

const agent = new OperateAgent();

// Methods
await agent.deploy(request: DeploymentRequest): Promise<DeploymentResult>
await agent.rollback(version: string): Promise<RollbackResult>
await agent.getMetrics(): Promise<Metrics>
await agent.getHealthStatus(): Promise<HealthStatus>
await agent.runDiagnostics(): Promise<DiagnosticsReport>
```

## 🔌 MCP Server APIs

### Intent Server

```text
// Start as MCP Server
pnpm run intent-agent

// Available tools
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

```text
// Start as MCP Server
pnpm run mcp:test-gen

// Available tools
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

## 🎨 Custom Extensions

### Creating Custom Agents

```text
import { BaseAgent } from 'ae-framework/agents';

export class CustomAgent extends BaseAgent {
  constructor() {
    super('intent'); // Specify phase
  }

  async executeTask(input: any): Promise<any> {
    // Initialize phase
    await this.initializePhase();

    // Get Steering Documents
    const steeringContext = await this.getSteeringContext();
    
    // Get previous phase artifacts
    const previousArtifacts = await this.getPreviousPhaseArtifacts();

    // Execute task
    const result = await this.processTask(input, steeringContext);

    // Log activity
    await this.logActivity('Task executed', { input, result });

    // Complete phase
    await this.completePhase(['output.md']);

    return result;
  }

  private async processTask(input: any, context: string): Promise<any> {
    // Custom logic
    return { processed: true };
  }
}
```

### Adding Custom Slash Commands

```text
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
    // Custom logic
    return {
      success: true,
      message: 'Custom command executed',
      data: { args }
    };
  }
}
```

### Implementing Custom Approval Conditions

```text
import { ApprovalService } from 'ae-framework/services';

const service = new ApprovalService();

// Define custom approval condition
service.setPolicy('custom-phase', {
  autoApproveConditions: [{
    type: 'custom',
    customCheck: async (artifacts: string[]) => {
      // Custom check logic
      const hasRequiredFiles = artifacts.includes('required.md');
      const passesValidation = await validateArtifacts(artifacts);
      
      return hasRequiredFiles && passesValidation;
    }
  }]
});

async function validateArtifacts(artifacts: string[]): Promise<boolean> {
  // Validation logic
  return true;
}
```

## 📊 Data Formats

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

## 🔗 Related Links

- [Quick Start](../getting-started/QUICK-START-GUIDE.md)
- [New Features Guide](../architecture/NEW_FEATURES.md)
- [Configuration Guide](../getting-started/SETUP.md)
- [Troubleshooting](../guides/ADVANCED-TROUBLESHOOTING-GUIDE.md)

---

## Japanese

**ae-frameworkの6フェーズソフトウェア開発ワークフローシステムの完全なAPIリファレンス**

### 📦 パッケージ構成

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

```text
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

```text
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

[Japanese content continues with all remaining sections following the same structure as English...]

---

**🚀 Build powerful applications with ae-framework APIs! / ae-framework APIで強力なアプリケーションを構築しましょう！**

## 日本語

**ae-framework の 6 フェーズ開発ワークフローを支える API の概要と使用例**

### 公開API（npm）
公開パッケージのトップレベルは最小構成です。

```text
import { createServer, DomainServices, Infra } from 'ae-framework';
```

本書の他のAPIは、主にリポジトリ内/ソースレベルの利用を想定した内部APIです。

### パッケージ構成（抜粋）
```
ae-framework/
├── src/agents/      # エージェント
├── src/cli/         # CLI
├── src/commands/    # スラッシュコマンド
├── src/services/    # サービス層
├── src/utils/       # ユーティリティ
└── src/mcp-server/  # MCP サーバ
```

### 例: SteeringLoader
ステアリングドキュメント（product/architecture/standards）を読み込み、文脈を生成します。

```text
const loader = new SteeringLoader();
const doc = await loader.loadDocument('product');
const all = await loader.loadAllDocuments();
const context = await loader.getSteeringContext();
```

以降は英語セクションと同じ順序で、各 API（エージェント/コード生成/検証など）の詳細をご確認ください。
