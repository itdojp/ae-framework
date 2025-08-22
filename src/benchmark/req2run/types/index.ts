/**
 * Req2Run Benchmark Integration Types
 * Core type definitions for benchmark execution and evaluation
 */

export interface RequirementSpec {
  id: string;
  title: string;
  description: string;
  category: BenchmarkCategory;
  difficulty: DifficultyLevel;
  requirements: string[];
  constraints: string[];
  testCriteria: TestCriteria[];
  expectedOutput: ExpectedOutput;
  timeLimit?: number;
  resourceLimits?: ResourceLimits;
  metadata: {
    created_by: string;
    created_at: string;
    category: string;
    difficulty: string;
  };
}

export interface BenchmarkResult {
  problemId: string;
  timestamp: Date;
  success: boolean;
  metrics: BenchmarkMetrics;
  executionDetails: ExecutionDetails;
  generatedArtifacts: GeneratedArtifacts;
  errors?: BenchmarkError[];
}

export interface BenchmarkMetrics {
  overallScore: number;              // 総合スコア (0-100)
  functionalCoverage: number;        // 機能カバレッジ (30-40%)
  testPassRate: number;              // テスト合格率 (20-30%)
  performance: PerformanceMetrics;   // 性能指標 (10-20%)
  codeQuality: QualityMetrics;       // コード品質 (10-20%)
  security: SecurityMetrics;         // セキュリティ (10-20%)
  timeToCompletion: number;          // 完了時間 (ms)
  resourceUsage: ResourceMetrics;    // リソース使用量
  phaseMetrics: PhaseMetrics[];      // フェーズ別メトリクス
}

export interface PerformanceMetrics {
  responseTime: number;              // レスポンス時間 (ms)
  throughput: number;                // スループット (req/s)
  memoryUsage: number;               // メモリ使用量 (MB)
  cpuUsage: number;                  // CPU使用率 (%)
  diskUsage: number;                 // ディスク使用量 (MB)
  networkLatency?: number;           // ネットワーク遅延 (ms)
}

export interface QualityMetrics {
  codeComplexity: number;            // コード複雑度
  maintainabilityIndex: number;      // 保守性指標
  testCoverage: number;              // テストカバレッジ (%)
  duplicationRatio: number;          // 重複率 (%)
  lintScore: number;                 // リント警告数
  typeScriptErrors: number;          // TypeScript エラー数
}

export interface SecurityMetrics {
  vulnerabilityCount: number;        // 脆弱性数
  securityScore: number;             // セキュリティスコア (0-100)
  owaspCompliance: number;           // OWASP準拠度 (%)
  dependencyVulnerabilities: number; // 依存関係の脆弱性数
  secretsExposed: number;            // 露出した秘密情報数
  securityHeaders: number;           // セキュリティヘッダー数
}

export interface ResourceMetrics {
  maxMemoryUsage: number;            // 最大メモリ使用量 (MB)
  avgCpuUsage: number;               // 平均CPU使用率 (%)
  diskIO: number;                    // ディスクI/O (MB/s)
  networkIO: number;                 // ネットワークI/O (MB/s)
  buildTime: number;                 // ビルド時間 (ms)
  deploymentTime: number;            // デプロイ時間 (ms)
}

export interface PhaseMetrics {
  phase: AEFrameworkPhase;
  duration: number;                  // フェーズ実行時間 (ms)
  success: boolean;
  outputQuality: number;             // 出力品質 (0-100)
  resourceUsage: ResourceMetrics;
  errors?: string[];
}

export interface ExecutionDetails {
  startTime: Date;
  endTime: Date;
  totalDuration: number;             // 総実行時間 (ms)
  phaseExecutions: PhaseExecution[];
  environment: ExecutionEnvironment;
  logs: ExecutionLog[];
}

export interface PhaseExecution {
  phase: AEFrameworkPhase;
  startTime: Date;
  endTime: Date;
  duration: number;
  input: any;
  output: any;
  success: boolean;
  errors?: string[];
}

export interface GeneratedArtifacts {
  sourceCode: SourceCodeArtifact[];
  documentation: DocumentationArtifact[];
  tests: TestArtifact[];
  configuration: ConfigurationArtifact[];
  deployment: DeploymentArtifact[];
}

export interface SourceCodeArtifact {
  filename: string;
  content: string;
  language: string;
  size: number;
  linesOfCode: number;
}

export interface TestCriteria {
  id: string;
  description: string;
  type: TestType;
  weight: number;                    // テスト重要度 (0-1)
  automated: boolean;
}

export interface ExpectedOutput {
  type: OutputType;
  format: string;
  schema?: any;
  examples: any[];
}

export enum BenchmarkCategory {
  WEB_API = 'web-api',
  CLI_TOOL = 'cli-tool',
  DATA_PROCESSING = 'data-processing',
  CRYPTOGRAPHY = 'cryptography',
  NETWORK_PROTOCOL = 'network-protocol',
  DATABASE = 'database',
  MACHINE_LEARNING = 'machine-learning',
  DISTRIBUTED_SYSTEM = 'distributed-system',
  AUTHENTICATION = 'authentication',
  FILE_PROCESSING = 'file-processing',
  REAL_TIME = 'real-time',
  MICROSERVICE = 'microservice',
  MONITORING = 'monitoring',
  DEVOPS = 'devops',
  SECURITY = 'security',
  PERFORMANCE = 'performance'
}

export enum DifficultyLevel {
  BASIC = 'basic',
  INTERMEDIATE = 'intermediate',
  ADVANCED = 'advanced',
  EXPERT = 'expert'
}

export enum AEFrameworkPhase {
  INTENT_ANALYSIS = 'intent-analysis',
  REQUIREMENTS = 'requirements',
  USER_STORIES = 'user-stories',
  VALIDATION = 'validation',
  DOMAIN_MODELING = 'domain-modeling',
  UI_UX_GENERATION = 'ui-ux-generation'
}

export enum TestType {
  UNIT = 'unit',
  INTEGRATION = 'integration',
  E2E = 'e2e',
  PERFORMANCE = 'performance',
  SECURITY = 'security',
  USABILITY = 'usability'
}

export enum OutputType {
  APPLICATION = 'application',
  API = 'api',
  LIBRARY = 'library',
  SERVICE = 'service',
  TOOL = 'tool'
}

export interface BenchmarkConfig {
  req2runRepository: string;
  problems: BenchmarkProblemConfig[];
  execution: ExecutionConfig;
  evaluation: EvaluationConfig;
  reporting: ReportingConfig;
}

export interface BenchmarkProblemConfig {
  id: string;
  enabled: boolean;
  timeoutMs: number;
  retries: number;
  category: BenchmarkCategory;
  difficulty: DifficultyLevel;
}

export interface ExecutionConfig {
  parallel: boolean;
  maxConcurrency: number;
  resourceLimits: ResourceLimits;
  environment: string;
  docker: DockerConfig;
}

export interface ResourceLimits {
  maxMemoryMB: number;
  maxCpuPercent: number;
  maxDiskMB: number;
  maxExecutionTimeMs: number;
}

export interface DockerConfig {
  enabled: boolean;
  image: string;
  volumes: string[];
  ports: number[];
}

export interface EvaluationConfig {
  weights: MetricWeights;
  thresholds: MetricThresholds;
  scoring: ScoringConfig;
}

export interface MetricWeights {
  functional: number;      // 0.3-0.4
  performance: number;     // 0.1-0.2
  quality: number;         // 0.1-0.2
  security: number;        // 0.1-0.2
  testing: number;         // 0.2-0.3
}

export interface MetricThresholds {
  minOverallScore: number;
  minFunctionalCoverage: number;
  maxResponseTime: number;
  minCodeQuality: number;
  maxVulnerabilities: number;
}

export interface ScoringConfig {
  algorithm: 'weighted-average' | 'weighted-geometric' | 'custom';
  penalties: PenaltyConfig;
  bonuses: BonusConfig;
}

export interface PenaltyConfig {
  timeoutPenalty: number;
  errorPenalty: number;
  qualityPenalty: number;
}

export interface BonusConfig {
  performanceBonus: number;
  qualityBonus: number;
  securityBonus: number;
}

export interface ReportingConfig {
  formats: ReportFormat[];
  destinations: ReportDestination[];
  dashboard: DashboardConfig;
}

export enum ReportFormat {
  JSON = 'json',
  HTML = 'html',
  PDF = 'pdf',
  CSV = 'csv',
  MARKDOWN = 'markdown'
}

export interface ReportDestination {
  type: 'file' | 'github' | 'slack' | 'email' | 'webhook';
  config: any;
}

export interface DashboardConfig {
  enabled: boolean;
  port: number;
  refreshInterval: number;
  charts: ChartConfig[];
}

export interface ChartConfig {
  type: 'line' | 'bar' | 'pie' | 'radar';
  metrics: string[];
  title: string;
}

export interface BenchmarkError {
  phase: AEFrameworkPhase;
  type: 'timeout' | 'runtime' | 'validation' | 'resource' | 'network';
  message: string;
  stack?: string;
  timestamp: Date;
}

export interface ExecutionEnvironment {
  nodeVersion: string;
  platform: string;
  arch: string;
  memory: number;
  cpuCount: number;
  dockerVersion?: string;
  kubernetesVersion?: string;
}

export interface ExecutionLog {
  timestamp: Date;
  level: 'debug' | 'info' | 'warn' | 'error';
  phase: AEFrameworkPhase;
  message: string;
  data?: any;
}

export interface DocumentationArtifact {
  filename: string;
  content: string;
  type: 'readme' | 'api' | 'architecture' | 'deployment' | 'user-guide';
  format: 'markdown' | 'html' | 'pdf';
}

export interface TestArtifact {
  filename: string;
  content: string;
  type: TestType;
  coverage: number;
  passed: number;
  failed: number;
  skipped: number;
}

export interface ConfigurationArtifact {
  filename: string;
  content: string;
  type: 'package' | 'docker' | 'ci' | 'deployment' | 'environment';
}

export interface DeploymentArtifact {
  filename: string;
  content: string;
  type: 'docker' | 'kubernetes' | 'terraform' | 'helm' | 'compose';
}

export interface BenchmarkReport {
  summary: BenchmarkSummary;
  results: BenchmarkResult[];
  trends: BenchmarkTrend[];
  recommendations: string[];
  generatedAt: Date;
}

export interface BenchmarkSummary {
  totalProblems: number;
  completedProblems: number;
  successRate: number;
  averageScore: number;
  totalExecutionTime: number;
  bestCategory: BenchmarkCategory;
  worstCategory: BenchmarkCategory;
  improvements: ImprovementSuggestion[];
}

export interface BenchmarkTrend {
  date: Date;
  metrics: BenchmarkMetrics;
  version: string;
  changes: string[];
}

export interface ImprovementSuggestion {
  category: string;
  priority: 'high' | 'medium' | 'low';
  description: string;
  estimatedImpact: number;
  implementationEffort: 'easy' | 'medium' | 'hard';
}