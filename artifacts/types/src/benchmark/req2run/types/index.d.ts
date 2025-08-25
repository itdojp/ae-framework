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
    constraints: {
        business?: string[];
        performance?: any;
    };
    testCriteria: TestCriteria[];
    expectedOutput: ExpectedOutput;
    timeLimit?: number;
    resourceLimits?: ResourceLimits;
    metadata: {
        created_by: string;
        created_at: string;
        category: string;
        difficulty: string;
        estimated_time?: number;
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
    overallScore: number;
    functionalCoverage: number;
    testPassRate: number;
    performance: PerformanceMetrics;
    codeQuality: QualityMetrics;
    security: SecurityMetrics;
    timeToCompletion: number;
    resourceUsage: ResourceMetrics;
    phaseMetrics: PhaseMetrics[];
}
export interface PerformanceMetrics {
    responseTime: number;
    throughput: number;
    memoryUsage: number;
    cpuUsage: number;
    diskUsage: number;
    networkLatency?: number;
}
export interface QualityMetrics {
    codeComplexity: number;
    maintainabilityIndex: number;
    testCoverage: number;
    duplicationRatio: number;
    lintScore: number;
    typeScriptErrors: number;
}
export interface SecurityMetrics {
    vulnerabilityCount: number;
    securityScore: number;
    owaspCompliance: number;
    dependencyVulnerabilities: number;
    secretsExposed: number;
    securityHeaders: number;
}
export interface ResourceMetrics {
    maxMemoryUsage: number;
    avgCpuUsage: number;
    diskIO: number;
    networkIO: number;
    buildTime: number;
    deploymentTime: number;
}
export interface PhaseMetrics {
    phase: AEFrameworkPhase;
    duration: number;
    success: boolean;
    outputQuality: number;
    resourceUsage: ResourceMetrics;
    errors?: string[];
}
export interface ExecutionDetails {
    startTime: Date;
    endTime: Date;
    totalDuration: number;
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
    weight: number;
    automated: boolean;
}
export interface ExpectedOutput {
    type: OutputType;
    format: string;
    schema?: any;
    examples: any[];
}
export declare enum BenchmarkCategory {
    WEB_API = "web-api",
    CLI_TOOL = "cli-tool",
    DATA_PROCESSING = "data-processing",
    CRYPTOGRAPHY = "cryptography",
    NETWORK_PROTOCOL = "network-protocol",
    DATABASE = "database",
    MACHINE_LEARNING = "machine-learning",
    DISTRIBUTED_SYSTEM = "distributed-system",
    AUTHENTICATION = "authentication",
    FILE_PROCESSING = "file-processing",
    REAL_TIME = "real-time",
    MICROSERVICE = "microservice",
    MONITORING = "monitoring",
    DEVOPS = "devops",
    SECURITY = "security",
    PERFORMANCE = "performance"
}
export declare enum DifficultyLevel {
    BASIC = "basic",
    INTERMEDIATE = "intermediate",
    ADVANCED = "advanced",
    EXPERT = "expert"
}
export declare enum AEFrameworkPhase {
    INTENT_ANALYSIS = "intent-analysis",
    REQUIREMENTS = "requirements",
    USER_STORIES = "user-stories",
    VALIDATION = "validation",
    DOMAIN_MODELING = "domain-modeling",
    UI_UX_GENERATION = "ui-ux-generation"
}
export declare enum TestType {
    UNIT = "unit",
    INTEGRATION = "integration",
    E2E = "e2e",
    PERFORMANCE = "performance",
    SECURITY = "security",
    USABILITY = "usability"
}
export declare enum OutputType {
    APPLICATION = "application",
    API = "api",
    LIBRARY = "library",
    SERVICE = "service",
    TOOL = "tool"
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
    functional: number;
    performance: number;
    quality: number;
    security: number;
    testing: number;
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
export declare enum ReportFormat {
    JSON = "json",
    HTML = "html",
    PDF = "pdf",
    CSV = "csv",
    MARKDOWN = "markdown"
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
