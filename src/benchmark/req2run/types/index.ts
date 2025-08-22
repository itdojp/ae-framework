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
  timeLimit?: number;
}

export interface BenchmarkResult {
  problemId: string;
  timestamp: Date;
  success: boolean;
  metrics: BenchmarkMetrics;
  executionDetails: ExecutionDetails;
  errors?: BenchmarkError[];
}

export interface BenchmarkMetrics {
  overallScore: number;
  functionalCoverage: number;
  testPassRate: number;
  timeToCompletion: number;
}

export interface ExecutionDetails {
  startTime: Date;
  endTime: Date;
  totalDuration: number;
  environment: ExecutionEnvironment;
}

export interface BenchmarkError {
  phase: AEFrameworkPhase;
  type: 'timeout' | 'runtime' | 'validation';
  message: string;
  timestamp: Date;
}

export interface ExecutionEnvironment {
  nodeVersion: string;
  platform: string;
  arch: string;
  memory: number;
  cpuCount: number;
}

export interface BenchmarkConfig {
  req2runRepository: string;
  problems: BenchmarkProblemConfig[];
  execution: ExecutionConfig;
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
  environment: string;
}

export enum BenchmarkCategory {
  WEB_API = 'web-api',
  CLI_TOOL = 'cli-tool',
  DATA_PROCESSING = 'data-processing',
  CRYPTOGRAPHY = 'cryptography'
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