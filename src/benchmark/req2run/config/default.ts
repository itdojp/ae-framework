/**
 * Default Req2Run Benchmark Configuration
 * Provides sensible defaults for benchmark execution
 */

import type { BenchmarkConfig } from '../types/index.js';
import { BenchmarkCategory, DifficultyLevel, ReportFormat } from '../types/index.js';

export const DEFAULT_BENCHMARK_CONFIG: BenchmarkConfig = {
  req2runRepository: 'https://github.com/itdojp/req2run-benchmark.git',
  
  problems: [
    // Basic level problems for initial testing - using actual available problem IDs
    {
      id: 'CLI-001',
      enabled: true,
      timeoutMs: 300000, // 5 minutes
      retries: 1,
      category: BenchmarkCategory.CLI_TOOL,
      difficulty: DifficultyLevel.BASIC
    },
    
    // Intermediate level problems - using actual available problem IDs
    {
      id: 'WEB-001',
      enabled: true, // Enable for comprehensive benchmark
      timeoutMs: 600000, // 10 minutes
      retries: 2,
      category: BenchmarkCategory.WEB_API,
      difficulty: DifficultyLevel.INTERMEDIATE
    },
    {
      id: 'CLI-010',
      enabled: true,
      timeoutMs: 480000, // 8 minutes
      retries: 2,
      category: BenchmarkCategory.CLI_TOOL,
      difficulty: DifficultyLevel.INTERMEDIATE
    },
    {
      id: 'NET-001',
      enabled: true,
      timeoutMs: 480000, // 8 minutes
      retries: 2,
      category: BenchmarkCategory.NETWORK_PROTOCOL,
      difficulty: DifficultyLevel.INTERMEDIATE
    },
    
    // Advanced level problems - enable for comprehensive benchmark
    {
      id: 'DATA-001',
      enabled: true,
      timeoutMs: 1800000, // 30 minutes
      retries: 3,
      category: BenchmarkCategory.DATA_PROCESSING,
      difficulty: DifficultyLevel.ADVANCED
    },
    {
      id: 'ML-001',
      enabled: true,
      timeoutMs: 1800000, // 30 minutes
      retries: 3,
      category: BenchmarkCategory.MACHINE_LEARNING,
      difficulty: DifficultyLevel.ADVANCED
    },
    {
      id: 'WEB-012',
      enabled: true,
      timeoutMs: 1800000, // 30 minutes
      retries: 3,
      category: BenchmarkCategory.WEB_API,
      difficulty: DifficultyLevel.ADVANCED
    },
    // Expert level problems - enable for comprehensive benchmark
    {
      id: 'RTC-001',
      enabled: false, // Temporarily disable due to YAML conflict
      timeoutMs: 3600000, // 60 minutes
      retries: 3,
      category: BenchmarkCategory.REAL_TIME,
      difficulty: DifficultyLevel.EXPERT
    },
    {
      id: 'LANG-001',
      enabled: true,
      timeoutMs: 3600000, // 60 minutes
      retries: 3,
      category: BenchmarkCategory.MACHINE_LEARNING,
      difficulty: DifficultyLevel.EXPERT
    }
  ],

  execution: {
    parallel: true, // Enable parallel execution for comprehensive benchmark
    maxConcurrency: 3,
    resourceLimits: {
      maxMemoryMB: 4096,    // 4GB memory limit
      maxCpuPercent: 80,    // 80% CPU limit
      maxDiskMB: 10240,     // 10GB disk limit
      maxExecutionTimeMs: 3600000 // 1 hour total limit
    },
    environment: 'development',
    docker: {
      enabled: false, // Start without Docker isolation
      image: 'node:18-alpine',
      volumes: ['/tmp:/tmp'],
      ports: [3000, 8080]
    }
  },

  evaluation: {
    weights: {
      functional: 0.35,   // 35% - Core functionality
      performance: 0.15,  // 15% - Performance metrics
      quality: 0.20,      // 20% - Code quality
      security: 0.15,     // 15% - Security compliance
      testing: 0.15       // 15% - Test coverage and quality
    },
    thresholds: {
      minOverallScore: 60,        // Minimum 60% to pass
      minFunctionalCoverage: 70,  // Minimum 70% functional coverage
      maxResponseTime: 2000,      // Max 2 seconds response time
      minCodeQuality: 75,         // Minimum 75% code quality score
      maxVulnerabilities: 5       // Maximum 5 security vulnerabilities
    },
    scoring: {
      algorithm: 'weighted-average',
      penalties: {
        timeoutPenalty: 0.5,     // 50% penalty for timeouts
        errorPenalty: 0.3,       // 30% penalty for errors
        qualityPenalty: 0.2      // 20% penalty for quality issues
      },
      bonuses: {
        performanceBonus: 0.1,   // 10% bonus for excellent performance
        qualityBonus: 0.1,       // 10% bonus for excellent quality
        securityBonus: 0.05      // 5% bonus for excellent security
      }
    }
  },

  reporting: {
    formats: [
      ReportFormat.JSON,
      ReportFormat.HTML,
      ReportFormat.MARKDOWN
    ],
    destinations: [
      {
        type: 'file',
        config: {
          directory: './reports/benchmark',
          filename: 'req2run-benchmark-{timestamp}.{format}'
        }
      },
      {
        type: 'github',
        config: {
          repository: 'itdojp/ae-framework',
          issueOnFailure: true,
          commentOnPR: true
        }
      }
    ],
    dashboard: {
      enabled: true,
      port: 3001,
      refreshInterval: 30000, // 30 seconds
      charts: [
        {
          type: 'line',
          metrics: ['overallScore', 'functionalCoverage'],
          title: 'Performance Trends'
        },
        {
          type: 'bar',
          metrics: ['performance.responseTime', 'performance.memoryUsage'],
          title: 'Resource Usage'
        },
        {
          type: 'pie',
          metrics: ['security.vulnerabilityCount'],
          title: 'Security Issues'
        },
        {
          type: 'radar',
          metrics: [
            'functionalCoverage',
            'codeQuality.maintainabilityIndex',
            'security.securityScore',
            'performance.throughput'
          ],
          title: 'Overall Quality Radar'
        }
      ]
    }
  }
};

/**
 * Get configuration for a specific difficulty level
 */
export function getConfigForDifficulty(difficulty: DifficultyLevel): Partial<BenchmarkConfig> {
  const baseConfig = { ...DEFAULT_BENCHMARK_CONFIG };
  
  switch (difficulty) {
    case DifficultyLevel.BASIC:
      return {
        ...baseConfig,
        problems: baseConfig.problems.filter(p => 
          p.difficulty === DifficultyLevel.BASIC && p.enabled
        ),
        execution: {
          ...baseConfig.execution,
          parallel: false,
          maxConcurrency: 1
        }
      };
      
    case DifficultyLevel.INTERMEDIATE:
      return {
        ...baseConfig,
        problems: baseConfig.problems.filter(p => 
          [DifficultyLevel.BASIC, DifficultyLevel.INTERMEDIATE].includes(p.difficulty)
        ),
        execution: {
          ...baseConfig.execution,
          parallel: true,
          maxConcurrency: 2
        }
      };
      
    case DifficultyLevel.ADVANCED:
      return {
        ...baseConfig,
        problems: baseConfig.problems.filter(p => 
          p.difficulty !== DifficultyLevel.EXPERT
        ),
        execution: {
          ...baseConfig.execution,
          parallel: true,
          maxConcurrency: 3,
          docker: {
            ...baseConfig.execution.docker,
            enabled: true // Enable Docker for advanced problems
          }
        }
      };
      
    case DifficultyLevel.EXPERT:
      return {
        ...baseConfig,
        problems: baseConfig.problems, // All problems enabled
        execution: {
          ...baseConfig.execution,
          parallel: true,
          maxConcurrency: 4,
          resourceLimits: {
            ...baseConfig.execution.resourceLimits,
            maxMemoryMB: 8192,    // 8GB for expert problems
            maxExecutionTimeMs: 7200000 // 2 hours for expert problems
          },
          docker: {
            ...baseConfig.execution.docker,
            enabled: true
          }
        }
      };
      
    default:
      return baseConfig;
  }
}

/**
 * Get configuration for a specific category
 */
export function getConfigForCategory(category: BenchmarkCategory): Partial<BenchmarkConfig> {
  const baseConfig = { ...DEFAULT_BENCHMARK_CONFIG };
  
  return {
    ...baseConfig,
    problems: baseConfig.problems.filter(p => p.category === category)
  };
}

/**
 * Create a minimal configuration for CI/CD environments
 */
export function getCIConfig(): BenchmarkConfig {
  return {
    ...DEFAULT_BENCHMARK_CONFIG,
    problems: DEFAULT_BENCHMARK_CONFIG.problems.filter(p => 
      p.difficulty === DifficultyLevel.BASIC && p.enabled
    ).slice(0, 1), // Only first basic problem for CI
    execution: {
      ...DEFAULT_BENCHMARK_CONFIG.execution,
      parallel: false,
      maxConcurrency: 1,
      resourceLimits: {
        ...DEFAULT_BENCHMARK_CONFIG.execution.resourceLimits,
        maxMemoryMB: 2048,        // 2GB for CI
        maxExecutionTimeMs: 600000 // 10 minutes max for CI
      }
    },
    reporting: {
      ...DEFAULT_BENCHMARK_CONFIG.reporting,
      formats: [ReportFormat.JSON], // Only JSON for CI
      dashboard: {
        ...DEFAULT_BENCHMARK_CONFIG.reporting.dashboard,
        enabled: false // No dashboard in CI
      }
    }
  };
}
