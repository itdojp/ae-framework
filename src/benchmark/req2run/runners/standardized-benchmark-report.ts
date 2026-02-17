import type {
  AgenticProgrammingMetrics,
  BenchmarkConfig,
  BenchmarkResult,
} from '../types/index.js';

export type PhaseSummary = {
  phase: string;
  success: boolean;
  duration: number;
  errors: number;
};

export type AnalyticsData = {
  summary: {
    totalProblems: number;
    successRate: number;
    averageScore: number;
    averageExecutionTime: number;
  };
  performance: {
    fastestExecution: number;
    slowestExecution: number;
    averagePhaseTime: Record<string, number>;
  };
  quality: {
    highScoreProblems: number;
    mediumScoreProblems: number;
    lowScoreProblems: number;
  };
  errors: {
    totalErrors: number;
    errorsByPhase: Record<string, number>;
    commonErrorPatterns: string[];
  };
};

export type EnhancedReportData = {
  metadata: {
    timestamp: string;
    totalProblems: number;
    successfulRuns: number;
    failedRuns: number;
    averageScore: number;
    totalExecutionTime: number;
    framework: string;
    benchmarkVersion: string;
    pipelineVersion: string;
    agentsUsed: string[];
  };
  configuration: BenchmarkConfig;
  analytics: AnalyticsData;
  results: Array<{
    problemId: string;
    success: boolean;
    score: number;
    executionTime: number;
    agentic: AgenticProgrammingMetrics | null;
    functionalCoverage: number;
    phases: PhaseSummary[];
    errors: string[];
  }>;
};

export function generateAnalytics(results: BenchmarkResult[]): AnalyticsData {
  const successful = results.filter((result) => result.success);

  return {
    summary: {
      totalProblems: results.length,
      successRate: results.length === 0 ? 0 : (successful.length / results.length) * 100,
      averageScore:
        successful.length > 0
          ? successful.reduce((sum, result) => sum + result.metrics.overallScore, 0) / successful.length
          : 0,
      averageExecutionTime:
        results.length > 0
          ? results.reduce((sum, result) => sum + result.executionDetails.totalDuration, 0) / results.length
          : 0,
    },
    performance: {
      fastestExecution: results.length > 0 ? Math.min(...results.map((result) => result.executionDetails.totalDuration)) : 0,
      slowestExecution: results.length > 0 ? Math.max(...results.map((result) => result.executionDetails.totalDuration)) : 0,
      averagePhaseTime: calculateAveragePhaseTime(results),
    },
    quality: {
      highScoreProblems: successful.filter((result) => result.metrics.overallScore >= 80).length,
      mediumScoreProblems: successful.filter(
        (result) => result.metrics.overallScore >= 60 && result.metrics.overallScore < 80,
      ).length,
      lowScoreProblems: successful.filter((result) => result.metrics.overallScore < 60).length,
    },
    errors: {
      totalErrors: results.reduce((sum, result) => sum + (result.errors?.length || 0), 0),
      errorsByPhase: analyzeErrorsByPhase(results),
      commonErrorPatterns: identifyCommonErrors(results),
    },
  };
}

export function generateEnhancedMarkdownReport(data: EnhancedReportData): string {
  return `# Standardized AE Framework Benchmark Report

Generated: ${data.metadata.timestamp}

## 📊 Executive Summary
- **Framework**: ${data.metadata.framework}
- **Pipeline Version**: ${data.metadata.pipelineVersion}
- **Total Problems**: ${data.metadata.totalProblems}
- **Success Rate**: ${data.analytics.summary.successRate.toFixed(1)}%
- **Average Score**: ${data.analytics.summary.averageScore.toFixed(1)}/100
- **Total Execution Time**: ${(data.metadata.totalExecutionTime / 1000).toFixed(1)}s

## 🎯 Performance Analytics

### Execution Performance
- **Fastest Execution**: ${(data.analytics.performance.fastestExecution / 1000).toFixed(2)}s
- **Slowest Execution**: ${(data.analytics.performance.slowestExecution / 1000).toFixed(2)}s
- **Average Execution**: ${(data.analytics.summary.averageExecutionTime / 1000).toFixed(2)}s

### Quality Distribution
- **High Score (≥80)**: ${data.analytics.quality.highScoreProblems} problems
- **Medium Score (60-79)**: ${data.analytics.quality.mediumScoreProblems} problems  
- **Low Score (<60)**: ${data.analytics.quality.lowScoreProblems} problems

### Phase Performance
${Object.entries(data.analytics.performance.averagePhaseTime)
  .map(([phase, time]) => `- **${phase}**: ${(Number(time) / 1000).toFixed(2)}s average`)
  .join('\n')}

## 🔍 Individual Results

${data.results
  .map(
    (result) => `### ${result.problemId}
- **Status**: ${result.success ? '✅ Success' : '❌ Failed'}
- **Score**: ${result.score.toFixed(1)}/100
- **Execution Time**: ${(result.executionTime / 1000).toFixed(2)}s
- **Functional Coverage**: ${result.functionalCoverage.toFixed(1)}%

#### Phase Breakdown
${result.phases
  .map(
    (phase) =>
      `- **${phase.phase}**: ${phase.success ? '✅' : '❌'} (${(phase.duration / 1000).toFixed(2)}s${
        phase.errors > 0 ? `, ${phase.errors} errors` : ''
      })`,
  )
  .join('\n')}

${result.errors.length > 0 ? `#### Errors\n${result.errors.map((error: string) => `- ${error}`).join('\n')}` : ''}
`,
  )
  .join('\n\n')}

## ⚠️ Error Analysis

### Errors by Phase
${Object.entries(data.analytics.errors.errorsByPhase)
  .map(([phase, count]) => `- **${phase}**: ${count} errors`)
  .join('\n')}

### Common Error Patterns
${data.analytics.errors.commonErrorPatterns.map((error: string) => `- ${error}`).join('\n')}

---
*Report generated by Standardized AE Framework Benchmark Runner v${data.metadata.pipelineVersion}*
`;
}

export function generateCSVReport(results: BenchmarkResult[]): string {
  const headers = [
    'Problem ID',
    'Success',
    'Score',
    'Execution Time (ms)',
    'Functional Coverage',
    'Phase Failures',
    'Error Count',
  ];
  const rows = results.map((result) => [
    result.problemId,
    result.success ? 'TRUE' : 'FALSE',
    result.metrics.overallScore.toFixed(1),
    result.executionDetails.totalDuration.toString(),
    result.metrics.functionalCoverage.toFixed(1),
    result.executionDetails.phaseExecutions.filter((phaseExecution) => !phaseExecution.success).length.toString(),
    (result.errors?.length || 0).toString(),
  ]);

  return [headers.join(','), ...rows.map((row) => row.join(','))].join('\n');
}

function calculateAveragePhaseTime(results: BenchmarkResult[]): Record<string, number> {
  const phaseTimes: Record<string, number[]> = {};

  results.forEach((result) => {
    result.executionDetails.phaseExecutions.forEach((phaseExecution) => {
      const phaseName = phaseExecution.phase.toString();
      if (!phaseTimes[phaseName]) {
        phaseTimes[phaseName] = [];
      }
      phaseTimes[phaseName].push(phaseExecution.duration);
    });
  });

  const averages: Record<string, number> = {};
  Object.entries(phaseTimes).forEach(([phase, times]) => {
    averages[phase] = times.reduce((sum, time) => sum + time, 0) / times.length;
  });

  return averages;
}

function analyzeErrorsByPhase(results: BenchmarkResult[]): Record<string, number> {
  const errorsByPhase: Record<string, number> = {};

  results.forEach((result) => {
    result.errors?.forEach((error) => {
      const phaseName = error.phase.toString();
      errorsByPhase[phaseName] = (errorsByPhase[phaseName] || 0) + 1;
    });
  });

  return errorsByPhase;
}

function identifyCommonErrors(results: BenchmarkResult[]): string[] {
  const errorMessages: Record<string, number> = {};

  results.forEach((result) => {
    result.errors?.forEach((error) => {
      const message = error.message.substring(0, 100);
      errorMessages[message] = (errorMessages[message] || 0) + 1;
    });
  });

  return Object.entries(errorMessages)
    .filter(([, count]) => count > 1)
    .sort(([, a], [, b]) => b - a)
    .slice(0, 5)
    .map(([message]) => message);
}
