import { metrics, trace, SpanStatusCode } from '@opentelemetry/api';

// Phase 6 metrics interface
export interface Phase6Metrics {
  quality: {
    coverage: number;
    a11yScore: number;
    performanceScore: number;
  };
  efficiency: {
    scaffoldTime: number;
    e2eTestTime: number;
    buildTime: number;
  };
  maintainability: {
    componentComplexity: number;
    cssUnusedRate: number;
    designTokenCoverage: number;
  };
}

// Performance thresholds
export const PHASE6_THRESHOLDS = {
  scaffoldTime: 30000, // 30 seconds
  e2eTestTime: 300000, // 5 minutes
  coverage: 80, // 80%
  a11yScore: 95, // 95%
  performanceScore: 75, // 75%
} as const;

// Metric instruments
const meter = metrics.getMeter('ae-framework-phase6', '1.0.0');
const tracer = trace.getTracer('ae-framework-phase6', '1.0.0');

// Counters
const scaffoldCounter = meter.createCounter('phase6_scaffold_operations_total', {
  description: 'Total number of scaffold operations',
});

const e2eTestCounter = meter.createCounter('phase6_e2e_tests_total', {
  description: 'Total number of E2E tests executed',
});

const a11yAuditCounter = meter.createCounter('phase6_a11y_audits_total', {
  description: 'Total number of accessibility audits performed',
});

// Histograms for timing
const scaffoldDuration = meter.createHistogram('phase6_scaffold_duration_ms', {
  description: 'Duration of scaffold operations in milliseconds',
});

const e2eDuration = meter.createHistogram('phase6_e2e_test_duration_ms', {
  description: 'Duration of E2E test execution in milliseconds',
});

const buildDuration = meter.createHistogram('phase6_build_duration_ms', {
  description: 'Duration of build operations in milliseconds',
});

// Gauges for quality metrics
const coverageGauge = meter.createObservableGauge('phase6_test_coverage_percent', {
  description: 'Test coverage percentage',
});

const a11yScoreGauge = meter.createObservableGauge('phase6_a11y_score_percent', {
  description: 'Accessibility score percentage',
});

const performanceScoreGauge = meter.createObservableGauge('phase6_performance_score_percent', {
  description: 'Performance score percentage',
});

// Telemetry helpers
export class Phase6Telemetry {
  // Scaffold operation instrumentation
  static async instrumentScaffoldOperation<T>(
    operationName: string,
    operation: () => Promise<T>,
    metadata: Record<string, any> = {}
  ): Promise<T> {
    const span = tracer.startSpan(`phase6.scaffold.${operationName}`, {
      attributes: {
        'phase6.operation': 'scaffold',
        'phase6.operation_name': operationName,
        ...metadata,
      },
    });

    const startTime = Date.now();
    
    try {
      const result = await operation();
      const duration = Date.now() - startTime;
      
      // Record metrics
      scaffoldCounter.add(1, { 
        operation: operationName,
        status: 'success',
      });
      
      scaffoldDuration.record(duration, {
        operation: operationName,
      });

      // Update span
      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'success',
        'phase6.threshold_met': duration < PHASE6_THRESHOLDS.scaffoldTime,
      });

      span.setStatus({ code: SpanStatusCode.OK });

      // Log performance warning if threshold exceeded
      if (duration > PHASE6_THRESHOLDS.scaffoldTime) {
        console.warn(`⚠️ Scaffold operation '${operationName}' took ${duration}ms (threshold: ${PHASE6_THRESHOLDS.scaffoldTime}ms)`);
      }

      return result;
    } catch (error) {
      const duration = Date.now() - startTime;
      
      scaffoldCounter.add(1, { 
        operation: operationName,
        status: 'error',
      });

      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'error',
        'phase6.error': error instanceof Error ? error.message : String(error),
      });

      span.setStatus({ 
        code: SpanStatusCode.ERROR,
        message: error instanceof Error ? error.message : String(error),
      });

      throw error;
    } finally {
      span.end();
    }
  }

  // E2E test instrumentation
  static async instrumentE2ETest<T>(
    testName: string,
    operation: () => Promise<T>,
    metadata: Record<string, any> = {}
  ): Promise<T> {
    const span = tracer.startSpan(`phase6.e2e.${testName}`, {
      attributes: {
        'phase6.operation': 'e2e_test',
        'phase6.test_name': testName,
        ...metadata,
      },
    });

    const startTime = Date.now();
    
    try {
      const result = await operation();
      const duration = Date.now() - startTime;
      
      e2eTestCounter.add(1, { 
        test: testName,
        status: 'passed',
      });
      
      e2eDuration.record(duration, {
        test: testName,
      });

      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'passed',
        'phase6.threshold_met': duration < PHASE6_THRESHOLDS.e2eTestTime,
      });

      span.setStatus({ code: SpanStatusCode.OK });

      if (duration > PHASE6_THRESHOLDS.e2eTestTime) {
        console.warn(`⚠️ E2E test '${testName}' took ${duration}ms (threshold: ${PHASE6_THRESHOLDS.e2eTestTime}ms)`);
      }

      return result;
    } catch (error) {
      const duration = Date.now() - startTime;
      
      e2eTestCounter.add(1, { 
        test: testName,
        status: 'failed',
      });

      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'failed',
        'phase6.error': error instanceof Error ? error.message : String(error),
      });

      span.setStatus({ 
        code: SpanStatusCode.ERROR,
        message: error instanceof Error ? error.message : String(error),
      });

      throw error;
    } finally {
      span.end();
    }
  }

  // Accessibility audit instrumentation
  static async instrumentA11yAudit<T>(
    auditName: string,
    operation: () => Promise<T>,
    metadata: Record<string, any> = {}
  ): Promise<T> {
    const span = tracer.startSpan(`phase6.a11y.${auditName}`, {
      attributes: {
        'phase6.operation': 'a11y_audit',
        'phase6.audit_name': auditName,
        ...metadata,
      },
    });

    const startTime = Date.now();
    
    try {
      const result = await operation();
      const duration = Date.now() - startTime;
      
      a11yAuditCounter.add(1, { 
        audit: auditName,
        status: 'completed',
      });

      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'completed',
      });

      span.setStatus({ code: SpanStatusCode.OK });

      return result;
    } catch (error) {
      const duration = Date.now() - startTime;
      
      a11yAuditCounter.add(1, { 
        audit: auditName,
        status: 'failed',
      });

      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'failed',
        'phase6.error': error instanceof Error ? error.message : String(error),
      });

      span.setStatus({ 
        code: SpanStatusCode.ERROR,
        message: error instanceof Error ? error.message : String(error),
      });

      throw error;
    } finally {
      span.end();
    }
  }

  // Build operation instrumentation
  static async instrumentBuildOperation<T>(
    buildType: string,
    operation: () => Promise<T>,
    metadata: Record<string, any> = {}
  ): Promise<T> {
    const span = tracer.startSpan(`phase6.build.${buildType}`, {
      attributes: {
        'phase6.operation': 'build',
        'phase6.build_type': buildType,
        ...metadata,
      },
    });

    const startTime = Date.now();
    
    try {
      const result = await operation();
      const duration = Date.now() - startTime;
      
      buildDuration.record(duration, {
        build_type: buildType,
      });

      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'success',
      });

      span.setStatus({ code: SpanStatusCode.OK });

      return result;
    } catch (error) {
      const duration = Date.now() - startTime;

      span.setAttributes({
        'phase6.duration_ms': duration,
        'phase6.status': 'failed',
        'phase6.error': error instanceof Error ? error.message : String(error),
      });

      span.setStatus({ 
        code: SpanStatusCode.ERROR,
        message: error instanceof Error ? error.message : String(error),
      });

      throw error;
    } finally {
      span.end();
    }
  }

  // Record quality metrics
  static recordQualityMetrics(metrics: Partial<Phase6Metrics['quality']>): void {
    if (metrics.coverage !== undefined) {
      console.log(`📊 Test Coverage: ${metrics.coverage}% (threshold: ${PHASE6_THRESHOLDS.coverage}%)`);
      if (metrics.coverage < PHASE6_THRESHOLDS.coverage) {
        console.warn(`⚠️ Test coverage below threshold: ${metrics.coverage}% < ${PHASE6_THRESHOLDS.coverage}%`);
      }
    }

    if (metrics.a11yScore !== undefined) {
      console.log(`♿ A11y Score: ${metrics.a11yScore}% (threshold: ${PHASE6_THRESHOLDS.a11yScore}%)`);
      if (metrics.a11yScore < PHASE6_THRESHOLDS.a11yScore) {
        console.warn(`⚠️ Accessibility score below threshold: ${metrics.a11yScore}% < ${PHASE6_THRESHOLDS.a11yScore}%`);
      }
    }

    if (metrics.performanceScore !== undefined) {
      console.log(`⚡ Performance Score: ${metrics.performanceScore}% (threshold: ${PHASE6_THRESHOLDS.performanceScore}%)`);
      if (metrics.performanceScore < PHASE6_THRESHOLDS.performanceScore) {
        console.warn(`⚠️ Performance score below threshold: ${metrics.performanceScore}% < ${PHASE6_THRESHOLDS.performanceScore}%`);
      }
    }
  }

  // Log efficiency metrics summary
  static logEfficiencyMetrics(metrics: Partial<Phase6Metrics['efficiency']>): void {
    console.log('\n📈 Phase 6 Efficiency Metrics:');
    
    if (metrics.scaffoldTime !== undefined) {
      const thresholdMet = metrics.scaffoldTime < PHASE6_THRESHOLDS.scaffoldTime;
      console.log(`  🏗️  Scaffold Time: ${metrics.scaffoldTime}ms ${thresholdMet ? '✅' : '⚠️'}`);
    }

    if (metrics.e2eTestTime !== undefined) {
      const thresholdMet = metrics.e2eTestTime < PHASE6_THRESHOLDS.e2eTestTime;
      console.log(`  🧪 E2E Test Time: ${metrics.e2eTestTime}ms ${thresholdMet ? '✅' : '⚠️'}`);
    }

    if (metrics.buildTime !== undefined) {
      console.log(`  🔨 Build Time: ${metrics.buildTime}ms`);
    }
  }
}