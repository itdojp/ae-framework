/**
 * Telemetry Service for ae-framework
 * 
 * Provides OpenTelemetry integration for traces, metrics, and logs
 */

import { trace, metrics, Tracer, Meter } from '@opentelemetry/api';
import { logs, Logger } from '@opentelemetry/api-logs';

export enum PhaseType {
  INTENT_ANALYSIS = 'intent_analysis',
  NATURAL_LANGUAGE = 'natural_language', 
  USER_STORIES = 'user_stories',
  VALIDATION = 'validation',
  DOMAIN_MODELING = 'domain_modeling',
  UI_GENERATION = 'ui_generation'
}

export interface QualityMetrics {
  overallScore: number;
  codeQuality: {
    typeErrors: number;
    lintErrors: number;
    testCoverage: number;
  };
  accessibility: {
    wcagCompliance: number;
    contrastRatio: number;
    keyboardNavigation: number;
  };
  performance: {
    buildTime: number;
    bundleSize: number;
    lighthouse: number;
  };
}

export class TelemetryService {
  private tracer: Tracer;
  private meter: Meter;
  private logger: Logger;
  
  // Metrics instruments
  private phaseExecutionHistogram: any;
  private errorRateCounter: any;
  private cegisFixCounter: any;
  private cegisConfidenceHistogram: any;
  private conformanceViolationCounter: any;
  private conformanceLatencyHistogram: any;

  constructor() {
    this.tracer = trace.getTracer('@ae-framework/telemetry');
    this.meter = metrics.getMeter('@ae-framework/telemetry');
    this.logger = logs.getLogger('@ae-framework/telemetry');
    
    this.initializeMetrics();
  }

  private initializeMetrics(): void {
    // Phase execution metrics
    this.phaseExecutionHistogram = this.meter.createHistogram(
      'ae_framework_phase_execution_duration',
      {
        description: 'Duration of phase execution in milliseconds',
        unit: 'ms'
      }
    );

    // Quality metrics (Observable Gauge for snapshot values)
    this.meter.createObservableGauge(
      'ae_framework_quality_score',
      {
        description: 'Quality score for generated artifacts (0-100)'
      }
    ).addCallback((obs) => {
      const latestScore = this.getLatestQualityScore();
      obs.observe(latestScore);
    });

    // Error rate metrics
    this.errorRateCounter = this.meter.createCounter(
      'ae_framework_errors_total',
      {
        description: 'Total number of errors by phase and type'
      }
    );

    // CEGIS related metrics
    this.cegisFixCounter = this.meter.createCounter(
      'ae_framework_cegis_fixes_total',
      {
        description: 'Total number of CEGIS auto-fixes applied'
      }
    );

    this.cegisConfidenceHistogram = this.meter.createHistogram(
      'ae_framework_cegis_confidence',
      {
        description: 'Confidence score of CEGIS fixes',
        unit: 'ratio'
      }
    );

    // Runtime Conformance metrics
    this.conformanceViolationCounter = this.meter.createCounter(
      'ae_framework_conformance_violations_total',
      {
        description: 'Total number of runtime conformance violations'
      }
    );

    this.conformanceLatencyHistogram = this.meter.createHistogram(
      'ae_framework_conformance_check_duration_ms',
      {
        description: 'Duration of runtime conformance checks in milliseconds',
        unit: 'ms'
      }
    );
  }

  async recordPhaseExecution(
    phase: PhaseType,
    duration: number,
    success: boolean,
    qualityMetrics?: QualityMetrics
  ): Promise<void> {
    // Create trace span
    const span = this.tracer.startSpan(`phase_${phase}_execution`);
    span.setAttributes({
      'phase.type': phase,
      'phase.success': success,
      'phase.duration': duration
    });

    // Record metrics
    this.phaseExecutionHistogram.record(duration, {
      phase: phase,
      success: success.toString()
    });

    if (qualityMetrics) {
      // Quality metrics are recorded via ObservableGauge callback
      this.lastQualityScore = qualityMetrics.overallScore;
    }

    if (!success) {
      this.errorRateCounter.add(1, {
        phase: phase,
        error_type: 'execution_failure'
      });
    }

    span.end();
  }

  recordCegisFix(confidence: number, strategy: string): void {
    this.cegisFixCounter.add(1, {
      strategy: strategy
    });

    this.cegisConfidenceHistogram.record(confidence, {
      strategy: strategy
    });
  }

  recordConformanceViolation(
    schemaName: string,
    direction: 'input' | 'output',
    duration: number
  ): void {
    this.conformanceViolationCounter.add(1, {
      schema_name: schemaName,
      direction: direction
    });

    this.conformanceLatencyHistogram.record(duration, {
      schema_name: schemaName,
      direction: direction
    });
  }

  // Internal quality score tracking
  private lastQualityScore: number = 0;

  private getLatestQualityScore(): number {
    return this.lastQualityScore;
  }

  // Convenience method to get tracer
  getTracer(): Tracer {
    return this.tracer;
  }

  // Convenience method to get meter
  getMeter(): Meter {
    return this.meter;
  }

  // Convenience method to get logger
  getLogger(): Logger {
    return this.logger;
  }
}

// Singleton instance
export const telemetryService = new TelemetryService();