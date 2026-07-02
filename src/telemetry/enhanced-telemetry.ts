/**
 * Enhanced OpenTelemetry implementation with Observable Gauges and standardized metrics
 * Addresses Issue #71 requirements for comprehensive telemetry
 */

import { NodeSDK } from '@opentelemetry/sdk-node';
import { resourceFromAttributes } from '@opentelemetry/resources';
import type { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-grpc';
import { OTLPMetricExporter } from '@opentelemetry/exporter-metrics-otlp-grpc';
import { MeterProvider, PeriodicExportingMetricReader } from '@opentelemetry/sdk-metrics';
import { TraceIdRatioBasedSampler } from '@opentelemetry/sdk-trace-base';
import { metrics, trace } from '@opentelemetry/api';
import type { Meter, Histogram, Counter, UpDownCounter, ObservableGauge } from '@opentelemetry/api';
import { toMessage } from '../utils/error-utils.js';
import type { logs } from '@opentelemetry/api-logs';
import * as os from 'os';
import * as process from 'process';
import { redactSensitiveString, sanitizeTelemetryAttributes } from '../security/sensitive-redaction.js';

// Enhanced configuration with standardized attributes
export interface TelemetryConfig {
  serviceName: string;
  serviceVersion: string;
  serviceNamespace: string;
  environment: string;
  samplingRatio: number;
  enableMetrics: boolean;
  enableTracing: boolean;
  enableLogging: boolean;
  otlpEndpoint?: string;
  otlpMetricsEndpoint?: string;
  otlpTracesEndpoint?: string;
}

// Default configuration following OpenTelemetry standards
const DEFAULT_CONFIG: TelemetryConfig = {
  serviceName: 'ae-framework',
  serviceVersion: '1.0.0',
  serviceNamespace: 'ai-agent-framework',
  environment: process.env['NODE_ENV'] || 'development',
  samplingRatio: parseFloat(process.env['OTEL_TRACES_SAMPLER_ARG'] || '0.1'),
  enableMetrics: process.env['OTEL_METRICS_ENABLED'] !== 'false',
  enableTracing: process.env['OTEL_TRACES_ENABLED'] !== 'false',
  enableLogging: process.env['OTEL_LOGS_ENABLED'] !== 'false',
  ...(process.env['OTEL_EXPORTER_OTLP_ENDPOINT'] ? { otlpEndpoint: process.env['OTEL_EXPORTER_OTLP_ENDPOINT']! } : {}),
  ...(process.env['OTEL_EXPORTER_OTLP_METRICS_ENDPOINT'] ? { otlpMetricsEndpoint: process.env['OTEL_EXPORTER_OTLP_METRICS_ENDPOINT']! } : {}),
  ...(process.env['OTEL_EXPORTER_OTLP_TRACES_ENDPOINT'] ? { otlpTracesEndpoint: process.env['OTEL_EXPORTER_OTLP_TRACES_ENDPOINT']! } : {}),
};

// Standardized attribute names for consistency
export const TELEMETRY_ATTRIBUTES = {
  // Service attributes
  SERVICE_COMPONENT: 'service.component',
  SERVICE_OPERATION: 'service.operation',
  SERVICE_PHASE: 'service.phase',
  
  // Request attributes
  REQUEST_ID: 'request.id',
  REQUEST_TYPE: 'request.type',
  REQUEST_SOURCE: 'request.source',
  
  // Error attributes
  ERROR_TYPE: 'error.type',
  ERROR_CODE: 'error.code',
  ERROR_MESSAGE: 'error.message',
  
  // Performance attributes
  DURATION_MS: 'duration.ms',
  MEMORY_USAGE: 'memory.usage',
  CPU_USAGE: 'cpu.usage',
  
  // Business attributes
  ENTITY_TYPE: 'entity.type',
  ENTITY_ID: 'entity.id',
  PHASE_NAME: 'phase.name',
  QUALITY_SCORE: 'quality.score',
} as const;

export class EnhancedTelemetry {
  private config: TelemetryConfig;
  private sdk?: NodeSDK;
  private meterProvider?: MeterProvider;
  private meter?: Meter;
  
  // Observable Gauges for system metrics
  private systemMetrics: {
    memoryUsage?: ObservableGauge;
    cpuUsage?: ObservableGauge;
    activeConnections?: ObservableGauge;
    processUptime?: ObservableGauge;
  } = {};

  constructor(config: Partial<TelemetryConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.setupMetrics();
  }

  private setupMetrics(): void {
    if (!this.config.enableMetrics) return;

    // Create meter provider with OTLP exporter
    const metricsUrl = this.config.otlpMetricsEndpoint ?? this.config.otlpEndpoint;
    const metricExporter = metricsUrl
      ? new OTLPMetricExporter({ url: metricsUrl })
      : undefined;

    this.meterProvider = new MeterProvider({
      resource: this.createResource(),
      readers: metricExporter ? [
        new PeriodicExportingMetricReader({
          exporter: metricExporter,
          exportIntervalMillis: 30000, // Export every 30 seconds
        }),
      ] : [],
    });

    metrics.setGlobalMeterProvider(this.meterProvider);
    this.meter = metrics.getMeter(this.config.serviceName, this.config.serviceVersion);

    this.setupObservableGauges();
  }

  private setupObservableGauges(): void {
    if (!this.meter) return;

    // Memory usage gauge
    this.systemMetrics.memoryUsage = this.meter.createObservableGauge('system.memory.usage', {
      description: 'Current memory usage in bytes',
      unit: 'bytes',
    });

    // CPU usage gauge
    this.systemMetrics.cpuUsage = this.meter.createObservableGauge('system.cpu.usage', {
      description: 'Current CPU usage percentage',
      unit: 'percent',
    });

    // Process uptime gauge
    this.systemMetrics.processUptime = this.meter.createObservableGauge('system.process.uptime', {
      description: 'Process uptime in seconds',
      unit: 'seconds',
    });

    // Active connections gauge
    this.systemMetrics.activeConnections = this.meter.createObservableGauge('system.connections.active', {
      description: 'Number of active connections',
      unit: 'connections',
    });

    // Local minimal types for attributes and observable result
    type Attrs = Record<string, string | number | boolean>;
    interface MinimalObservableResult {
      observe: (instrument: ObservableGauge | undefined, value: number, attributes?: Attrs) => void;
    }

    // Add observables with proper error handling
    this.meter.addBatchObservableCallback(
      (observableResult) => {
        try {
          const memUsage = process.memoryUsage();
          (observableResult as any).observe(this.systemMetrics.memoryUsage, memUsage.heapUsed, {
            [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'memory',
            type: 'heap_used',
          } as Attrs);
          (observableResult as any).observe(this.systemMetrics.memoryUsage, memUsage.heapTotal, {
            [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'memory',
            type: 'heap_total',
          } as Attrs);
          (observableResult as any).observe(this.systemMetrics.memoryUsage, memUsage.external, {
            [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'memory',
            type: 'external',
          } as Attrs);

          // Process uptime
          (observableResult as any).observe(this.systemMetrics.processUptime, process.uptime(), {
            [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'process',
          } as Attrs);

          // CPU load average (Unix-like systems)
          if (os.loadavg) {
            const load = os.loadavg();
            (observableResult as any).observe(this.systemMetrics.cpuUsage, load[0] ?? 0, {
              [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'cpu',
              period: '1min',
            } as Attrs);
            (observableResult as any).observe(this.systemMetrics.cpuUsage, load[1] ?? 0, {
              [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'cpu',
              period: '5min',
            } as Attrs);
            (observableResult as any).observe(this.systemMetrics.cpuUsage, load[2] ?? 0, {
              [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'cpu',
              period: '15min',
            } as Attrs);
          }
        } catch (error: unknown) {
          console.error('Error collecting system metrics:', toMessage(error));
        }
      },
      [
        this.systemMetrics.memoryUsage!,
        this.systemMetrics.cpuUsage!,
        this.systemMetrics.processUptime!,
      ]
    );
  }

  private createResource(): Resource {
    return resourceFromAttributes({
      [SemanticResourceAttributes.SERVICE_NAME]: this.config.serviceName,
      [SemanticResourceAttributes.SERVICE_VERSION]: this.config.serviceVersion,
      [SemanticResourceAttributes.SERVICE_NAMESPACE]: this.config.serviceNamespace,
      [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: this.config.environment,
      [SemanticResourceAttributes.HOST_NAME]: os.hostname(),
      [SemanticResourceAttributes.HOST_ARCH]: os.arch(),
      [SemanticResourceAttributes.OS_TYPE]: os.type(),
      [SemanticResourceAttributes.OS_VERSION]: os.release(),
      [SemanticResourceAttributes.PROCESS_PID]: process.pid.toString(),
      [SemanticResourceAttributes.PROCESS_RUNTIME_NAME]: 'node',
      [SemanticResourceAttributes.PROCESS_RUNTIME_VERSION]: process.version,
    });
  }

  public initialize(): void {
    try {
      // Configure trace exporter
      const tracesUrl = (this.config.otlpTracesEndpoint ?? this.config.otlpEndpoint);
      const traceExporter = this.config.enableTracing && tracesUrl
        ? new OTLPTraceExporter({ url: tracesUrl })
        : undefined;

      // Create SDK with enhanced configuration (avoid passing undefined fields)
      const sdkConfig: any = {
        resource: this.createResource(),
        sampler: new TraceIdRatioBasedSampler(this.config.samplingRatio),
      };
      if (traceExporter) {
        sdkConfig.traceExporter = traceExporter;
      }
      this.sdk = new NodeSDK(sdkConfig);

      this.sdk.start();

      if (this.config.environment === 'production' || process.env['DEBUG_TELEMETRY']) {
        console.log('📊 Enhanced OpenTelemetry initialized');
        console.log(`   Service: ${this.config.serviceName} v${this.config.serviceVersion}`);
        console.log(`   Environment: ${this.config.environment}`);
        console.log(`   Sampling: ${this.config.samplingRatio * 100}%`);
        console.log(`   Metrics: ${this.config.enableMetrics ? '✅' : '❌'}`);
        console.log(`   Tracing: ${this.config.enableTracing ? '✅' : '❌'}`);
        console.log(`   OTLP: ${this.config.otlpEndpoint ? '✅' : '❌'}`);
      }
    } catch (error: unknown) {
      console.error('❌ Failed to initialize Enhanced OpenTelemetry:', redactSensitiveString(toMessage(error)));
    }
  }

  public async shutdown(): Promise<void> {
    try {
      if (this.sdk) {
        await this.sdk.shutdown();
      }
      if (this.meterProvider) {
        await this.meterProvider.shutdown();
      }
      console.log('📊 Enhanced OpenTelemetry shutdown complete');
    } catch (error: unknown) {
      console.error('❌ Error during Enhanced OpenTelemetry shutdown:', redactSensitiveString(toMessage(error)));
    }
  }

  // Convenience methods for creating standardized spans and metrics
  public createTimer(name: string, attributes?: Record<string, any>) {
    const start = Date.now();
    return {
      end: (additionalAttributes?: Record<string, any>) => {
        const duration = Date.now() - start;
        if (this.meter) {
          const histogram: Histogram = this.meter.createHistogram(`${name}.duration`, {
            description: `Duration of ${name} operation`,
            unit: 'ms',
          });
          histogram.record(duration, sanitizeTelemetryAttributes({ ...attributes, ...additionalAttributes }));
        }
        return duration;
      },
    };
  }

  public recordCounter(name: string, value: number = 1, attributes?: Record<string, any>) {
    if (this.meter) {
      const counter: Counter = this.meter.createCounter(name, {
        description: `Counter for ${name}`,
      });
      counter.add(value, sanitizeTelemetryAttributes(attributes));
    }
  }

  public recordGauge(name: string, value: number, attributes?: Record<string, any>) {
    if (this.meter) {
      const gauge: UpDownCounter = this.meter.createUpDownCounter(name, {
        description: `Gauge for ${name}`,
      });
      gauge.add(value, sanitizeTelemetryAttributes(attributes));
    }
  }

  // Contract violation tracking
  public recordContractViolation(
    violationType: string,
    contractId: string,
    severity: 'low' | 'medium' | 'high' | 'critical',
    attributes?: Record<string, any>
  ) {
    const violationAttributes = sanitizeTelemetryAttributes({
      [TELEMETRY_ATTRIBUTES.ERROR_TYPE]: violationType,
      contract_id: contractId,
      severity,
      ...attributes,
    }) ?? {};

    this.recordCounter('contract.violations.total', 1, violationAttributes);

    // Create a span for contract violation
    const tracer = trace.getTracer(this.config.serviceName);
    const span = tracer.startSpan('contract.violation', {
      attributes: violationAttributes,
    });
    
    span.recordException(new Error(redactSensitiveString(`Contract violation: ${violationType}`)));
    span.end();
  }

  // Quality metrics tracking
  public recordQualityMetrics(metrics: {
    coverage?: number;
    score?: number;
    phase?: string;
    component?: string;
  }) {
    if (metrics.coverage !== undefined) {
      this.recordGauge('quality.coverage', metrics.coverage, {
        [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: metrics.component || 'unknown',
        [TELEMETRY_ATTRIBUTES.PHASE_NAME]: metrics.phase || 'unknown',
      });
    }

    if (metrics.score !== undefined) {
      this.recordGauge('quality.score', metrics.score, {
        [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: metrics.component || 'unknown',
        [TELEMETRY_ATTRIBUTES.PHASE_NAME]: metrics.phase || 'unknown',
      });
    }
  }
}

// Global instance for easy access
export const enhancedTelemetry = new EnhancedTelemetry();

// Auto-initialize if not disabled and not in test environment
if (process.env['DISABLE_ENHANCED_TELEMETRY'] !== 'true' && process.env['NODE_ENV'] !== 'test') {
  enhancedTelemetry.initialize();

  // Graceful shutdown handling (only when auto-initialized and not in test)
  const shutdownHandler = async () => {
    await enhancedTelemetry.shutdown();
  };
  
  // Safe process event handler registration for different environments
  try {
    if (typeof process !== 'undefined' && process.on && typeof process.on === 'function') {
      process.on('SIGTERM', shutdownHandler);
      process.on('SIGINT', shutdownHandler);
    }
  } catch (error) {
    // In some ESM environments, process.on may not be available
    // This is not critical for telemetry functionality
    console.warn('Process event handlers could not be registered:', error instanceof Error ? error.message : String(error));
  }
}
