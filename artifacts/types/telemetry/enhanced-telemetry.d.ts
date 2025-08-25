/**
 * Enhanced OpenTelemetry implementation with Observable Gauges and standardized metrics
 * Addresses Issue #71 requirements for comprehensive telemetry
 */
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
export declare const TELEMETRY_ATTRIBUTES: {
    readonly SERVICE_COMPONENT: "service.component";
    readonly SERVICE_OPERATION: "service.operation";
    readonly SERVICE_PHASE: "service.phase";
    readonly REQUEST_ID: "request.id";
    readonly REQUEST_TYPE: "request.type";
    readonly REQUEST_SOURCE: "request.source";
    readonly ERROR_TYPE: "error.type";
    readonly ERROR_CODE: "error.code";
    readonly ERROR_MESSAGE: "error.message";
    readonly DURATION_MS: "duration.ms";
    readonly MEMORY_USAGE: "memory.usage";
    readonly CPU_USAGE: "cpu.usage";
    readonly ENTITY_TYPE: "entity.type";
    readonly ENTITY_ID: "entity.id";
    readonly PHASE_NAME: "phase.name";
    readonly QUALITY_SCORE: "quality.score";
};
export declare class EnhancedTelemetry {
    private config;
    private sdk?;
    private meterProvider?;
    private meter;
    private systemMetrics;
    constructor(config?: Partial<TelemetryConfig>);
    private setupMetrics;
    private setupObservableGauges;
    private createResource;
    initialize(): void;
    shutdown(): Promise<void>;
    createTimer(name: string, attributes?: Record<string, any>): {
        end: (additionalAttributes?: Record<string, any>) => number;
    };
    recordCounter(name: string, value?: number, attributes?: Record<string, any>): void;
    recordGauge(name: string, value: number, attributes?: Record<string, any>): void;
    recordContractViolation(violationType: string, contractId: string, severity: 'low' | 'medium' | 'high' | 'critical', attributes?: Record<string, any>): void;
    recordQualityMetrics(metrics: {
        coverage?: number;
        score?: number;
        phase?: string;
        component?: string;
    }): void;
}
export declare const enhancedTelemetry: EnhancedTelemetry;
