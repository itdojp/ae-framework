/**
 * Telemetry Service for ae-framework
 *
 * Provides OpenTelemetry integration for traces, metrics, and logs
 */
import { Tracer, Meter } from '@opentelemetry/api';
import { Logger } from '@opentelemetry/api-logs';
export declare enum PhaseType {
    INTENT_ANALYSIS = "intent_analysis",
    NATURAL_LANGUAGE = "natural_language",
    USER_STORIES = "user_stories",
    VALIDATION = "validation",
    DOMAIN_MODELING = "domain_modeling",
    UI_GENERATION = "ui_generation"
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
export declare class TelemetryService {
    private tracer;
    private meter;
    private logger;
    private lastQualityScore;
    private phaseExecutionHistogram;
    private errorRateCounter;
    private cegisFixCounter;
    private cegisConfidenceHistogram;
    private conformanceViolationCounter;
    private conformanceLatencyHistogram;
    constructor();
    private initializeMetrics;
    recordPhaseExecution(phase: PhaseType, duration: number, success: boolean, qualityMetrics?: QualityMetrics): Promise<void>;
    recordCegisFix(confidence: number, strategy: string): void;
    recordConformanceViolation(schemaName: string, direction: 'input' | 'output', duration: number): void;
    private getLatestQualityScore;
    getTracer(): Tracer;
    getMeter(): Meter;
    getLogger(): Logger;
}
export declare const telemetryService: TelemetryService;
