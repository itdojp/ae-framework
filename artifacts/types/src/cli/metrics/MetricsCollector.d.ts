import { AEFrameworkConfig } from '../types.js';
export interface TDDViolation {
    timestamp: Date;
    type: 'code_without_test' | 'test_not_run' | 'skip_red_phase' | 'coverage_low';
    file?: string;
    phase: string;
    message: string;
    severity: 'error' | 'warning';
}
export interface PhaseMetrics {
    phase: string;
    startTime: Date;
    endTime?: Date;
    duration?: number;
    artifacts_created: string[];
    tests_written: number;
    tests_passed: number;
    coverage: number;
    violations: TDDViolation[];
}
export interface ProjectMetrics {
    projectName: string;
    startTime: Date;
    phases: PhaseMetrics[];
    totalViolations: number;
    tddCompliance: number;
    overallCoverage: number;
    sessionId: string;
}
export interface Logger {
    warn(message: string): void;
    info(message: string): void;
    error(message: string): void;
}
export declare class MetricsCollector {
    private _config;
    private projectMetrics;
    private metricsPath;
    private logger;
    constructor(_config: AEFrameworkConfig, logger?: Logger);
    private ensureMetricsDirectory;
    private loadOrCreateProjectMetrics;
    startPhase(phaseName: string): void;
    endPhase(): void;
    recordViolation(violation: Omit<TDDViolation, 'timestamp'>): void;
    recordArtifact(artifactPath: string): void;
    recordTestMetrics(testsWritten: number, testsPassed: number, coverage: number): void;
    private getCurrentPhase;
    private updateTDDCompliance;
    private updateOverallCoverage;
    private saveMetrics;
    private saveViolationLog;
    private generateSessionId;
    generateReport(): string;
    private getTopViolations;
    private generateRecommendations;
}
