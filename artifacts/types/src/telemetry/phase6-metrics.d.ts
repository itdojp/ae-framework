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
export declare const PHASE6_THRESHOLDS: {
    readonly scaffoldTime: 30000;
    readonly e2eTestTime: 300000;
    readonly coverage: 80;
    readonly a11yScore: 95;
    readonly performanceScore: 75;
};
export declare class Phase6Telemetry {
    static instrumentScaffoldOperation<T>(operationName: string, operation: () => Promise<T>, metadata?: Record<string, any>): Promise<T>;
    static instrumentE2ETest<T>(testName: string, operation: () => Promise<T>, metadata?: Record<string, any>): Promise<T>;
    static instrumentA11yAudit<T>(auditName: string, operation: () => Promise<T>, metadata?: Record<string, any>): Promise<T>;
    static instrumentBuildOperation<T>(buildType: string, operation: () => Promise<T>, metadata?: Record<string, any>): Promise<T>;
    static recordQualityMetrics(metrics: Partial<Phase6Metrics['quality']>): void;
    static logEfficiencyMetrics(metrics: Partial<Phase6Metrics['efficiency']>): void;
}
