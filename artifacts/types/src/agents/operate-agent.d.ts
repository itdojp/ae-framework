import { z } from 'zod';
export interface OperateAgentConfig {
    deploymentConfig: DeploymentConfig;
    monitoringConfig: MonitoringConfig;
    alertingConfig: AlertingConfig;
    scalingConfig: ScalingConfig;
    securityConfig: SecurityConfig;
    costConfig: CostConfig;
    sloConfig: SloConfig;
    chaosConfig: ChaosConfig;
}
export interface DeploymentConfig {
    cicdProvider: 'github-actions' | 'gitlab-ci' | 'jenkins' | 'tekton';
    environments: string[];
    rolloutStrategy: 'blue-green' | 'canary' | 'rolling';
    healthCheckUrl: string;
    timeoutSeconds: number;
}
export interface MonitoringConfig {
    metricsEndpoint: string;
    logsEndpoint: string;
    tracesEndpoint: string;
    healthEndpoints: string[];
    checkIntervalMs: number;
}
export interface AlertingConfig {
    channels: AlertChannel[];
    thresholds: AlertThreshold[];
    escalationPolicy: EscalationPolicy[];
}
export interface AlertChannel {
    type: 'slack' | 'email' | 'pagerduty' | 'webhook';
    endpoint: string;
    severity: 'low' | 'medium' | 'high' | 'critical';
}
export interface AlertThreshold {
    metric: string;
    condition: 'gt' | 'lt' | 'eq';
    value: number;
    duration: string;
    severity: 'low' | 'medium' | 'high' | 'critical';
}
export interface EscalationPolicy {
    delay: string;
    channels: string[];
}
export interface ScalingConfig {
    minInstances: number;
    maxInstances: number;
    targetCpuPercent: number;
    targetMemoryPercent: number;
    scaleUpCooldown: string;
    scaleDownCooldown: string;
}
export interface SecurityConfig {
    scanSchedule: string;
    vulnerabilityThreshold: 'low' | 'medium' | 'high' | 'critical';
    complianceFrameworks: string[];
    securityEndpoints: string[];
}
export interface CostConfig {
    budgetLimit: number;
    costCenter: string;
    optimizationTargets: string[];
    reportingSchedule: string;
}
export interface SloConfig {
    availability: number;
    latencyP95Ms: number;
    errorRatePercent: number;
    throughputRps: number;
    evaluationWindow: string;
}
export interface ChaosConfig {
    enabled: boolean;
    schedule: string;
    experiments: ChaosExperiment[];
    safetyLimits: SafetyLimits;
}
export interface ChaosExperiment {
    name: string;
    type: 'pod-failure' | 'network-latency' | 'cpu-stress' | 'memory-stress';
    targets: string[];
    duration: string;
    intensity: number;
}
export interface SafetyLimits {
    maxErrorRate: number;
    maxLatencyMs: number;
    minHealthyInstances: number;
}
export declare const DeploymentConfigSchema: z.ZodObject<{
    cicdProvider: z.ZodEnum<["github-actions", "gitlab-ci", "jenkins", "tekton"]>;
    environments: z.ZodArray<z.ZodString, "many">;
    rolloutStrategy: z.ZodEnum<["blue-green", "canary", "rolling"]>;
    healthCheckUrl: z.ZodString;
    timeoutSeconds: z.ZodNumber;
}, "strip", z.ZodTypeAny, {
    cicdProvider?: "github-actions" | "gitlab-ci" | "jenkins" | "tekton";
    environments?: string[];
    rolloutStrategy?: "blue-green" | "canary" | "rolling";
    healthCheckUrl?: string;
    timeoutSeconds?: number;
}, {
    cicdProvider?: "github-actions" | "gitlab-ci" | "jenkins" | "tekton";
    environments?: string[];
    rolloutStrategy?: "blue-green" | "canary" | "rolling";
    healthCheckUrl?: string;
    timeoutSeconds?: number;
}>;
export declare const MonitoringConfigSchema: z.ZodObject<{
    metricsEndpoint: z.ZodString;
    logsEndpoint: z.ZodString;
    tracesEndpoint: z.ZodString;
    healthEndpoints: z.ZodArray<z.ZodString, "many">;
    checkIntervalMs: z.ZodNumber;
}, "strip", z.ZodTypeAny, {
    metricsEndpoint?: string;
    logsEndpoint?: string;
    tracesEndpoint?: string;
    healthEndpoints?: string[];
    checkIntervalMs?: number;
}, {
    metricsEndpoint?: string;
    logsEndpoint?: string;
    tracesEndpoint?: string;
    healthEndpoints?: string[];
    checkIntervalMs?: number;
}>;
export declare const AlertingConfigSchema: z.ZodObject<{
    channels: z.ZodArray<z.ZodObject<{
        type: z.ZodEnum<["slack", "email", "pagerduty", "webhook"]>;
        endpoint: z.ZodString;
        severity: z.ZodEnum<["low", "medium", "high", "critical"]>;
    }, "strip", z.ZodTypeAny, {
        type?: "email" | "slack" | "pagerduty" | "webhook";
        severity?: "critical" | "low" | "medium" | "high";
        endpoint?: string;
    }, {
        type?: "email" | "slack" | "pagerduty" | "webhook";
        severity?: "critical" | "low" | "medium" | "high";
        endpoint?: string;
    }>, "many">;
    thresholds: z.ZodArray<z.ZodObject<{
        metric: z.ZodString;
        condition: z.ZodEnum<["gt", "lt", "eq"]>;
        value: z.ZodNumber;
        duration: z.ZodString;
        severity: z.ZodEnum<["low", "medium", "high", "critical"]>;
    }, "strip", z.ZodTypeAny, {
        value?: number;
        severity?: "critical" | "low" | "medium" | "high";
        metric?: string;
        condition?: "gt" | "lt" | "eq";
        duration?: string;
    }, {
        value?: number;
        severity?: "critical" | "low" | "medium" | "high";
        metric?: string;
        condition?: "gt" | "lt" | "eq";
        duration?: string;
    }>, "many">;
    escalationPolicy: z.ZodArray<z.ZodObject<{
        delay: z.ZodString;
        channels: z.ZodArray<z.ZodString, "many">;
    }, "strip", z.ZodTypeAny, {
        channels?: string[];
        delay?: string;
    }, {
        channels?: string[];
        delay?: string;
    }>, "many">;
}, "strip", z.ZodTypeAny, {
    channels?: {
        type?: "email" | "slack" | "pagerduty" | "webhook";
        severity?: "critical" | "low" | "medium" | "high";
        endpoint?: string;
    }[];
    thresholds?: {
        value?: number;
        severity?: "critical" | "low" | "medium" | "high";
        metric?: string;
        condition?: "gt" | "lt" | "eq";
        duration?: string;
    }[];
    escalationPolicy?: {
        channels?: string[];
        delay?: string;
    }[];
}, {
    channels?: {
        type?: "email" | "slack" | "pagerduty" | "webhook";
        severity?: "critical" | "low" | "medium" | "high";
        endpoint?: string;
    }[];
    thresholds?: {
        value?: number;
        severity?: "critical" | "low" | "medium" | "high";
        metric?: string;
        condition?: "gt" | "lt" | "eq";
        duration?: string;
    }[];
    escalationPolicy?: {
        channels?: string[];
        delay?: string;
    }[];
}>;
export declare const ScalingConfigSchema: z.ZodObject<{
    minInstances: z.ZodNumber;
    maxInstances: z.ZodNumber;
    targetCpuPercent: z.ZodNumber;
    targetMemoryPercent: z.ZodNumber;
    scaleUpCooldown: z.ZodString;
    scaleDownCooldown: z.ZodString;
}, "strip", z.ZodTypeAny, {
    minInstances?: number;
    maxInstances?: number;
    targetCpuPercent?: number;
    targetMemoryPercent?: number;
    scaleUpCooldown?: string;
    scaleDownCooldown?: string;
}, {
    minInstances?: number;
    maxInstances?: number;
    targetCpuPercent?: number;
    targetMemoryPercent?: number;
    scaleUpCooldown?: string;
    scaleDownCooldown?: string;
}>;
export declare const SecurityConfigSchema: z.ZodObject<{
    scanSchedule: z.ZodString;
    vulnerabilityThreshold: z.ZodEnum<["low", "medium", "high", "critical"]>;
    complianceFrameworks: z.ZodArray<z.ZodString, "many">;
    securityEndpoints: z.ZodArray<z.ZodString, "many">;
}, "strip", z.ZodTypeAny, {
    scanSchedule?: string;
    vulnerabilityThreshold?: "critical" | "low" | "medium" | "high";
    complianceFrameworks?: string[];
    securityEndpoints?: string[];
}, {
    scanSchedule?: string;
    vulnerabilityThreshold?: "critical" | "low" | "medium" | "high";
    complianceFrameworks?: string[];
    securityEndpoints?: string[];
}>;
export declare const CostConfigSchema: z.ZodObject<{
    budgetLimit: z.ZodNumber;
    costCenter: z.ZodString;
    optimizationTargets: z.ZodArray<z.ZodString, "many">;
    reportingSchedule: z.ZodString;
}, "strip", z.ZodTypeAny, {
    budgetLimit?: number;
    costCenter?: string;
    optimizationTargets?: string[];
    reportingSchedule?: string;
}, {
    budgetLimit?: number;
    costCenter?: string;
    optimizationTargets?: string[];
    reportingSchedule?: string;
}>;
export declare const SloConfigSchema: z.ZodObject<{
    availability: z.ZodNumber;
    latencyP95Ms: z.ZodNumber;
    errorRatePercent: z.ZodNumber;
    throughputRps: z.ZodNumber;
    evaluationWindow: z.ZodString;
}, "strip", z.ZodTypeAny, {
    availability?: number;
    latencyP95Ms?: number;
    errorRatePercent?: number;
    throughputRps?: number;
    evaluationWindow?: string;
}, {
    availability?: number;
    latencyP95Ms?: number;
    errorRatePercent?: number;
    throughputRps?: number;
    evaluationWindow?: string;
}>;
export declare const ChaosConfigSchema: z.ZodObject<{
    enabled: z.ZodBoolean;
    schedule: z.ZodString;
    experiments: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        type: z.ZodEnum<["pod-failure", "network-latency", "cpu-stress", "memory-stress"]>;
        targets: z.ZodArray<z.ZodString, "many">;
        duration: z.ZodString;
        intensity: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
        name?: string;
        duration?: string;
        targets?: string[];
        intensity?: number;
    }, {
        type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
        name?: string;
        duration?: string;
        targets?: string[];
        intensity?: number;
    }>, "many">;
    safetyLimits: z.ZodObject<{
        maxErrorRate: z.ZodNumber;
        maxLatencyMs: z.ZodNumber;
        minHealthyInstances: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        maxErrorRate?: number;
        maxLatencyMs?: number;
        minHealthyInstances?: number;
    }, {
        maxErrorRate?: number;
        maxLatencyMs?: number;
        minHealthyInstances?: number;
    }>;
}, "strip", z.ZodTypeAny, {
    enabled?: boolean;
    schedule?: string;
    experiments?: {
        type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
        name?: string;
        duration?: string;
        targets?: string[];
        intensity?: number;
    }[];
    safetyLimits?: {
        maxErrorRate?: number;
        maxLatencyMs?: number;
        minHealthyInstances?: number;
    };
}, {
    enabled?: boolean;
    schedule?: string;
    experiments?: {
        type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
        name?: string;
        duration?: string;
        targets?: string[];
        intensity?: number;
    }[];
    safetyLimits?: {
        maxErrorRate?: number;
        maxLatencyMs?: number;
        minHealthyInstances?: number;
    };
}>;
export declare const OperateAgentConfigSchema: z.ZodObject<{
    deploymentConfig: z.ZodObject<{
        cicdProvider: z.ZodEnum<["github-actions", "gitlab-ci", "jenkins", "tekton"]>;
        environments: z.ZodArray<z.ZodString, "many">;
        rolloutStrategy: z.ZodEnum<["blue-green", "canary", "rolling"]>;
        healthCheckUrl: z.ZodString;
        timeoutSeconds: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        cicdProvider?: "github-actions" | "gitlab-ci" | "jenkins" | "tekton";
        environments?: string[];
        rolloutStrategy?: "blue-green" | "canary" | "rolling";
        healthCheckUrl?: string;
        timeoutSeconds?: number;
    }, {
        cicdProvider?: "github-actions" | "gitlab-ci" | "jenkins" | "tekton";
        environments?: string[];
        rolloutStrategy?: "blue-green" | "canary" | "rolling";
        healthCheckUrl?: string;
        timeoutSeconds?: number;
    }>;
    monitoringConfig: z.ZodObject<{
        metricsEndpoint: z.ZodString;
        logsEndpoint: z.ZodString;
        tracesEndpoint: z.ZodString;
        healthEndpoints: z.ZodArray<z.ZodString, "many">;
        checkIntervalMs: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        metricsEndpoint?: string;
        logsEndpoint?: string;
        tracesEndpoint?: string;
        healthEndpoints?: string[];
        checkIntervalMs?: number;
    }, {
        metricsEndpoint?: string;
        logsEndpoint?: string;
        tracesEndpoint?: string;
        healthEndpoints?: string[];
        checkIntervalMs?: number;
    }>;
    alertingConfig: z.ZodObject<{
        channels: z.ZodArray<z.ZodObject<{
            type: z.ZodEnum<["slack", "email", "pagerduty", "webhook"]>;
            endpoint: z.ZodString;
            severity: z.ZodEnum<["low", "medium", "high", "critical"]>;
        }, "strip", z.ZodTypeAny, {
            type?: "email" | "slack" | "pagerduty" | "webhook";
            severity?: "critical" | "low" | "medium" | "high";
            endpoint?: string;
        }, {
            type?: "email" | "slack" | "pagerduty" | "webhook";
            severity?: "critical" | "low" | "medium" | "high";
            endpoint?: string;
        }>, "many">;
        thresholds: z.ZodArray<z.ZodObject<{
            metric: z.ZodString;
            condition: z.ZodEnum<["gt", "lt", "eq"]>;
            value: z.ZodNumber;
            duration: z.ZodString;
            severity: z.ZodEnum<["low", "medium", "high", "critical"]>;
        }, "strip", z.ZodTypeAny, {
            value?: number;
            severity?: "critical" | "low" | "medium" | "high";
            metric?: string;
            condition?: "gt" | "lt" | "eq";
            duration?: string;
        }, {
            value?: number;
            severity?: "critical" | "low" | "medium" | "high";
            metric?: string;
            condition?: "gt" | "lt" | "eq";
            duration?: string;
        }>, "many">;
        escalationPolicy: z.ZodArray<z.ZodObject<{
            delay: z.ZodString;
            channels: z.ZodArray<z.ZodString, "many">;
        }, "strip", z.ZodTypeAny, {
            channels?: string[];
            delay?: string;
        }, {
            channels?: string[];
            delay?: string;
        }>, "many">;
    }, "strip", z.ZodTypeAny, {
        channels?: {
            type?: "email" | "slack" | "pagerduty" | "webhook";
            severity?: "critical" | "low" | "medium" | "high";
            endpoint?: string;
        }[];
        thresholds?: {
            value?: number;
            severity?: "critical" | "low" | "medium" | "high";
            metric?: string;
            condition?: "gt" | "lt" | "eq";
            duration?: string;
        }[];
        escalationPolicy?: {
            channels?: string[];
            delay?: string;
        }[];
    }, {
        channels?: {
            type?: "email" | "slack" | "pagerduty" | "webhook";
            severity?: "critical" | "low" | "medium" | "high";
            endpoint?: string;
        }[];
        thresholds?: {
            value?: number;
            severity?: "critical" | "low" | "medium" | "high";
            metric?: string;
            condition?: "gt" | "lt" | "eq";
            duration?: string;
        }[];
        escalationPolicy?: {
            channels?: string[];
            delay?: string;
        }[];
    }>;
    scalingConfig: z.ZodObject<{
        minInstances: z.ZodNumber;
        maxInstances: z.ZodNumber;
        targetCpuPercent: z.ZodNumber;
        targetMemoryPercent: z.ZodNumber;
        scaleUpCooldown: z.ZodString;
        scaleDownCooldown: z.ZodString;
    }, "strip", z.ZodTypeAny, {
        minInstances?: number;
        maxInstances?: number;
        targetCpuPercent?: number;
        targetMemoryPercent?: number;
        scaleUpCooldown?: string;
        scaleDownCooldown?: string;
    }, {
        minInstances?: number;
        maxInstances?: number;
        targetCpuPercent?: number;
        targetMemoryPercent?: number;
        scaleUpCooldown?: string;
        scaleDownCooldown?: string;
    }>;
    securityConfig: z.ZodObject<{
        scanSchedule: z.ZodString;
        vulnerabilityThreshold: z.ZodEnum<["low", "medium", "high", "critical"]>;
        complianceFrameworks: z.ZodArray<z.ZodString, "many">;
        securityEndpoints: z.ZodArray<z.ZodString, "many">;
    }, "strip", z.ZodTypeAny, {
        scanSchedule?: string;
        vulnerabilityThreshold?: "critical" | "low" | "medium" | "high";
        complianceFrameworks?: string[];
        securityEndpoints?: string[];
    }, {
        scanSchedule?: string;
        vulnerabilityThreshold?: "critical" | "low" | "medium" | "high";
        complianceFrameworks?: string[];
        securityEndpoints?: string[];
    }>;
    costConfig: z.ZodObject<{
        budgetLimit: z.ZodNumber;
        costCenter: z.ZodString;
        optimizationTargets: z.ZodArray<z.ZodString, "many">;
        reportingSchedule: z.ZodString;
    }, "strip", z.ZodTypeAny, {
        budgetLimit?: number;
        costCenter?: string;
        optimizationTargets?: string[];
        reportingSchedule?: string;
    }, {
        budgetLimit?: number;
        costCenter?: string;
        optimizationTargets?: string[];
        reportingSchedule?: string;
    }>;
    sloConfig: z.ZodObject<{
        availability: z.ZodNumber;
        latencyP95Ms: z.ZodNumber;
        errorRatePercent: z.ZodNumber;
        throughputRps: z.ZodNumber;
        evaluationWindow: z.ZodString;
    }, "strip", z.ZodTypeAny, {
        availability?: number;
        latencyP95Ms?: number;
        errorRatePercent?: number;
        throughputRps?: number;
        evaluationWindow?: string;
    }, {
        availability?: number;
        latencyP95Ms?: number;
        errorRatePercent?: number;
        throughputRps?: number;
        evaluationWindow?: string;
    }>;
    chaosConfig: z.ZodObject<{
        enabled: z.ZodBoolean;
        schedule: z.ZodString;
        experiments: z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            type: z.ZodEnum<["pod-failure", "network-latency", "cpu-stress", "memory-stress"]>;
            targets: z.ZodArray<z.ZodString, "many">;
            duration: z.ZodString;
            intensity: z.ZodNumber;
        }, "strip", z.ZodTypeAny, {
            type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
            name?: string;
            duration?: string;
            targets?: string[];
            intensity?: number;
        }, {
            type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
            name?: string;
            duration?: string;
            targets?: string[];
            intensity?: number;
        }>, "many">;
        safetyLimits: z.ZodObject<{
            maxErrorRate: z.ZodNumber;
            maxLatencyMs: z.ZodNumber;
            minHealthyInstances: z.ZodNumber;
        }, "strip", z.ZodTypeAny, {
            maxErrorRate?: number;
            maxLatencyMs?: number;
            minHealthyInstances?: number;
        }, {
            maxErrorRate?: number;
            maxLatencyMs?: number;
            minHealthyInstances?: number;
        }>;
    }, "strip", z.ZodTypeAny, {
        enabled?: boolean;
        schedule?: string;
        experiments?: {
            type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
            name?: string;
            duration?: string;
            targets?: string[];
            intensity?: number;
        }[];
        safetyLimits?: {
            maxErrorRate?: number;
            maxLatencyMs?: number;
            minHealthyInstances?: number;
        };
    }, {
        enabled?: boolean;
        schedule?: string;
        experiments?: {
            type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
            name?: string;
            duration?: string;
            targets?: string[];
            intensity?: number;
        }[];
        safetyLimits?: {
            maxErrorRate?: number;
            maxLatencyMs?: number;
            minHealthyInstances?: number;
        };
    }>;
}, "strip", z.ZodTypeAny, {
    deploymentConfig?: {
        cicdProvider?: "github-actions" | "gitlab-ci" | "jenkins" | "tekton";
        environments?: string[];
        rolloutStrategy?: "blue-green" | "canary" | "rolling";
        healthCheckUrl?: string;
        timeoutSeconds?: number;
    };
    monitoringConfig?: {
        metricsEndpoint?: string;
        logsEndpoint?: string;
        tracesEndpoint?: string;
        healthEndpoints?: string[];
        checkIntervalMs?: number;
    };
    alertingConfig?: {
        channels?: {
            type?: "email" | "slack" | "pagerduty" | "webhook";
            severity?: "critical" | "low" | "medium" | "high";
            endpoint?: string;
        }[];
        thresholds?: {
            value?: number;
            severity?: "critical" | "low" | "medium" | "high";
            metric?: string;
            condition?: "gt" | "lt" | "eq";
            duration?: string;
        }[];
        escalationPolicy?: {
            channels?: string[];
            delay?: string;
        }[];
    };
    scalingConfig?: {
        minInstances?: number;
        maxInstances?: number;
        targetCpuPercent?: number;
        targetMemoryPercent?: number;
        scaleUpCooldown?: string;
        scaleDownCooldown?: string;
    };
    securityConfig?: {
        scanSchedule?: string;
        vulnerabilityThreshold?: "critical" | "low" | "medium" | "high";
        complianceFrameworks?: string[];
        securityEndpoints?: string[];
    };
    costConfig?: {
        budgetLimit?: number;
        costCenter?: string;
        optimizationTargets?: string[];
        reportingSchedule?: string;
    };
    sloConfig?: {
        availability?: number;
        latencyP95Ms?: number;
        errorRatePercent?: number;
        throughputRps?: number;
        evaluationWindow?: string;
    };
    chaosConfig?: {
        enabled?: boolean;
        schedule?: string;
        experiments?: {
            type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
            name?: string;
            duration?: string;
            targets?: string[];
            intensity?: number;
        }[];
        safetyLimits?: {
            maxErrorRate?: number;
            maxLatencyMs?: number;
            minHealthyInstances?: number;
        };
    };
}, {
    deploymentConfig?: {
        cicdProvider?: "github-actions" | "gitlab-ci" | "jenkins" | "tekton";
        environments?: string[];
        rolloutStrategy?: "blue-green" | "canary" | "rolling";
        healthCheckUrl?: string;
        timeoutSeconds?: number;
    };
    monitoringConfig?: {
        metricsEndpoint?: string;
        logsEndpoint?: string;
        tracesEndpoint?: string;
        healthEndpoints?: string[];
        checkIntervalMs?: number;
    };
    alertingConfig?: {
        channels?: {
            type?: "email" | "slack" | "pagerduty" | "webhook";
            severity?: "critical" | "low" | "medium" | "high";
            endpoint?: string;
        }[];
        thresholds?: {
            value?: number;
            severity?: "critical" | "low" | "medium" | "high";
            metric?: string;
            condition?: "gt" | "lt" | "eq";
            duration?: string;
        }[];
        escalationPolicy?: {
            channels?: string[];
            delay?: string;
        }[];
    };
    scalingConfig?: {
        minInstances?: number;
        maxInstances?: number;
        targetCpuPercent?: number;
        targetMemoryPercent?: number;
        scaleUpCooldown?: string;
        scaleDownCooldown?: string;
    };
    securityConfig?: {
        scanSchedule?: string;
        vulnerabilityThreshold?: "critical" | "low" | "medium" | "high";
        complianceFrameworks?: string[];
        securityEndpoints?: string[];
    };
    costConfig?: {
        budgetLimit?: number;
        costCenter?: string;
        optimizationTargets?: string[];
        reportingSchedule?: string;
    };
    sloConfig?: {
        availability?: number;
        latencyP95Ms?: number;
        errorRatePercent?: number;
        throughputRps?: number;
        evaluationWindow?: string;
    };
    chaosConfig?: {
        enabled?: boolean;
        schedule?: string;
        experiments?: {
            type?: "pod-failure" | "network-latency" | "cpu-stress" | "memory-stress";
            name?: string;
            duration?: string;
            targets?: string[];
            intensity?: number;
        }[];
        safetyLimits?: {
            maxErrorRate?: number;
            maxLatencyMs?: number;
            minHealthyInstances?: number;
        };
    };
}>;
export declare class OperateAgent {
    private logger;
    private config;
    private deploymentHistory;
    private incidentHistory;
    private performanceMetrics;
    private costMetrics;
    constructor(config: OperateAgentConfig);
    deployApplication(params: DeploymentParams): Promise<DeploymentResult>;
    monitorHealth(): Promise<HealthStatus>;
    analyzeLogs(params: LogAnalysisParams): Promise<LogAnalysisResult>;
    manageIncident(params: IncidentParams): Promise<IncidentResult>;
    optimizePerformance(params: PerformanceOptimizationParams): Promise<PerformanceOptimizationResult>;
    scaleResources(params: ScalingParams): Promise<ScalingResult>;
    runChaosTest(params: ChaosTestParams): Promise<ChaosTestResult>;
    trackSlo(): Promise<SloStatus>;
    analyzeCosts(params: CostAnalysisParams): Promise<CostAnalysisResult>;
    securityScan(params: SecurityScanParams): Promise<SecurityScanResult>;
    private generateDeploymentId;
    private generateIncidentId;
    private generateChaosTestId;
    private generateSecurityScanId;
    private runPreDeploymentChecks;
    private executeDeploymentStrategy;
    private verifyDeployment;
    private checkEndpointHealth;
    private fetchLogs;
    private performLogAnalysis;
    private createIncident;
    private updateIncident;
    private resolveIncident;
    private escalateIncident;
    private collectPerformanceMetrics;
    private generateOptimizationRecommendations;
    private applyOptimizations;
    private getCurrentScale;
    private calculateTargetScale;
    private executeScaling;
    private performChaosPreChecks;
    private executeChaosExperiment;
    private collectSloMetrics;
    private evaluateSloCompliance;
    private collectCostMetrics;
    private generateCostOptimizations;
    private calculateProjectedSavings;
    private evaluateBudgetStatus;
    private scanForVulnerabilities;
    private checkCompliance;
    private generateSecurityRecommendations;
    private calculateRiskScore;
}
export interface DeploymentParams {
    environment: string;
    version: string;
    strategy?: 'blue-green' | 'canary' | 'rolling';
    rollbackOnFailure?: boolean;
    healthCheckTimeout?: number;
}
export interface DeploymentResult {
    success: boolean;
    deploymentId: string;
    message: string;
    rollbackPerformed?: boolean;
}
export interface DeploymentRecord {
    id: string;
    environment: string;
    version: string;
    strategy: string;
    status: 'success' | 'failed' | 'rolled-back';
    startTime: Date;
    endTime: Date;
    duration: number;
    rollbackOnFailure: boolean;
}
export interface HealthStatus {
    overall: 'healthy' | 'unhealthy';
    timestamp: Date;
    details: Array<{
        endpoint: string;
        status: {
            healthy: boolean;
            error?: string;
        };
    }>;
}
export interface LogAnalysisParams {
    startTime: Date;
    endTime: Date;
    logLevel?: 'debug' | 'info' | 'warn' | 'error';
    service?: string;
    query?: string;
}
export interface LogAnalysisResult {
    totalLogs: number;
    errorLogs: number;
    warningLogs: number;
    patterns: LogPattern[];
    anomalies: LogAnomaly[];
    recommendations: string[];
}
export interface LogEntry {
    timestamp: Date;
    level: string;
    message: string;
    service: string;
    metadata?: Record<string, any>;
}
export interface LogPattern {
    pattern: string;
    frequency: number;
    severity: string;
}
export interface LogAnomaly {
    type: string;
    description: string;
    severity: string;
    occurrences: number;
}
export interface IncidentParams {
    action: 'create' | 'update' | 'resolve' | 'escalate';
    incidentId?: string;
    title?: string;
    description?: string;
    severity?: 'low' | 'medium' | 'high' | 'critical';
    assignee?: string;
    updateNotes?: string;
    resolution?: string;
}
export interface IncidentResult {
    incidentId: string;
    action: string;
    message: string;
}
export interface IncidentRecord {
    id: string;
    title: string;
    description: string;
    severity: 'low' | 'medium' | 'high' | 'critical';
    status: 'open' | 'assigned' | 'in-progress' | 'resolved' | 'closed';
    createdAt: Date;
    updatedAt: Date;
    assignee?: string;
    resolution?: string;
}
export interface PerformanceOptimizationParams {
    service?: string;
    timeWindow: string;
    metrics: string[];
    autoApply?: boolean;
}
export interface PerformanceOptimizationResult {
    metrics: PerformanceMetrics;
    recommendations: OptimizationRecommendation[];
    appliedOptimizations: AppliedOptimization[];
    timestamp: Date;
}
export interface PerformanceMetrics {
    [key: string]: any;
}
export interface OptimizationRecommendation {
    type: string;
    description: string;
    impact: 'low' | 'medium' | 'high';
    effort: 'low' | 'medium' | 'high';
    estimatedImprovement: string;
}
export interface AppliedOptimization {
    recommendation: string;
    applied: boolean;
    result?: string;
    error?: string;
}
export interface ScalingParams {
    service: string;
    action?: 'auto' | 'scale-up' | 'scale-down';
    targetInstances?: number;
    force?: boolean;
}
export interface ScalingResult {
    action: 'scale-up' | 'scale-down' | 'none';
    currentInstances: number;
    targetInstances: number;
    message: string;
}
export interface ChaosTestParams {
    experiment: string;
    dryRun?: boolean;
    duration?: string;
    intensity?: number;
}
export interface ChaosTestResult {
    testId: string;
    experiment: string;
    startTime: Date;
    endTime: Date;
    duration: number;
    success: boolean;
    impact: any;
    observations: any[];
}
export interface SloStatus {
    availability: {
        target: number;
        actual: number;
        compliant: boolean;
    };
    latency: {
        target: number;
        actual: number;
        compliant: boolean;
    };
    errorRate: {
        target: number;
        actual: number;
        compliant: boolean;
    };
    throughput: {
        target: number;
        actual: number;
        compliant: boolean;
    };
    timestamp: Date;
}
export interface CostAnalysisParams {
    timeWindow: string;
    services?: string[];
    includePredictions?: boolean;
}
export interface CostAnalysisResult {
    currentCosts: CostMetrics;
    recommendations: CostOptimization[];
    projectedSavings: number;
    budgetStatus: 'under' | 'at' | 'over';
    timestamp: Date;
}
export interface CostMetrics {
    [key: string]: any;
}
export interface CostOptimization {
    type: string;
    description: string;
    estimatedSavings: number;
    effort: 'low' | 'medium' | 'high';
    risk: 'low' | 'medium' | 'high';
}
export interface SecurityScanParams {
    scope?: 'infrastructure' | 'application' | 'dependencies' | 'all';
    includeCompliance?: boolean;
    frameworks?: string[];
}
export interface SecurityScanResult {
    scanId: string;
    startTime: Date;
    endTime: Date;
    vulnerabilities: Vulnerability[];
    complianceStatus: ComplianceStatus;
    recommendations: SecurityRecommendation[];
    riskScore: number;
}
export interface Vulnerability {
    id: string;
    severity: 'low' | 'medium' | 'high' | 'critical';
    type: string;
    description: string;
    affected: string[];
    remediation?: string;
}
export interface ComplianceStatus {
    [framework: string]: {
        compliant: boolean;
        score: number;
        issues: string[];
    };
}
export interface SecurityRecommendation {
    type: string;
    description: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    effort: 'low' | 'medium' | 'high';
}
