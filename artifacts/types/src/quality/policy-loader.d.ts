/**
 * Quality Policy Loader and Manager
 * Centralized system for loading and managing quality gates from policy.json
 */
import { z } from 'zod';
export declare const QualityThresholdSchema: z.ZodObject<{
    minScore: z.ZodOptional<z.ZodNumber>;
    maxViolations: z.ZodOptional<z.ZodNumber>;
    blockOnCritical: z.ZodOptional<z.ZodBoolean>;
    blockOnFail: z.ZodOptional<z.ZodBoolean>;
    lines: z.ZodOptional<z.ZodNumber>;
    functions: z.ZodOptional<z.ZodNumber>;
    branches: z.ZodOptional<z.ZodNumber>;
    statements: z.ZodOptional<z.ZodNumber>;
    maxResponseTime: z.ZodOptional<z.ZodNumber>;
    minThroughput: z.ZodOptional<z.ZodNumber>;
    maxMemoryUsage: z.ZodOptional<z.ZodString>;
    performance: z.ZodOptional<z.ZodNumber>;
    accessibility: z.ZodOptional<z.ZodNumber>;
    bestPractices: z.ZodOptional<z.ZodNumber>;
    seo: z.ZodOptional<z.ZodNumber>;
    maxCritical: z.ZodOptional<z.ZodNumber>;
    maxHigh: z.ZodOptional<z.ZodNumber>;
    maxMedium: z.ZodOptional<z.ZodNumber>;
    maxErrors: z.ZodOptional<z.ZodNumber>;
    maxWarnings: z.ZodOptional<z.ZodNumber>;
    blockOnErrors: z.ZodOptional<z.ZodBoolean>;
    minTestsPerFunction: z.ZodOptional<z.ZodNumber>;
    maxCyclomaticComplexity: z.ZodOptional<z.ZodNumber>;
    schemaComplianceScore: z.ZodOptional<z.ZodNumber>;
    maxContractViolations: z.ZodOptional<z.ZodNumber>;
}, "strip", z.ZodTypeAny, {
    branches?: number;
    lines?: number;
    functions?: number;
    statements?: number;
    performance?: number;
    accessibility?: number;
    bestPractices?: number;
    seo?: number;
    minScore?: number;
    maxViolations?: number;
    blockOnCritical?: boolean;
    blockOnFail?: boolean;
    maxResponseTime?: number;
    minThroughput?: number;
    maxMemoryUsage?: string;
    maxCritical?: number;
    maxHigh?: number;
    maxMedium?: number;
    maxErrors?: number;
    maxWarnings?: number;
    blockOnErrors?: boolean;
    minTestsPerFunction?: number;
    maxCyclomaticComplexity?: number;
    schemaComplianceScore?: number;
    maxContractViolations?: number;
}, {
    branches?: number;
    lines?: number;
    functions?: number;
    statements?: number;
    performance?: number;
    accessibility?: number;
    bestPractices?: number;
    seo?: number;
    minScore?: number;
    maxViolations?: number;
    blockOnCritical?: boolean;
    blockOnFail?: boolean;
    maxResponseTime?: number;
    minThroughput?: number;
    maxMemoryUsage?: string;
    maxCritical?: number;
    maxHigh?: number;
    maxMedium?: number;
    maxErrors?: number;
    maxWarnings?: number;
    blockOnErrors?: boolean;
    minTestsPerFunction?: number;
    maxCyclomaticComplexity?: number;
    schemaComplianceScore?: number;
    maxContractViolations?: number;
}>;
export declare const QualityGateSchema: z.ZodObject<{
    name: z.ZodString;
    description: z.ZodString;
    category: z.ZodString;
    enabled: z.ZodBoolean;
    thresholds: z.ZodRecord<z.ZodString, z.ZodObject<{
        minScore: z.ZodOptional<z.ZodNumber>;
        maxViolations: z.ZodOptional<z.ZodNumber>;
        blockOnCritical: z.ZodOptional<z.ZodBoolean>;
        blockOnFail: z.ZodOptional<z.ZodBoolean>;
        lines: z.ZodOptional<z.ZodNumber>;
        functions: z.ZodOptional<z.ZodNumber>;
        branches: z.ZodOptional<z.ZodNumber>;
        statements: z.ZodOptional<z.ZodNumber>;
        maxResponseTime: z.ZodOptional<z.ZodNumber>;
        minThroughput: z.ZodOptional<z.ZodNumber>;
        maxMemoryUsage: z.ZodOptional<z.ZodString>;
        performance: z.ZodOptional<z.ZodNumber>;
        accessibility: z.ZodOptional<z.ZodNumber>;
        bestPractices: z.ZodOptional<z.ZodNumber>;
        seo: z.ZodOptional<z.ZodNumber>;
        maxCritical: z.ZodOptional<z.ZodNumber>;
        maxHigh: z.ZodOptional<z.ZodNumber>;
        maxMedium: z.ZodOptional<z.ZodNumber>;
        maxErrors: z.ZodOptional<z.ZodNumber>;
        maxWarnings: z.ZodOptional<z.ZodNumber>;
        blockOnErrors: z.ZodOptional<z.ZodBoolean>;
        minTestsPerFunction: z.ZodOptional<z.ZodNumber>;
        maxCyclomaticComplexity: z.ZodOptional<z.ZodNumber>;
        schemaComplianceScore: z.ZodOptional<z.ZodNumber>;
        maxContractViolations: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
        performance?: number;
        accessibility?: number;
        bestPractices?: number;
        seo?: number;
        minScore?: number;
        maxViolations?: number;
        blockOnCritical?: boolean;
        blockOnFail?: boolean;
        maxResponseTime?: number;
        minThroughput?: number;
        maxMemoryUsage?: string;
        maxCritical?: number;
        maxHigh?: number;
        maxMedium?: number;
        maxErrors?: number;
        maxWarnings?: number;
        blockOnErrors?: boolean;
        minTestsPerFunction?: number;
        maxCyclomaticComplexity?: number;
        schemaComplianceScore?: number;
        maxContractViolations?: number;
    }, {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
        performance?: number;
        accessibility?: number;
        bestPractices?: number;
        seo?: number;
        minScore?: number;
        maxViolations?: number;
        blockOnCritical?: boolean;
        blockOnFail?: boolean;
        maxResponseTime?: number;
        minThroughput?: number;
        maxMemoryUsage?: string;
        maxCritical?: number;
        maxHigh?: number;
        maxMedium?: number;
        maxErrors?: number;
        maxWarnings?: number;
        blockOnErrors?: boolean;
        minTestsPerFunction?: number;
        maxCyclomaticComplexity?: number;
        schemaComplianceScore?: number;
        maxContractViolations?: number;
    }>>;
    tools: z.ZodArray<z.ZodString, "many">;
    commands: z.ZodObject<{
        test: z.ZodString;
        report: z.ZodOptional<z.ZodString>;
        fix: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        test?: string;
        report?: string;
        fix?: string;
    }, {
        test?: string;
        report?: string;
        fix?: string;
    }>;
}, "strip", z.ZodTypeAny, {
    enabled?: boolean;
    name?: string;
    tools?: string[];
    description?: string;
    thresholds?: Record<string, {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
        performance?: number;
        accessibility?: number;
        bestPractices?: number;
        seo?: number;
        minScore?: number;
        maxViolations?: number;
        blockOnCritical?: boolean;
        blockOnFail?: boolean;
        maxResponseTime?: number;
        minThroughput?: number;
        maxMemoryUsage?: string;
        maxCritical?: number;
        maxHigh?: number;
        maxMedium?: number;
        maxErrors?: number;
        maxWarnings?: number;
        blockOnErrors?: boolean;
        minTestsPerFunction?: number;
        maxCyclomaticComplexity?: number;
        schemaComplianceScore?: number;
        maxContractViolations?: number;
    }>;
    category?: string;
    commands?: {
        test?: string;
        report?: string;
        fix?: string;
    };
}, {
    enabled?: boolean;
    name?: string;
    tools?: string[];
    description?: string;
    thresholds?: Record<string, {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
        performance?: number;
        accessibility?: number;
        bestPractices?: number;
        seo?: number;
        minScore?: number;
        maxViolations?: number;
        blockOnCritical?: boolean;
        blockOnFail?: boolean;
        maxResponseTime?: number;
        minThroughput?: number;
        maxMemoryUsage?: string;
        maxCritical?: number;
        maxHigh?: number;
        maxMedium?: number;
        maxErrors?: number;
        maxWarnings?: number;
        blockOnErrors?: boolean;
        minTestsPerFunction?: number;
        maxCyclomaticComplexity?: number;
        schemaComplianceScore?: number;
        maxContractViolations?: number;
    }>;
    category?: string;
    commands?: {
        test?: string;
        report?: string;
        fix?: string;
    };
}>;
export declare const EnvironmentConfigSchema: z.ZodObject<{
    description: z.ZodString;
    enforcementLevel: z.ZodEnum<["warning", "strict", "blocking"]>;
}, "strip", z.ZodTypeAny, {
    description?: string;
    enforcementLevel?: "strict" | "warning" | "blocking";
}, {
    description?: string;
    enforcementLevel?: "strict" | "warning" | "blocking";
}>;
export declare const CompositeGateSchema: z.ZodObject<{
    description: z.ZodString;
    gates: z.ZodArray<z.ZodString, "many">;
    environments: z.ZodArray<z.ZodString, "many">;
}, "strip", z.ZodTypeAny, {
    description?: string;
    environments?: string[];
    gates?: string[];
}, {
    description?: string;
    environments?: string[];
    gates?: string[];
}>;
export declare const QualityPolicySchema: z.ZodObject<{
    version: z.ZodString;
    lastUpdated: z.ZodString;
    description: z.ZodString;
    environments: z.ZodRecord<z.ZodString, z.ZodObject<{
        description: z.ZodString;
        enforcementLevel: z.ZodEnum<["warning", "strict", "blocking"]>;
    }, "strip", z.ZodTypeAny, {
        description?: string;
        enforcementLevel?: "strict" | "warning" | "blocking";
    }, {
        description?: string;
        enforcementLevel?: "strict" | "warning" | "blocking";
    }>>;
    qualityGates: z.ZodRecord<z.ZodString, z.ZodObject<{
        name: z.ZodString;
        description: z.ZodString;
        category: z.ZodString;
        enabled: z.ZodBoolean;
        thresholds: z.ZodRecord<z.ZodString, z.ZodObject<{
            minScore: z.ZodOptional<z.ZodNumber>;
            maxViolations: z.ZodOptional<z.ZodNumber>;
            blockOnCritical: z.ZodOptional<z.ZodBoolean>;
            blockOnFail: z.ZodOptional<z.ZodBoolean>;
            lines: z.ZodOptional<z.ZodNumber>;
            functions: z.ZodOptional<z.ZodNumber>;
            branches: z.ZodOptional<z.ZodNumber>;
            statements: z.ZodOptional<z.ZodNumber>;
            maxResponseTime: z.ZodOptional<z.ZodNumber>;
            minThroughput: z.ZodOptional<z.ZodNumber>;
            maxMemoryUsage: z.ZodOptional<z.ZodString>;
            performance: z.ZodOptional<z.ZodNumber>;
            accessibility: z.ZodOptional<z.ZodNumber>;
            bestPractices: z.ZodOptional<z.ZodNumber>;
            seo: z.ZodOptional<z.ZodNumber>;
            maxCritical: z.ZodOptional<z.ZodNumber>;
            maxHigh: z.ZodOptional<z.ZodNumber>;
            maxMedium: z.ZodOptional<z.ZodNumber>;
            maxErrors: z.ZodOptional<z.ZodNumber>;
            maxWarnings: z.ZodOptional<z.ZodNumber>;
            blockOnErrors: z.ZodOptional<z.ZodBoolean>;
            minTestsPerFunction: z.ZodOptional<z.ZodNumber>;
            maxCyclomaticComplexity: z.ZodOptional<z.ZodNumber>;
            schemaComplianceScore: z.ZodOptional<z.ZodNumber>;
            maxContractViolations: z.ZodOptional<z.ZodNumber>;
        }, "strip", z.ZodTypeAny, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
            performance?: number;
            accessibility?: number;
            bestPractices?: number;
            seo?: number;
            minScore?: number;
            maxViolations?: number;
            blockOnCritical?: boolean;
            blockOnFail?: boolean;
            maxResponseTime?: number;
            minThroughput?: number;
            maxMemoryUsage?: string;
            maxCritical?: number;
            maxHigh?: number;
            maxMedium?: number;
            maxErrors?: number;
            maxWarnings?: number;
            blockOnErrors?: boolean;
            minTestsPerFunction?: number;
            maxCyclomaticComplexity?: number;
            schemaComplianceScore?: number;
            maxContractViolations?: number;
        }, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
            performance?: number;
            accessibility?: number;
            bestPractices?: number;
            seo?: number;
            minScore?: number;
            maxViolations?: number;
            blockOnCritical?: boolean;
            blockOnFail?: boolean;
            maxResponseTime?: number;
            minThroughput?: number;
            maxMemoryUsage?: string;
            maxCritical?: number;
            maxHigh?: number;
            maxMedium?: number;
            maxErrors?: number;
            maxWarnings?: number;
            blockOnErrors?: boolean;
            minTestsPerFunction?: number;
            maxCyclomaticComplexity?: number;
            schemaComplianceScore?: number;
            maxContractViolations?: number;
        }>>;
        tools: z.ZodArray<z.ZodString, "many">;
        commands: z.ZodObject<{
            test: z.ZodString;
            report: z.ZodOptional<z.ZodString>;
            fix: z.ZodOptional<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            test?: string;
            report?: string;
            fix?: string;
        }, {
            test?: string;
            report?: string;
            fix?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        enabled?: boolean;
        name?: string;
        tools?: string[];
        description?: string;
        thresholds?: Record<string, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
            performance?: number;
            accessibility?: number;
            bestPractices?: number;
            seo?: number;
            minScore?: number;
            maxViolations?: number;
            blockOnCritical?: boolean;
            blockOnFail?: boolean;
            maxResponseTime?: number;
            minThroughput?: number;
            maxMemoryUsage?: string;
            maxCritical?: number;
            maxHigh?: number;
            maxMedium?: number;
            maxErrors?: number;
            maxWarnings?: number;
            blockOnErrors?: boolean;
            minTestsPerFunction?: number;
            maxCyclomaticComplexity?: number;
            schemaComplianceScore?: number;
            maxContractViolations?: number;
        }>;
        category?: string;
        commands?: {
            test?: string;
            report?: string;
            fix?: string;
        };
    }, {
        enabled?: boolean;
        name?: string;
        tools?: string[];
        description?: string;
        thresholds?: Record<string, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
            performance?: number;
            accessibility?: number;
            bestPractices?: number;
            seo?: number;
            minScore?: number;
            maxViolations?: number;
            blockOnCritical?: boolean;
            blockOnFail?: boolean;
            maxResponseTime?: number;
            minThroughput?: number;
            maxMemoryUsage?: string;
            maxCritical?: number;
            maxHigh?: number;
            maxMedium?: number;
            maxErrors?: number;
            maxWarnings?: number;
            blockOnErrors?: boolean;
            minTestsPerFunction?: number;
            maxCyclomaticComplexity?: number;
            schemaComplianceScore?: number;
            maxContractViolations?: number;
        }>;
        category?: string;
        commands?: {
            test?: string;
            report?: string;
            fix?: string;
        };
    }>>;
    compositeGates: z.ZodRecord<z.ZodString, z.ZodObject<{
        description: z.ZodString;
        gates: z.ZodArray<z.ZodString, "many">;
        environments: z.ZodArray<z.ZodString, "many">;
    }, "strip", z.ZodTypeAny, {
        description?: string;
        environments?: string[];
        gates?: string[];
    }, {
        description?: string;
        environments?: string[];
        gates?: string[];
    }>>;
    integrations: z.ZodObject<{
        ci: z.ZodObject<{
            githubActions: z.ZodObject<{
                enabled: z.ZodBoolean;
                workflow: z.ZodString;
                triggerOn: z.ZodArray<z.ZodString, "many">;
                parallelExecution: z.ZodBoolean;
            }, "strip", z.ZodTypeAny, {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            }, {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            }>;
            preCommitHooks: z.ZodObject<{
                enabled: z.ZodBoolean;
                hooks: z.ZodArray<z.ZodString, "many">;
                blocking: z.ZodBoolean;
            }, "strip", z.ZodTypeAny, {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            }, {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            }>;
        }, "strip", z.ZodTypeAny, {
            githubActions?: {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            };
            preCommitHooks?: {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            };
        }, {
            githubActions?: {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            };
            preCommitHooks?: {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            };
        }>;
        monitoring: z.ZodObject<{
            opentelemetry: z.ZodObject<{
                enabled: z.ZodBoolean;
                metricsPrefix: z.ZodString;
                tracingEnabled: z.ZodBoolean;
            }, "strip", z.ZodTypeAny, {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            }, {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            }>;
            dashboards: z.ZodRecord<z.ZodString, z.ZodAny>;
        }, "strip", z.ZodTypeAny, {
            opentelemetry?: {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            };
            dashboards?: Record<string, any>;
        }, {
            opentelemetry?: {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            };
            dashboards?: Record<string, any>;
        }>;
    }, "strip", z.ZodTypeAny, {
        monitoring?: {
            opentelemetry?: {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            };
            dashboards?: Record<string, any>;
        };
        ci?: {
            githubActions?: {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            };
            preCommitHooks?: {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            };
        };
    }, {
        monitoring?: {
            opentelemetry?: {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            };
            dashboards?: Record<string, any>;
        };
        ci?: {
            githubActions?: {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            };
            preCommitHooks?: {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            };
        };
    }>;
    notifications: z.ZodRecord<z.ZodString, z.ZodAny>;
    reporting: z.ZodObject<{
        formats: z.ZodArray<z.ZodString, "many">;
        outputDirectory: z.ZodString;
        retention: z.ZodObject<{
            days: z.ZodNumber;
            maxReports: z.ZodNumber;
        }, "strip", z.ZodTypeAny, {
            days?: number;
            maxReports?: number;
        }, {
            days?: number;
            maxReports?: number;
        }>;
        aggregation: z.ZodObject<{
            enabled: z.ZodBoolean;
            interval: z.ZodString;
            metrics: z.ZodArray<z.ZodString, "many">;
        }, "strip", z.ZodTypeAny, {
            enabled?: boolean;
            metrics?: string[];
            interval?: string;
        }, {
            enabled?: boolean;
            metrics?: string[];
            interval?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        aggregation?: {
            enabled?: boolean;
            metrics?: string[];
            interval?: string;
        };
        formats?: string[];
        outputDirectory?: string;
        retention?: {
            days?: number;
            maxReports?: number;
        };
    }, {
        aggregation?: {
            enabled?: boolean;
            metrics?: string[];
            interval?: string;
        };
        formats?: string[];
        outputDirectory?: string;
        retention?: {
            days?: number;
            maxReports?: number;
        };
    }>;
}, "strip", z.ZodTypeAny, {
    version?: string;
    description?: string;
    environments?: Record<string, {
        description?: string;
        enforcementLevel?: "strict" | "warning" | "blocking";
    }>;
    reporting?: {
        aggregation?: {
            enabled?: boolean;
            metrics?: string[];
            interval?: string;
        };
        formats?: string[];
        outputDirectory?: string;
        retention?: {
            days?: number;
            maxReports?: number;
        };
    };
    integrations?: {
        monitoring?: {
            opentelemetry?: {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            };
            dashboards?: Record<string, any>;
        };
        ci?: {
            githubActions?: {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            };
            preCommitHooks?: {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            };
        };
    };
    lastUpdated?: string;
    qualityGates?: Record<string, {
        enabled?: boolean;
        name?: string;
        tools?: string[];
        description?: string;
        thresholds?: Record<string, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
            performance?: number;
            accessibility?: number;
            bestPractices?: number;
            seo?: number;
            minScore?: number;
            maxViolations?: number;
            blockOnCritical?: boolean;
            blockOnFail?: boolean;
            maxResponseTime?: number;
            minThroughput?: number;
            maxMemoryUsage?: string;
            maxCritical?: number;
            maxHigh?: number;
            maxMedium?: number;
            maxErrors?: number;
            maxWarnings?: number;
            blockOnErrors?: boolean;
            minTestsPerFunction?: number;
            maxCyclomaticComplexity?: number;
            schemaComplianceScore?: number;
            maxContractViolations?: number;
        }>;
        category?: string;
        commands?: {
            test?: string;
            report?: string;
            fix?: string;
        };
    }>;
    compositeGates?: Record<string, {
        description?: string;
        environments?: string[];
        gates?: string[];
    }>;
    notifications?: Record<string, any>;
}, {
    version?: string;
    description?: string;
    environments?: Record<string, {
        description?: string;
        enforcementLevel?: "strict" | "warning" | "blocking";
    }>;
    reporting?: {
        aggregation?: {
            enabled?: boolean;
            metrics?: string[];
            interval?: string;
        };
        formats?: string[];
        outputDirectory?: string;
        retention?: {
            days?: number;
            maxReports?: number;
        };
    };
    integrations?: {
        monitoring?: {
            opentelemetry?: {
                enabled?: boolean;
                metricsPrefix?: string;
                tracingEnabled?: boolean;
            };
            dashboards?: Record<string, any>;
        };
        ci?: {
            githubActions?: {
                enabled?: boolean;
                workflow?: string;
                triggerOn?: string[];
                parallelExecution?: boolean;
            };
            preCommitHooks?: {
                enabled?: boolean;
                hooks?: string[];
                blocking?: boolean;
            };
        };
    };
    lastUpdated?: string;
    qualityGates?: Record<string, {
        enabled?: boolean;
        name?: string;
        tools?: string[];
        description?: string;
        thresholds?: Record<string, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
            performance?: number;
            accessibility?: number;
            bestPractices?: number;
            seo?: number;
            minScore?: number;
            maxViolations?: number;
            blockOnCritical?: boolean;
            blockOnFail?: boolean;
            maxResponseTime?: number;
            minThroughput?: number;
            maxMemoryUsage?: string;
            maxCritical?: number;
            maxHigh?: number;
            maxMedium?: number;
            maxErrors?: number;
            maxWarnings?: number;
            blockOnErrors?: boolean;
            minTestsPerFunction?: number;
            maxCyclomaticComplexity?: number;
            schemaComplianceScore?: number;
            maxContractViolations?: number;
        }>;
        category?: string;
        commands?: {
            test?: string;
            report?: string;
            fix?: string;
        };
    }>;
    compositeGates?: Record<string, {
        description?: string;
        environments?: string[];
        gates?: string[];
    }>;
    notifications?: Record<string, any>;
}>;
export type QualityThreshold = z.infer<typeof QualityThresholdSchema>;
export type QualityGate = z.infer<typeof QualityGateSchema>;
export type EnvironmentConfig = z.infer<typeof EnvironmentConfigSchema>;
export type CompositeGate = z.infer<typeof CompositeGateSchema>;
export type QualityPolicy = z.infer<typeof QualityPolicySchema>;
export interface QualityGateResult {
    gateName: string;
    passed: boolean;
    score?: number;
    violations: string[];
    executionTime: number;
    environment: string;
    threshold: QualityThreshold;
    details?: Record<string, any>;
}
export interface QualityReport {
    timestamp: string;
    environment: string;
    overallScore: number;
    totalGates: number;
    passedGates: number;
    failedGates: number;
    results: QualityGateResult[];
    summary: {
        byCategory: Record<string, {
            passed: number;
            total: number;
        }>;
        executionTime: number;
        blockers: string[];
    };
}
export declare class QualityPolicyLoader {
    private policy;
    private policyPath;
    constructor(policyPath?: string);
    /**
     * Load quality policy from JSON file
     */
    loadPolicy(): QualityPolicy;
    /**
     * Get quality gates for specific environment
     */
    getGatesForEnvironment(environment?: string): QualityGate[];
    /**
     * Get threshold for specific gate and environment
     */
    getThreshold(gateName: string, environment?: string): QualityThreshold;
    /**
     * Check if gate should block on failure for environment
     */
    shouldBlock(gateName: string, environment?: string): boolean;
    /**
     * Get environment configuration
     */
    getEnvironmentConfig(environment: string): EnvironmentConfig;
    /**
     * Get all available quality gates
     */
    getAllGates(): Record<string, QualityGate>;
    /**
     * Get composite gate definition
     */
    getCompositeGate(gateName: string): CompositeGate | null;
    /**
     * Get integration settings
     */
    getIntegrations(): QualityPolicy['integrations'];
    /**
     * Get reporting configuration
     */
    getReportingConfig(): QualityPolicy['reporting'];
    /**
     * Validate gate result against thresholds
     */
    validateGateResult(gateName: string, result: Partial<QualityGateResult>, environment?: string): {
        passed: boolean;
        violations: string[];
    };
    /**
     * Generate quality report
     */
    generateReport(results: QualityGateResult[], environment: string): QualityReport;
    /**
     * Export policy as different formats
     */
    exportPolicy(format?: 'json' | 'yaml' | 'summary'): string;
}
export declare const qualityPolicy: QualityPolicyLoader;
