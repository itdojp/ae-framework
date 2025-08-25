/**
 * CEGIS (Counter-Example Guided Inductive Synthesis) Failure Artifact Schema
 *
 * Standardized schema for capturing and processing failure artifacts
 * to enable automated specification/code repair and synthesis
 */
import { z } from 'zod';
export declare const FailureSeveritySchema: z.ZodEnum<["critical", "major", "minor", "info"]>;
export type FailureSeverity = z.infer<typeof FailureSeveritySchema>;
export declare const FailureCategorySchema: z.ZodEnum<["specification_mismatch", "contract_violation", "type_error", "runtime_error", "performance_regression", "security_violation", "quality_gate_failure", "drift_detection", "test_failure"]>;
export type FailureCategory = z.infer<typeof FailureCategorySchema>;
export declare const FailureLocationSchema: z.ZodObject<{
    file: z.ZodString;
    line: z.ZodOptional<z.ZodNumber>;
    column: z.ZodOptional<z.ZodNumber>;
    function: z.ZodOptional<z.ZodString>;
    module: z.ZodOptional<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    function?: string;
    line?: number;
    file?: string;
    module?: string;
    column?: number;
}, {
    function?: string;
    line?: number;
    file?: string;
    module?: string;
    column?: number;
}>;
export type FailureLocation = z.infer<typeof FailureLocationSchema>;
export declare const FailureContextSchema: z.ZodObject<{
    environment: z.ZodDefault<z.ZodString>;
    phase: z.ZodOptional<z.ZodString>;
    component: z.ZodOptional<z.ZodString>;
    timestamp: z.ZodString;
    commitHash: z.ZodOptional<z.ZodString>;
    branch: z.ZodOptional<z.ZodString>;
    userId: z.ZodOptional<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    environment?: string;
    timestamp?: string;
    component?: string;
    phase?: string;
    branch?: string;
    commitHash?: string;
    userId?: string;
}, {
    environment?: string;
    timestamp?: string;
    component?: string;
    phase?: string;
    branch?: string;
    commitHash?: string;
    userId?: string;
}>;
export type FailureContext = z.infer<typeof FailureContextSchema>;
export declare const FailureEvidenceSchema: z.ZodObject<{
    stackTrace: z.ZodOptional<z.ZodString>;
    logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metrics: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnion<[z.ZodString, z.ZodNumber, z.ZodBoolean]>>>;
    screenshots: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    networkLogs: z.ZodDefault<z.ZodArray<z.ZodObject<{
        url: z.ZodString;
        method: z.ZodString;
        status: z.ZodOptional<z.ZodNumber>;
        requestBody: z.ZodOptional<z.ZodString>;
        responseBody: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        status?: number;
        method?: string;
        url?: string;
        requestBody?: string;
        responseBody?: string;
    }, {
        status?: number;
        method?: string;
        url?: string;
        requestBody?: string;
        responseBody?: string;
    }>, "many">>;
    environmentInfo: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodString>>;
}, "strip", z.ZodTypeAny, {
    metrics?: Record<string, string | number | boolean>;
    logs?: string[];
    stackTrace?: string;
    screenshots?: string[];
    networkLogs?: {
        status?: number;
        method?: string;
        url?: string;
        requestBody?: string;
        responseBody?: string;
    }[];
    environmentInfo?: Record<string, string>;
}, {
    metrics?: Record<string, string | number | boolean>;
    logs?: string[];
    stackTrace?: string;
    screenshots?: string[];
    networkLogs?: {
        status?: number;
        method?: string;
        url?: string;
        requestBody?: string;
        responseBody?: string;
    }[];
    environmentInfo?: Record<string, string>;
}>;
export type FailureEvidence = z.infer<typeof FailureEvidenceSchema>;
export declare const RepairActionSchema: z.ZodObject<{
    type: z.ZodEnum<["code_change", "spec_update", "config_change", "dependency_update", "test_update", "documentation_update"]>;
    description: z.ZodString;
    targetFile: z.ZodOptional<z.ZodString>;
    proposedChange: z.ZodOptional<z.ZodString>;
    confidence: z.ZodNumber;
    reasoning: z.ZodOptional<z.ZodString>;
    prerequisites: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
    description?: string;
    confidence?: number;
    reasoning?: string;
    prerequisites?: string[];
    targetFile?: string;
    proposedChange?: string;
}, {
    type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
    description?: string;
    confidence?: number;
    reasoning?: string;
    prerequisites?: string[];
    targetFile?: string;
    proposedChange?: string;
}>;
export type RepairAction = z.infer<typeof RepairActionSchema>;
export declare const RootCauseSchema: z.ZodObject<{
    hypothesis: z.ZodString;
    evidence: z.ZodArray<z.ZodString, "many">;
    confidence: z.ZodNumber;
    relatedFailures: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    confidence?: number;
    evidence?: string[];
    hypothesis?: string;
    relatedFailures?: string[];
}, {
    confidence?: number;
    evidence?: string[];
    hypothesis?: string;
    relatedFailures?: string[];
}>;
export type RootCause = z.infer<typeof RootCauseSchema>;
export declare const FailureArtifactSchema: z.ZodObject<{
    id: z.ZodString;
    title: z.ZodString;
    description: z.ZodString;
    severity: z.ZodEnum<["critical", "major", "minor", "info"]>;
    category: z.ZodEnum<["specification_mismatch", "contract_violation", "type_error", "runtime_error", "performance_regression", "security_violation", "quality_gate_failure", "drift_detection", "test_failure"]>;
    location: z.ZodOptional<z.ZodObject<{
        file: z.ZodString;
        line: z.ZodOptional<z.ZodNumber>;
        column: z.ZodOptional<z.ZodNumber>;
        function: z.ZodOptional<z.ZodString>;
        module: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        function?: string;
        line?: number;
        file?: string;
        module?: string;
        column?: number;
    }, {
        function?: string;
        line?: number;
        file?: string;
        module?: string;
        column?: number;
    }>>;
    context: z.ZodObject<{
        environment: z.ZodDefault<z.ZodString>;
        phase: z.ZodOptional<z.ZodString>;
        component: z.ZodOptional<z.ZodString>;
        timestamp: z.ZodString;
        commitHash: z.ZodOptional<z.ZodString>;
        branch: z.ZodOptional<z.ZodString>;
        userId: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        environment?: string;
        timestamp?: string;
        component?: string;
        phase?: string;
        branch?: string;
        commitHash?: string;
        userId?: string;
    }, {
        environment?: string;
        timestamp?: string;
        component?: string;
        phase?: string;
        branch?: string;
        commitHash?: string;
        userId?: string;
    }>;
    evidence: z.ZodObject<{
        stackTrace: z.ZodOptional<z.ZodString>;
        logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        metrics: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnion<[z.ZodString, z.ZodNumber, z.ZodBoolean]>>>;
        screenshots: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        networkLogs: z.ZodDefault<z.ZodArray<z.ZodObject<{
            url: z.ZodString;
            method: z.ZodString;
            status: z.ZodOptional<z.ZodNumber>;
            requestBody: z.ZodOptional<z.ZodString>;
            responseBody: z.ZodOptional<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            status?: number;
            method?: string;
            url?: string;
            requestBody?: string;
            responseBody?: string;
        }, {
            status?: number;
            method?: string;
            url?: string;
            requestBody?: string;
            responseBody?: string;
        }>, "many">>;
        environmentInfo: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodString>>;
    }, "strip", z.ZodTypeAny, {
        metrics?: Record<string, string | number | boolean>;
        logs?: string[];
        stackTrace?: string;
        screenshots?: string[];
        networkLogs?: {
            status?: number;
            method?: string;
            url?: string;
            requestBody?: string;
            responseBody?: string;
        }[];
        environmentInfo?: Record<string, string>;
    }, {
        metrics?: Record<string, string | number | boolean>;
        logs?: string[];
        stackTrace?: string;
        screenshots?: string[];
        networkLogs?: {
            status?: number;
            method?: string;
            url?: string;
            requestBody?: string;
            responseBody?: string;
        }[];
        environmentInfo?: Record<string, string>;
    }>;
    rootCause: z.ZodOptional<z.ZodObject<{
        hypothesis: z.ZodString;
        evidence: z.ZodArray<z.ZodString, "many">;
        confidence: z.ZodNumber;
        relatedFailures: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        confidence?: number;
        evidence?: string[];
        hypothesis?: string;
        relatedFailures?: string[];
    }, {
        confidence?: number;
        evidence?: string[];
        hypothesis?: string;
        relatedFailures?: string[];
    }>>;
    suggestedActions: z.ZodDefault<z.ZodArray<z.ZodObject<{
        type: z.ZodEnum<["code_change", "spec_update", "config_change", "dependency_update", "test_update", "documentation_update"]>;
        description: z.ZodString;
        targetFile: z.ZodOptional<z.ZodString>;
        proposedChange: z.ZodOptional<z.ZodString>;
        confidence: z.ZodNumber;
        reasoning: z.ZodOptional<z.ZodString>;
        prerequisites: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
        description?: string;
        confidence?: number;
        reasoning?: string;
        prerequisites?: string[];
        targetFile?: string;
        proposedChange?: string;
    }, {
        type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
        description?: string;
        confidence?: number;
        reasoning?: string;
        prerequisites?: string[];
        targetFile?: string;
        proposedChange?: string;
    }>, "many">>;
    createdAt: z.ZodString;
    updatedAt: z.ZodString;
    resolvedAt: z.ZodOptional<z.ZodString>;
    tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    parentFailureId: z.ZodOptional<z.ZodString>;
    childFailureIds: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    status: z.ZodDefault<z.ZodEnum<["open", "analyzing", "fixing", "testing", "resolved", "ignored"]>>;
    assignee: z.ZodOptional<z.ZodString>;
    schemaVersion: z.ZodDefault<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    status?: "testing" | "open" | "resolved" | "analyzing" | "fixing" | "ignored";
    id?: string;
    createdAt?: string;
    location?: {
        function?: string;
        line?: number;
        file?: string;
        module?: string;
        column?: number;
    };
    severity?: "critical" | "major" | "minor" | "info";
    description?: string;
    category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection";
    context?: {
        environment?: string;
        timestamp?: string;
        component?: string;
        phase?: string;
        branch?: string;
        commitHash?: string;
        userId?: string;
    };
    title?: string;
    suggestedActions?: {
        type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
        description?: string;
        confidence?: number;
        reasoning?: string;
        prerequisites?: string[];
        targetFile?: string;
        proposedChange?: string;
    }[];
    evidence?: {
        metrics?: Record<string, string | number | boolean>;
        logs?: string[];
        stackTrace?: string;
        screenshots?: string[];
        networkLogs?: {
            status?: number;
            method?: string;
            url?: string;
            requestBody?: string;
            responseBody?: string;
        }[];
        environmentInfo?: Record<string, string>;
    };
    rootCause?: {
        confidence?: number;
        evidence?: string[];
        hypothesis?: string;
        relatedFailures?: string[];
    };
    updatedAt?: string;
    tags?: string[];
    resolvedAt?: string;
    parentFailureId?: string;
    childFailureIds?: string[];
    assignee?: string;
    schemaVersion?: string;
}, {
    status?: "testing" | "open" | "resolved" | "analyzing" | "fixing" | "ignored";
    id?: string;
    createdAt?: string;
    location?: {
        function?: string;
        line?: number;
        file?: string;
        module?: string;
        column?: number;
    };
    severity?: "critical" | "major" | "minor" | "info";
    description?: string;
    category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection";
    context?: {
        environment?: string;
        timestamp?: string;
        component?: string;
        phase?: string;
        branch?: string;
        commitHash?: string;
        userId?: string;
    };
    title?: string;
    suggestedActions?: {
        type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
        description?: string;
        confidence?: number;
        reasoning?: string;
        prerequisites?: string[];
        targetFile?: string;
        proposedChange?: string;
    }[];
    evidence?: {
        metrics?: Record<string, string | number | boolean>;
        logs?: string[];
        stackTrace?: string;
        screenshots?: string[];
        networkLogs?: {
            status?: number;
            method?: string;
            url?: string;
            requestBody?: string;
            responseBody?: string;
        }[];
        environmentInfo?: Record<string, string>;
    };
    rootCause?: {
        confidence?: number;
        evidence?: string[];
        hypothesis?: string;
        relatedFailures?: string[];
    };
    updatedAt?: string;
    tags?: string[];
    resolvedAt?: string;
    parentFailureId?: string;
    childFailureIds?: string[];
    assignee?: string;
    schemaVersion?: string;
}>;
export type FailureArtifact = z.infer<typeof FailureArtifactSchema>;
export declare const FailureArtifactCollectionSchema: z.ZodObject<{
    failures: z.ZodArray<z.ZodObject<{
        id: z.ZodString;
        title: z.ZodString;
        description: z.ZodString;
        severity: z.ZodEnum<["critical", "major", "minor", "info"]>;
        category: z.ZodEnum<["specification_mismatch", "contract_violation", "type_error", "runtime_error", "performance_regression", "security_violation", "quality_gate_failure", "drift_detection", "test_failure"]>;
        location: z.ZodOptional<z.ZodObject<{
            file: z.ZodString;
            line: z.ZodOptional<z.ZodNumber>;
            column: z.ZodOptional<z.ZodNumber>;
            function: z.ZodOptional<z.ZodString>;
            module: z.ZodOptional<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            function?: string;
            line?: number;
            file?: string;
            module?: string;
            column?: number;
        }, {
            function?: string;
            line?: number;
            file?: string;
            module?: string;
            column?: number;
        }>>;
        context: z.ZodObject<{
            environment: z.ZodDefault<z.ZodString>;
            phase: z.ZodOptional<z.ZodString>;
            component: z.ZodOptional<z.ZodString>;
            timestamp: z.ZodString;
            commitHash: z.ZodOptional<z.ZodString>;
            branch: z.ZodOptional<z.ZodString>;
            userId: z.ZodOptional<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            environment?: string;
            timestamp?: string;
            component?: string;
            phase?: string;
            branch?: string;
            commitHash?: string;
            userId?: string;
        }, {
            environment?: string;
            timestamp?: string;
            component?: string;
            phase?: string;
            branch?: string;
            commitHash?: string;
            userId?: string;
        }>;
        evidence: z.ZodObject<{
            stackTrace: z.ZodOptional<z.ZodString>;
            logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
            metrics: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodUnion<[z.ZodString, z.ZodNumber, z.ZodBoolean]>>>;
            screenshots: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
            networkLogs: z.ZodDefault<z.ZodArray<z.ZodObject<{
                url: z.ZodString;
                method: z.ZodString;
                status: z.ZodOptional<z.ZodNumber>;
                requestBody: z.ZodOptional<z.ZodString>;
                responseBody: z.ZodOptional<z.ZodString>;
            }, "strip", z.ZodTypeAny, {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }, {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }>, "many">>;
            environmentInfo: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodString>>;
        }, "strip", z.ZodTypeAny, {
            metrics?: Record<string, string | number | boolean>;
            logs?: string[];
            stackTrace?: string;
            screenshots?: string[];
            networkLogs?: {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }[];
            environmentInfo?: Record<string, string>;
        }, {
            metrics?: Record<string, string | number | boolean>;
            logs?: string[];
            stackTrace?: string;
            screenshots?: string[];
            networkLogs?: {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }[];
            environmentInfo?: Record<string, string>;
        }>;
        rootCause: z.ZodOptional<z.ZodObject<{
            hypothesis: z.ZodString;
            evidence: z.ZodArray<z.ZodString, "many">;
            confidence: z.ZodNumber;
            relatedFailures: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        }, "strip", z.ZodTypeAny, {
            confidence?: number;
            evidence?: string[];
            hypothesis?: string;
            relatedFailures?: string[];
        }, {
            confidence?: number;
            evidence?: string[];
            hypothesis?: string;
            relatedFailures?: string[];
        }>>;
        suggestedActions: z.ZodDefault<z.ZodArray<z.ZodObject<{
            type: z.ZodEnum<["code_change", "spec_update", "config_change", "dependency_update", "test_update", "documentation_update"]>;
            description: z.ZodString;
            targetFile: z.ZodOptional<z.ZodString>;
            proposedChange: z.ZodOptional<z.ZodString>;
            confidence: z.ZodNumber;
            reasoning: z.ZodOptional<z.ZodString>;
            prerequisites: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        }, "strip", z.ZodTypeAny, {
            type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
            description?: string;
            confidence?: number;
            reasoning?: string;
            prerequisites?: string[];
            targetFile?: string;
            proposedChange?: string;
        }, {
            type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
            description?: string;
            confidence?: number;
            reasoning?: string;
            prerequisites?: string[];
            targetFile?: string;
            proposedChange?: string;
        }>, "many">>;
        createdAt: z.ZodString;
        updatedAt: z.ZodString;
        resolvedAt: z.ZodOptional<z.ZodString>;
        tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        parentFailureId: z.ZodOptional<z.ZodString>;
        childFailureIds: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        status: z.ZodDefault<z.ZodEnum<["open", "analyzing", "fixing", "testing", "resolved", "ignored"]>>;
        assignee: z.ZodOptional<z.ZodString>;
        schemaVersion: z.ZodDefault<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        status?: "testing" | "open" | "resolved" | "analyzing" | "fixing" | "ignored";
        id?: string;
        createdAt?: string;
        location?: {
            function?: string;
            line?: number;
            file?: string;
            module?: string;
            column?: number;
        };
        severity?: "critical" | "major" | "minor" | "info";
        description?: string;
        category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection";
        context?: {
            environment?: string;
            timestamp?: string;
            component?: string;
            phase?: string;
            branch?: string;
            commitHash?: string;
            userId?: string;
        };
        title?: string;
        suggestedActions?: {
            type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
            description?: string;
            confidence?: number;
            reasoning?: string;
            prerequisites?: string[];
            targetFile?: string;
            proposedChange?: string;
        }[];
        evidence?: {
            metrics?: Record<string, string | number | boolean>;
            logs?: string[];
            stackTrace?: string;
            screenshots?: string[];
            networkLogs?: {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }[];
            environmentInfo?: Record<string, string>;
        };
        rootCause?: {
            confidence?: number;
            evidence?: string[];
            hypothesis?: string;
            relatedFailures?: string[];
        };
        updatedAt?: string;
        tags?: string[];
        resolvedAt?: string;
        parentFailureId?: string;
        childFailureIds?: string[];
        assignee?: string;
        schemaVersion?: string;
    }, {
        status?: "testing" | "open" | "resolved" | "analyzing" | "fixing" | "ignored";
        id?: string;
        createdAt?: string;
        location?: {
            function?: string;
            line?: number;
            file?: string;
            module?: string;
            column?: number;
        };
        severity?: "critical" | "major" | "minor" | "info";
        description?: string;
        category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection";
        context?: {
            environment?: string;
            timestamp?: string;
            component?: string;
            phase?: string;
            branch?: string;
            commitHash?: string;
            userId?: string;
        };
        title?: string;
        suggestedActions?: {
            type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
            description?: string;
            confidence?: number;
            reasoning?: string;
            prerequisites?: string[];
            targetFile?: string;
            proposedChange?: string;
        }[];
        evidence?: {
            metrics?: Record<string, string | number | boolean>;
            logs?: string[];
            stackTrace?: string;
            screenshots?: string[];
            networkLogs?: {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }[];
            environmentInfo?: Record<string, string>;
        };
        rootCause?: {
            confidence?: number;
            evidence?: string[];
            hypothesis?: string;
            relatedFailures?: string[];
        };
        updatedAt?: string;
        tags?: string[];
        resolvedAt?: string;
        parentFailureId?: string;
        childFailureIds?: string[];
        assignee?: string;
        schemaVersion?: string;
    }>, "many">;
    metadata: z.ZodObject<{
        generatedAt: z.ZodString;
        totalCount: z.ZodNumber;
        severityCounts: z.ZodOptional<z.ZodRecord<z.ZodEnum<["critical", "major", "minor", "info"]>, z.ZodNumber>>;
        categoryCounts: z.ZodOptional<z.ZodRecord<z.ZodEnum<["specification_mismatch", "contract_violation", "type_error", "runtime_error", "performance_regression", "security_violation", "quality_gate_failure", "drift_detection", "test_failure"]>, z.ZodNumber>>;
        environment: z.ZodString;
        source: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        environment?: string;
        source?: string;
        generatedAt?: string;
        totalCount?: number;
        severityCounts?: Partial<Record<"critical" | "major" | "minor" | "info", number>>;
        categoryCounts?: Partial<Record<"contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection", number>>;
    }, {
        environment?: string;
        source?: string;
        generatedAt?: string;
        totalCount?: number;
        severityCounts?: Partial<Record<"critical" | "major" | "minor" | "info", number>>;
        categoryCounts?: Partial<Record<"contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection", number>>;
    }>;
    schemaVersion: z.ZodDefault<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    failures?: {
        status?: "testing" | "open" | "resolved" | "analyzing" | "fixing" | "ignored";
        id?: string;
        createdAt?: string;
        location?: {
            function?: string;
            line?: number;
            file?: string;
            module?: string;
            column?: number;
        };
        severity?: "critical" | "major" | "minor" | "info";
        description?: string;
        category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection";
        context?: {
            environment?: string;
            timestamp?: string;
            component?: string;
            phase?: string;
            branch?: string;
            commitHash?: string;
            userId?: string;
        };
        title?: string;
        suggestedActions?: {
            type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
            description?: string;
            confidence?: number;
            reasoning?: string;
            prerequisites?: string[];
            targetFile?: string;
            proposedChange?: string;
        }[];
        evidence?: {
            metrics?: Record<string, string | number | boolean>;
            logs?: string[];
            stackTrace?: string;
            screenshots?: string[];
            networkLogs?: {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }[];
            environmentInfo?: Record<string, string>;
        };
        rootCause?: {
            confidence?: number;
            evidence?: string[];
            hypothesis?: string;
            relatedFailures?: string[];
        };
        updatedAt?: string;
        tags?: string[];
        resolvedAt?: string;
        parentFailureId?: string;
        childFailureIds?: string[];
        assignee?: string;
        schemaVersion?: string;
    }[];
    metadata?: {
        environment?: string;
        source?: string;
        generatedAt?: string;
        totalCount?: number;
        severityCounts?: Partial<Record<"critical" | "major" | "minor" | "info", number>>;
        categoryCounts?: Partial<Record<"contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection", number>>;
    };
    schemaVersion?: string;
}, {
    failures?: {
        status?: "testing" | "open" | "resolved" | "analyzing" | "fixing" | "ignored";
        id?: string;
        createdAt?: string;
        location?: {
            function?: string;
            line?: number;
            file?: string;
            module?: string;
            column?: number;
        };
        severity?: "critical" | "major" | "minor" | "info";
        description?: string;
        category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection";
        context?: {
            environment?: string;
            timestamp?: string;
            component?: string;
            phase?: string;
            branch?: string;
            commitHash?: string;
            userId?: string;
        };
        title?: string;
        suggestedActions?: {
            type?: "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "spec_update";
            description?: string;
            confidence?: number;
            reasoning?: string;
            prerequisites?: string[];
            targetFile?: string;
            proposedChange?: string;
        }[];
        evidence?: {
            metrics?: Record<string, string | number | boolean>;
            logs?: string[];
            stackTrace?: string;
            screenshots?: string[];
            networkLogs?: {
                status?: number;
                method?: string;
                url?: string;
                requestBody?: string;
                responseBody?: string;
            }[];
            environmentInfo?: Record<string, string>;
        };
        rootCause?: {
            confidence?: number;
            evidence?: string[];
            hypothesis?: string;
            relatedFailures?: string[];
        };
        updatedAt?: string;
        tags?: string[];
        resolvedAt?: string;
        parentFailureId?: string;
        childFailureIds?: string[];
        assignee?: string;
        schemaVersion?: string;
    }[];
    metadata?: {
        environment?: string;
        source?: string;
        generatedAt?: string;
        totalCount?: number;
        severityCounts?: Partial<Record<"critical" | "major" | "minor" | "info", number>>;
        categoryCounts?: Partial<Record<"contract_violation" | "test_failure" | "type_error" | "runtime_error" | "security_violation" | "specification_mismatch" | "performance_regression" | "quality_gate_failure" | "drift_detection", number>>;
    };
    schemaVersion?: string;
}>;
export type FailureArtifactCollection = z.infer<typeof FailureArtifactCollectionSchema>;
export declare class FailureArtifactFactory {
    static create(base: Partial<FailureArtifact>): FailureArtifact;
    static fromError(error: Error, context?: Partial<FailureContext>): FailureArtifact;
    static fromTestFailure(testName: string, error: string, location?: FailureLocation): FailureArtifact;
    static fromContractViolation(contractName: string, expected: any, actual: any, location?: FailureLocation): FailureArtifact;
}
export declare function validateFailureArtifact(data: unknown): FailureArtifact;
export declare function validateFailureArtifactCollection(data: unknown): FailureArtifactCollection;
export declare function isFailureArtifact(data: unknown): data is FailureArtifact;
