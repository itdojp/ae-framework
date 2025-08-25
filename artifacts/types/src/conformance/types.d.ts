/**
 * Runtime Conformance Verification Types
 * Phase 2.2: Types and schemas for runtime behavior monitoring and verification
 */
import { z } from 'zod';
export declare const ConformanceRuleCategorySchema: z.ZodEnum<["data_validation", "api_contract", "business_logic", "security_policy", "performance_constraint", "resource_usage", "state_invariant", "behavioral_constraint", "integration_requirement", "compliance_rule"]>;
export type ConformanceRuleCategory = z.infer<typeof ConformanceRuleCategorySchema>;
export declare const ViolationSeveritySchema: z.ZodEnum<["critical", "major", "minor", "info", "warning"]>;
export type ViolationSeverity = z.infer<typeof ViolationSeveritySchema>;
export declare const VerificationStatusSchema: z.ZodEnum<["pass", "fail", "skip", "error", "timeout"]>;
export type VerificationStatus = z.infer<typeof VerificationStatusSchema>;
export declare const RuntimeContextSchema: z.ZodObject<{
    timestamp: z.ZodString;
    executionId: z.ZodString;
    functionName: z.ZodOptional<z.ZodString>;
    modulePath: z.ZodOptional<z.ZodString>;
    requestId: z.ZodOptional<z.ZodString>;
    userId: z.ZodOptional<z.ZodString>;
    sessionId: z.ZodOptional<z.ZodString>;
    environment: z.ZodDefault<z.ZodString>;
    version: z.ZodOptional<z.ZodString>;
    buildId: z.ZodOptional<z.ZodString>;
    traceId: z.ZodOptional<z.ZodString>;
    spanId: z.ZodOptional<z.ZodString>;
    metadata: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
}, "strip", z.ZodTypeAny, {
    version?: string;
    environment?: string;
    timestamp?: string;
    metadata?: Record<string, any>;
    functionName?: string;
    userId?: string;
    executionId?: string;
    modulePath?: string;
    requestId?: string;
    sessionId?: string;
    buildId?: string;
    traceId?: string;
    spanId?: string;
}, {
    version?: string;
    environment?: string;
    timestamp?: string;
    metadata?: Record<string, any>;
    functionName?: string;
    userId?: string;
    executionId?: string;
    modulePath?: string;
    requestId?: string;
    sessionId?: string;
    buildId?: string;
    traceId?: string;
    spanId?: string;
}>;
export type RuntimeContext = z.infer<typeof RuntimeContextSchema>;
export declare const ConformanceRuleSchema: z.ZodObject<{
    id: z.ZodString;
    name: z.ZodString;
    description: z.ZodString;
    category: z.ZodEnum<["data_validation", "api_contract", "business_logic", "security_policy", "performance_constraint", "resource_usage", "state_invariant", "behavioral_constraint", "integration_requirement", "compliance_rule"]>;
    severity: z.ZodEnum<["critical", "major", "minor", "info", "warning"]>;
    enabled: z.ZodDefault<z.ZodBoolean>;
    condition: z.ZodObject<{
        expression: z.ZodString;
        variables: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        constraints: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
    }, "strip", z.ZodTypeAny, {
        constraints?: Record<string, any>;
        expression?: string;
        variables?: string[];
    }, {
        constraints?: Record<string, any>;
        expression?: string;
        variables?: string[];
    }>;
    actions: z.ZodDefault<z.ZodArray<z.ZodEnum<["log_violation", "throw_error", "return_default", "circuit_break", "alert", "metric_increment", "trace_event"]>, "many">>;
    metadata: z.ZodObject<{
        createdAt: z.ZodString;
        updatedAt: z.ZodString;
        version: z.ZodDefault<z.ZodString>;
        tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        owner: z.ZodOptional<z.ZodString>;
        documentation: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        createdAt?: string;
        version?: string;
        documentation?: string;
        updatedAt?: string;
        tags?: string[];
        owner?: string;
    }, {
        createdAt?: string;
        version?: string;
        documentation?: string;
        updatedAt?: string;
        tags?: string[];
        owner?: string;
    }>;
}, "strip", z.ZodTypeAny, {
    enabled?: boolean;
    name?: string;
    id?: string;
    severity?: "critical" | "major" | "minor" | "warning" | "info";
    description?: string;
    condition?: {
        constraints?: Record<string, any>;
        expression?: string;
        variables?: string[];
    };
    category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
    metadata?: {
        createdAt?: string;
        version?: string;
        documentation?: string;
        updatedAt?: string;
        tags?: string[];
        owner?: string;
    };
    actions?: ("log_violation" | "throw_error" | "return_default" | "circuit_break" | "alert" | "metric_increment" | "trace_event")[];
}, {
    enabled?: boolean;
    name?: string;
    id?: string;
    severity?: "critical" | "major" | "minor" | "warning" | "info";
    description?: string;
    condition?: {
        constraints?: Record<string, any>;
        expression?: string;
        variables?: string[];
    };
    category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
    metadata?: {
        createdAt?: string;
        version?: string;
        documentation?: string;
        updatedAt?: string;
        tags?: string[];
        owner?: string;
    };
    actions?: ("log_violation" | "throw_error" | "return_default" | "circuit_break" | "alert" | "metric_increment" | "trace_event")[];
}>;
export type ConformanceRule = z.infer<typeof ConformanceRuleSchema>;
export declare const ViolationDetailsSchema: z.ZodObject<{
    ruleId: z.ZodString;
    ruleName: z.ZodString;
    category: z.ZodEnum<["data_validation", "api_contract", "business_logic", "security_policy", "performance_constraint", "resource_usage", "state_invariant", "behavioral_constraint", "integration_requirement", "compliance_rule"]>;
    severity: z.ZodEnum<["critical", "major", "minor", "info", "warning"]>;
    message: z.ZodString;
    actualValue: z.ZodOptional<z.ZodAny>;
    expectedValue: z.ZodOptional<z.ZodAny>;
    context: z.ZodObject<{
        timestamp: z.ZodString;
        executionId: z.ZodString;
        functionName: z.ZodOptional<z.ZodString>;
        modulePath: z.ZodOptional<z.ZodString>;
        requestId: z.ZodOptional<z.ZodString>;
        userId: z.ZodOptional<z.ZodString>;
        sessionId: z.ZodOptional<z.ZodString>;
        environment: z.ZodDefault<z.ZodString>;
        version: z.ZodOptional<z.ZodString>;
        buildId: z.ZodOptional<z.ZodString>;
        traceId: z.ZodOptional<z.ZodString>;
        spanId: z.ZodOptional<z.ZodString>;
        metadata: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
    }, "strip", z.ZodTypeAny, {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    }, {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    }>;
    stackTrace: z.ZodOptional<z.ZodString>;
    evidence: z.ZodDefault<z.ZodObject<{
        inputData: z.ZodOptional<z.ZodAny>;
        outputData: z.ZodOptional<z.ZodAny>;
        stateSnapshot: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
        metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
        logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        traces: z.ZodDefault<z.ZodArray<z.ZodAny, "many">>;
    }, "strip", z.ZodTypeAny, {
        metrics?: Record<string, number>;
        logs?: string[];
        inputData?: any;
        outputData?: any;
        stateSnapshot?: Record<string, any>;
        traces?: any[];
    }, {
        metrics?: Record<string, number>;
        logs?: string[];
        inputData?: any;
        outputData?: any;
        stateSnapshot?: Record<string, any>;
        traces?: any[];
    }>>;
    remediation: z.ZodOptional<z.ZodObject<{
        suggested: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        automatic: z.ZodDefault<z.ZodBoolean>;
        priority: z.ZodDefault<z.ZodEnum<["low", "medium", "high", "critical"]>>;
    }, "strip", z.ZodTypeAny, {
        priority?: "critical" | "low" | "medium" | "high";
        suggested?: string[];
        automatic?: boolean;
    }, {
        priority?: "critical" | "low" | "medium" | "high";
        suggested?: string[];
        automatic?: boolean;
    }>>;
}, "strip", z.ZodTypeAny, {
    message?: string;
    severity?: "critical" | "major" | "minor" | "warning" | "info";
    category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
    context?: {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    };
    stackTrace?: string;
    evidence?: {
        metrics?: Record<string, number>;
        logs?: string[];
        inputData?: any;
        outputData?: any;
        stateSnapshot?: Record<string, any>;
        traces?: any[];
    };
    ruleId?: string;
    ruleName?: string;
    actualValue?: any;
    expectedValue?: any;
    remediation?: {
        priority?: "critical" | "low" | "medium" | "high";
        suggested?: string[];
        automatic?: boolean;
    };
}, {
    message?: string;
    severity?: "critical" | "major" | "minor" | "warning" | "info";
    category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
    context?: {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    };
    stackTrace?: string;
    evidence?: {
        metrics?: Record<string, number>;
        logs?: string[];
        inputData?: any;
        outputData?: any;
        stateSnapshot?: Record<string, any>;
        traces?: any[];
    };
    ruleId?: string;
    ruleName?: string;
    actualValue?: any;
    expectedValue?: any;
    remediation?: {
        priority?: "critical" | "low" | "medium" | "high";
        suggested?: string[];
        automatic?: boolean;
    };
}>;
export type ViolationDetails = z.infer<typeof ViolationDetailsSchema>;
export declare const VerificationResultSchema: z.ZodObject<{
    id: z.ZodString;
    ruleId: z.ZodString;
    status: z.ZodEnum<["pass", "fail", "skip", "error", "timeout"]>;
    timestamp: z.ZodString;
    duration: z.ZodNumber;
    context: z.ZodObject<{
        timestamp: z.ZodString;
        executionId: z.ZodString;
        functionName: z.ZodOptional<z.ZodString>;
        modulePath: z.ZodOptional<z.ZodString>;
        requestId: z.ZodOptional<z.ZodString>;
        userId: z.ZodOptional<z.ZodString>;
        sessionId: z.ZodOptional<z.ZodString>;
        environment: z.ZodDefault<z.ZodString>;
        version: z.ZodOptional<z.ZodString>;
        buildId: z.ZodOptional<z.ZodString>;
        traceId: z.ZodOptional<z.ZodString>;
        spanId: z.ZodOptional<z.ZodString>;
        metadata: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
    }, "strip", z.ZodTypeAny, {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    }, {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    }>;
    violation: z.ZodOptional<z.ZodObject<{
        ruleId: z.ZodString;
        ruleName: z.ZodString;
        category: z.ZodEnum<["data_validation", "api_contract", "business_logic", "security_policy", "performance_constraint", "resource_usage", "state_invariant", "behavioral_constraint", "integration_requirement", "compliance_rule"]>;
        severity: z.ZodEnum<["critical", "major", "minor", "info", "warning"]>;
        message: z.ZodString;
        actualValue: z.ZodOptional<z.ZodAny>;
        expectedValue: z.ZodOptional<z.ZodAny>;
        context: z.ZodObject<{
            timestamp: z.ZodString;
            executionId: z.ZodString;
            functionName: z.ZodOptional<z.ZodString>;
            modulePath: z.ZodOptional<z.ZodString>;
            requestId: z.ZodOptional<z.ZodString>;
            userId: z.ZodOptional<z.ZodString>;
            sessionId: z.ZodOptional<z.ZodString>;
            environment: z.ZodDefault<z.ZodString>;
            version: z.ZodOptional<z.ZodString>;
            buildId: z.ZodOptional<z.ZodString>;
            traceId: z.ZodOptional<z.ZodString>;
            spanId: z.ZodOptional<z.ZodString>;
            metadata: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
        }, "strip", z.ZodTypeAny, {
            version?: string;
            environment?: string;
            timestamp?: string;
            metadata?: Record<string, any>;
            functionName?: string;
            userId?: string;
            executionId?: string;
            modulePath?: string;
            requestId?: string;
            sessionId?: string;
            buildId?: string;
            traceId?: string;
            spanId?: string;
        }, {
            version?: string;
            environment?: string;
            timestamp?: string;
            metadata?: Record<string, any>;
            functionName?: string;
            userId?: string;
            executionId?: string;
            modulePath?: string;
            requestId?: string;
            sessionId?: string;
            buildId?: string;
            traceId?: string;
            spanId?: string;
        }>;
        stackTrace: z.ZodOptional<z.ZodString>;
        evidence: z.ZodDefault<z.ZodObject<{
            inputData: z.ZodOptional<z.ZodAny>;
            outputData: z.ZodOptional<z.ZodAny>;
            stateSnapshot: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
            metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
            logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
            traces: z.ZodDefault<z.ZodArray<z.ZodAny, "many">>;
        }, "strip", z.ZodTypeAny, {
            metrics?: Record<string, number>;
            logs?: string[];
            inputData?: any;
            outputData?: any;
            stateSnapshot?: Record<string, any>;
            traces?: any[];
        }, {
            metrics?: Record<string, number>;
            logs?: string[];
            inputData?: any;
            outputData?: any;
            stateSnapshot?: Record<string, any>;
            traces?: any[];
        }>>;
        remediation: z.ZodOptional<z.ZodObject<{
            suggested: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
            automatic: z.ZodDefault<z.ZodBoolean>;
            priority: z.ZodDefault<z.ZodEnum<["low", "medium", "high", "critical"]>>;
        }, "strip", z.ZodTypeAny, {
            priority?: "critical" | "low" | "medium" | "high";
            suggested?: string[];
            automatic?: boolean;
        }, {
            priority?: "critical" | "low" | "medium" | "high";
            suggested?: string[];
            automatic?: boolean;
        }>>;
    }, "strip", z.ZodTypeAny, {
        message?: string;
        severity?: "critical" | "major" | "minor" | "warning" | "info";
        category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
        context?: {
            version?: string;
            environment?: string;
            timestamp?: string;
            metadata?: Record<string, any>;
            functionName?: string;
            userId?: string;
            executionId?: string;
            modulePath?: string;
            requestId?: string;
            sessionId?: string;
            buildId?: string;
            traceId?: string;
            spanId?: string;
        };
        stackTrace?: string;
        evidence?: {
            metrics?: Record<string, number>;
            logs?: string[];
            inputData?: any;
            outputData?: any;
            stateSnapshot?: Record<string, any>;
            traces?: any[];
        };
        ruleId?: string;
        ruleName?: string;
        actualValue?: any;
        expectedValue?: any;
        remediation?: {
            priority?: "critical" | "low" | "medium" | "high";
            suggested?: string[];
            automatic?: boolean;
        };
    }, {
        message?: string;
        severity?: "critical" | "major" | "minor" | "warning" | "info";
        category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
        context?: {
            version?: string;
            environment?: string;
            timestamp?: string;
            metadata?: Record<string, any>;
            functionName?: string;
            userId?: string;
            executionId?: string;
            modulePath?: string;
            requestId?: string;
            sessionId?: string;
            buildId?: string;
            traceId?: string;
            spanId?: string;
        };
        stackTrace?: string;
        evidence?: {
            metrics?: Record<string, number>;
            logs?: string[];
            inputData?: any;
            outputData?: any;
            stateSnapshot?: Record<string, any>;
            traces?: any[];
        };
        ruleId?: string;
        ruleName?: string;
        actualValue?: any;
        expectedValue?: any;
        remediation?: {
            priority?: "critical" | "low" | "medium" | "high";
            suggested?: string[];
            automatic?: boolean;
        };
    }>>;
    metrics: z.ZodDefault<z.ZodObject<{
        executionTime: z.ZodNumber;
        memoryUsage: z.ZodOptional<z.ZodNumber>;
        cpuUsage: z.ZodOptional<z.ZodNumber>;
        networkCalls: z.ZodDefault<z.ZodNumber>;
        dbQueries: z.ZodDefault<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        executionTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        dbQueries?: number;
    }, {
        executionTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        dbQueries?: number;
    }>>;
    metadata: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
}, "strip", z.ZodTypeAny, {
    status?: "error" | "timeout" | "pass" | "fail" | "skip";
    id?: string;
    timestamp?: string;
    metrics?: {
        executionTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        dbQueries?: number;
    };
    duration?: number;
    violation?: {
        message?: string;
        severity?: "critical" | "major" | "minor" | "warning" | "info";
        category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
        context?: {
            version?: string;
            environment?: string;
            timestamp?: string;
            metadata?: Record<string, any>;
            functionName?: string;
            userId?: string;
            executionId?: string;
            modulePath?: string;
            requestId?: string;
            sessionId?: string;
            buildId?: string;
            traceId?: string;
            spanId?: string;
        };
        stackTrace?: string;
        evidence?: {
            metrics?: Record<string, number>;
            logs?: string[];
            inputData?: any;
            outputData?: any;
            stateSnapshot?: Record<string, any>;
            traces?: any[];
        };
        ruleId?: string;
        ruleName?: string;
        actualValue?: any;
        expectedValue?: any;
        remediation?: {
            priority?: "critical" | "low" | "medium" | "high";
            suggested?: string[];
            automatic?: boolean;
        };
    };
    metadata?: Record<string, any>;
    context?: {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    };
    ruleId?: string;
}, {
    status?: "error" | "timeout" | "pass" | "fail" | "skip";
    id?: string;
    timestamp?: string;
    metrics?: {
        executionTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        dbQueries?: number;
    };
    duration?: number;
    violation?: {
        message?: string;
        severity?: "critical" | "major" | "minor" | "warning" | "info";
        category?: "data_validation" | "api_contract" | "business_logic" | "security_policy" | "performance_constraint" | "resource_usage" | "state_invariant" | "behavioral_constraint" | "integration_requirement" | "compliance_rule";
        context?: {
            version?: string;
            environment?: string;
            timestamp?: string;
            metadata?: Record<string, any>;
            functionName?: string;
            userId?: string;
            executionId?: string;
            modulePath?: string;
            requestId?: string;
            sessionId?: string;
            buildId?: string;
            traceId?: string;
            spanId?: string;
        };
        stackTrace?: string;
        evidence?: {
            metrics?: Record<string, number>;
            logs?: string[];
            inputData?: any;
            outputData?: any;
            stateSnapshot?: Record<string, any>;
            traces?: any[];
        };
        ruleId?: string;
        ruleName?: string;
        actualValue?: any;
        expectedValue?: any;
        remediation?: {
            priority?: "critical" | "low" | "medium" | "high";
            suggested?: string[];
            automatic?: boolean;
        };
    };
    metadata?: Record<string, any>;
    context?: {
        version?: string;
        environment?: string;
        timestamp?: string;
        metadata?: Record<string, any>;
        functionName?: string;
        userId?: string;
        executionId?: string;
        modulePath?: string;
        requestId?: string;
        sessionId?: string;
        buildId?: string;
        traceId?: string;
        spanId?: string;
    };
    ruleId?: string;
}>;
export type VerificationResult = z.infer<typeof VerificationResultSchema>;
export declare const ConformanceConfigSchema: z.ZodObject<{
    enabled: z.ZodDefault<z.ZodBoolean>;
    mode: z.ZodDefault<z.ZodEnum<["strict", "permissive", "monitor_only"]>>;
    rules: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    sampling: z.ZodDefault<z.ZodObject<{
        enabled: z.ZodDefault<z.ZodBoolean>;
        rate: z.ZodDefault<z.ZodNumber>;
        strategy: z.ZodDefault<z.ZodEnum<["random", "systematic", "adaptive"]>>;
    }, "strip", z.ZodTypeAny, {
        enabled?: boolean;
        strategy?: "random" | "systematic" | "adaptive";
        rate?: number;
    }, {
        enabled?: boolean;
        strategy?: "random" | "systematic" | "adaptive";
        rate?: number;
    }>>;
    performance: z.ZodDefault<z.ZodObject<{
        timeoutMs: z.ZodDefault<z.ZodNumber>;
        maxConcurrentChecks: z.ZodDefault<z.ZodNumber>;
        cacheResults: z.ZodDefault<z.ZodBoolean>;
        cacheTtlMs: z.ZodDefault<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        timeoutMs?: number;
        maxConcurrentChecks?: number;
        cacheResults?: boolean;
        cacheTtlMs?: number;
    }, {
        timeoutMs?: number;
        maxConcurrentChecks?: number;
        cacheResults?: boolean;
        cacheTtlMs?: number;
    }>>;
    reporting: z.ZodDefault<z.ZodObject<{
        destinations: z.ZodDefault<z.ZodArray<z.ZodEnum<["console", "file", "metrics", "database", "webhook"]>, "many">>;
        batchSize: z.ZodDefault<z.ZodNumber>;
        flushIntervalMs: z.ZodDefault<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        destinations?: ("metrics" | "database" | "webhook" | "file" | "console")[];
        batchSize?: number;
        flushIntervalMs?: number;
    }, {
        destinations?: ("metrics" | "database" | "webhook" | "file" | "console")[];
        batchSize?: number;
        flushIntervalMs?: number;
    }>>;
    alerting: z.ZodDefault<z.ZodObject<{
        enabled: z.ZodDefault<z.ZodBoolean>;
        thresholds: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
        channels: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        enabled?: boolean;
        channels?: string[];
        thresholds?: Record<string, number>;
    }, {
        enabled?: boolean;
        channels?: string[];
        thresholds?: Record<string, number>;
    }>>;
}, "strip", z.ZodTypeAny, {
    enabled?: boolean;
    performance?: {
        timeoutMs?: number;
        maxConcurrentChecks?: number;
        cacheResults?: boolean;
        cacheTtlMs?: number;
    };
    reporting?: {
        destinations?: ("metrics" | "database" | "webhook" | "file" | "console")[];
        batchSize?: number;
        flushIntervalMs?: number;
    };
    mode?: "strict" | "permissive" | "monitor_only";
    rules?: string[];
    sampling?: {
        enabled?: boolean;
        strategy?: "random" | "systematic" | "adaptive";
        rate?: number;
    };
    alerting?: {
        enabled?: boolean;
        channels?: string[];
        thresholds?: Record<string, number>;
    };
}, {
    enabled?: boolean;
    performance?: {
        timeoutMs?: number;
        maxConcurrentChecks?: number;
        cacheResults?: boolean;
        cacheTtlMs?: number;
    };
    reporting?: {
        destinations?: ("metrics" | "database" | "webhook" | "file" | "console")[];
        batchSize?: number;
        flushIntervalMs?: number;
    };
    mode?: "strict" | "permissive" | "monitor_only";
    rules?: string[];
    sampling?: {
        enabled?: boolean;
        strategy?: "random" | "systematic" | "adaptive";
        rate?: number;
    };
    alerting?: {
        enabled?: boolean;
        channels?: string[];
        thresholds?: Record<string, number>;
    };
}>;
export type ConformanceConfig = z.infer<typeof ConformanceConfigSchema>;
export interface ConformanceMonitor {
    readonly id: string;
    readonly name: string;
    verify(data: any, context: RuntimeContext): Promise<VerificationResult>;
    canVerify(ruleId: string): boolean;
    getRules(): ConformanceRule[];
    updateRule(rule: ConformanceRule): Promise<void>;
    removeRule(ruleId: string): Promise<void>;
}
export interface ViolationHandler {
    readonly category: ConformanceRuleCategory;
    readonly priority: number;
    handle(violation: ViolationDetails, context: RuntimeContext): Promise<void>;
    canHandle(violation: ViolationDetails): boolean;
}
export interface ConformanceVerificationResult {
    overall: VerificationStatus;
    results: VerificationResult[];
    violations: ViolationDetails[];
    summary: {
        totalRules: number;
        rulesExecuted: number;
        rulesPassed: number;
        rulesFailed: number;
        rulesSkipped: number;
        rulesError: number;
        totalDuration: number;
        violationsBySeverity: Record<ViolationSeverity, number>;
        violationsByCategory: Record<ConformanceRuleCategory, number>;
    };
    metadata: {
        executionId: string;
        timestamp: string;
        environment: string;
        version: string;
    };
}
export interface RuleExecutionContext {
    rule: ConformanceRule;
    input: any;
    output?: any;
    runtime: RuntimeContext;
    config: ConformanceConfig;
    cache: Map<string, any>;
}
export interface ViolationPattern {
    id: string;
    name: string;
    category: ConformanceRuleCategory;
    pattern: RegExp | string;
    confidence: number;
    description: string;
    suggestedFix?: string;
}
export interface ConformanceMetrics {
    timestamp: string;
    period: {
        start: string;
        end: string;
    };
    counts: {
        totalVerifications: number;
        totalViolations: number;
        uniqueRules: number;
        uniqueViolations: number;
    };
    performance: {
        averageExecutionTime: number;
        p95ExecutionTime: number;
        p99ExecutionTime: number;
        timeouts: number;
        errors: number;
    };
    violationTrends: {
        category: ConformanceRuleCategory;
        severity: ViolationSeverity;
        count: number;
        trend: 'increasing' | 'decreasing' | 'stable';
    }[];
    topViolations: {
        ruleId: string;
        ruleName: string;
        count: number;
        lastOccurrence: string;
    }[];
}
