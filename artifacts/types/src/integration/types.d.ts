/**
 * Integration Testing Types
 * Phase 2.3: Types and interfaces for comprehensive integration testing
 */
import { z } from 'zod';
export declare const TestStatusSchema: z.ZodEnum<["pending", "running", "passed", "failed", "skipped", "timeout", "error"]>;
export type TestStatus = z.infer<typeof TestStatusSchema>;
export declare const TestSeveritySchema: z.ZodEnum<["critical", "major", "minor", "info"]>;
export type TestSeverity = z.infer<typeof TestSeveritySchema>;
export declare const TestCategorySchema: z.ZodEnum<["unit", "integration", "e2e", "performance", "security", "accessibility", "compatibility", "regression", "smoke", "contract"]>;
export type TestCategory = z.infer<typeof TestCategorySchema>;
export declare const TestEnvironmentSchema: z.ZodObject<{
    name: z.ZodString;
    baseUrl: z.ZodOptional<z.ZodString>;
    apiUrl: z.ZodOptional<z.ZodString>;
    database: z.ZodOptional<z.ZodObject<{
        host: z.ZodString;
        port: z.ZodNumber;
        name: z.ZodString;
        username: z.ZodOptional<z.ZodString>;
        password: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        name?: string;
        host?: string;
        username?: string;
        password?: string;
        port?: number;
    }, {
        name?: string;
        host?: string;
        username?: string;
        password?: string;
        port?: number;
    }>>;
    variables: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodString>>;
    timeouts: z.ZodDefault<z.ZodObject<{
        default: z.ZodDefault<z.ZodNumber>;
        api: z.ZodDefault<z.ZodNumber>;
        ui: z.ZodDefault<z.ZodNumber>;
        database: z.ZodDefault<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        default?: number;
        api?: number;
        database?: number;
        ui?: number;
    }, {
        default?: number;
        api?: number;
        database?: number;
        ui?: number;
    }>>;
    retries: z.ZodDefault<z.ZodObject<{
        max: z.ZodDefault<z.ZodNumber>;
        delay: z.ZodDefault<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        max?: number;
        delay?: number;
    }, {
        max?: number;
        delay?: number;
    }>>;
}, "strip", z.ZodTypeAny, {
    name?: string;
    database?: {
        name?: string;
        host?: string;
        username?: string;
        password?: string;
        port?: number;
    };
    variables?: Record<string, string>;
    baseUrl?: string;
    apiUrl?: string;
    timeouts?: {
        default?: number;
        api?: number;
        database?: number;
        ui?: number;
    };
    retries?: {
        max?: number;
        delay?: number;
    };
}, {
    name?: string;
    database?: {
        name?: string;
        host?: string;
        username?: string;
        password?: string;
        port?: number;
    };
    variables?: Record<string, string>;
    baseUrl?: string;
    apiUrl?: string;
    timeouts?: {
        default?: number;
        api?: number;
        database?: number;
        ui?: number;
    };
    retries?: {
        max?: number;
        delay?: number;
    };
}>;
export type TestEnvironment = z.infer<typeof TestEnvironmentSchema>;
export declare const TestFixtureSchema: z.ZodObject<{
    id: z.ZodString;
    name: z.ZodString;
    description: z.ZodString;
    category: z.ZodEnum<["unit", "integration", "e2e", "performance", "security", "accessibility", "compatibility", "regression", "smoke", "contract"]>;
    data: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
    setup: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    teardown: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metadata: z.ZodObject<{
        createdAt: z.ZodString;
        updatedAt: z.ZodString;
        version: z.ZodDefault<z.ZodString>;
        tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        author: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        createdAt?: string;
        version?: string;
        author?: string;
        updatedAt?: string;
        tags?: string[];
    }, {
        createdAt?: string;
        version?: string;
        author?: string;
        updatedAt?: string;
        tags?: string[];
    }>;
}, "strip", z.ZodTypeAny, {
    name?: string;
    id?: string;
    dependencies?: string[];
    data?: Record<string, any>;
    description?: string;
    category?: "unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke";
    metadata?: {
        createdAt?: string;
        version?: string;
        author?: string;
        updatedAt?: string;
        tags?: string[];
    };
    setup?: string[];
    teardown?: string[];
}, {
    name?: string;
    id?: string;
    dependencies?: string[];
    data?: Record<string, any>;
    description?: string;
    category?: "unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke";
    metadata?: {
        createdAt?: string;
        version?: string;
        author?: string;
        updatedAt?: string;
        tags?: string[];
    };
    setup?: string[];
    teardown?: string[];
}>;
export type TestFixture = z.infer<typeof TestFixtureSchema>;
export declare const TestCaseSchema: z.ZodObject<{
    id: z.ZodString;
    name: z.ZodString;
    description: z.ZodString;
    category: z.ZodEnum<["unit", "integration", "e2e", "performance", "security", "accessibility", "compatibility", "regression", "smoke", "contract"]>;
    severity: z.ZodEnum<["critical", "major", "minor", "info"]>;
    enabled: z.ZodDefault<z.ZodBoolean>;
    preconditions: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    steps: z.ZodArray<z.ZodObject<{
        id: z.ZodString;
        description: z.ZodString;
        action: z.ZodString;
        data: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodAny>>;
        expectedResult: z.ZodOptional<z.ZodString>;
        timeout: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        id?: string;
        timeout?: number;
        data?: Record<string, any>;
        description?: string;
        action?: string;
        expectedResult?: string;
    }, {
        id?: string;
        timeout?: number;
        data?: Record<string, any>;
        description?: string;
        action?: string;
        expectedResult?: string;
    }>, "many">;
    expectedResults: z.ZodArray<z.ZodString, "many">;
    fixtures: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metadata: z.ZodObject<{
        estimatedDuration: z.ZodOptional<z.ZodNumber>;
        complexity: z.ZodDefault<z.ZodEnum<["low", "medium", "high"]>>;
        stability: z.ZodDefault<z.ZodEnum<["stable", "flaky", "unstable"]>>;
        lastUpdated: z.ZodString;
        maintainer: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        complexity?: "low" | "medium" | "high";
        lastUpdated?: string;
        estimatedDuration?: number;
        stability?: "stable" | "flaky" | "unstable";
        maintainer?: string;
    }, {
        complexity?: "low" | "medium" | "high";
        lastUpdated?: string;
        estimatedDuration?: number;
        stability?: "stable" | "flaky" | "unstable";
        maintainer?: string;
    }>;
}, "strip", z.ZodTypeAny, {
    enabled?: boolean;
    name?: string;
    id?: string;
    severity?: "critical" | "major" | "minor" | "info";
    dependencies?: string[];
    description?: string;
    category?: "unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke";
    metadata?: {
        complexity?: "low" | "medium" | "high";
        lastUpdated?: string;
        estimatedDuration?: number;
        stability?: "stable" | "flaky" | "unstable";
        maintainer?: string;
    };
    tags?: string[];
    preconditions?: string[];
    steps?: {
        id?: string;
        timeout?: number;
        data?: Record<string, any>;
        description?: string;
        action?: string;
        expectedResult?: string;
    }[];
    expectedResults?: string[];
    fixtures?: string[];
}, {
    enabled?: boolean;
    name?: string;
    id?: string;
    severity?: "critical" | "major" | "minor" | "info";
    dependencies?: string[];
    description?: string;
    category?: "unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke";
    metadata?: {
        complexity?: "low" | "medium" | "high";
        lastUpdated?: string;
        estimatedDuration?: number;
        stability?: "stable" | "flaky" | "unstable";
        maintainer?: string;
    };
    tags?: string[];
    preconditions?: string[];
    steps?: {
        id?: string;
        timeout?: number;
        data?: Record<string, any>;
        description?: string;
        action?: string;
        expectedResult?: string;
    }[];
    expectedResults?: string[];
    fixtures?: string[];
}>;
export type TestCase = z.infer<typeof TestCaseSchema>;
export declare const TestResultSchema: z.ZodObject<{
    id: z.ZodString;
    testId: z.ZodString;
    status: z.ZodEnum<["pending", "running", "passed", "failed", "skipped", "timeout", "error"]>;
    startTime: z.ZodString;
    endTime: z.ZodOptional<z.ZodString>;
    duration: z.ZodNumber;
    environment: z.ZodString;
    steps: z.ZodArray<z.ZodObject<{
        id: z.ZodString;
        status: z.ZodEnum<["pending", "running", "passed", "failed", "skipped", "timeout", "error"]>;
        startTime: z.ZodString;
        endTime: z.ZodOptional<z.ZodString>;
        duration: z.ZodNumber;
        actualResult: z.ZodOptional<z.ZodString>;
        error: z.ZodOptional<z.ZodString>;
        screenshots: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
    }, "strip", z.ZodTypeAny, {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        error?: string;
        id?: string;
        metrics?: Record<string, number>;
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        screenshots?: string[];
        actualResult?: string;
    }, {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        error?: string;
        id?: string;
        metrics?: Record<string, number>;
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        screenshots?: string[];
        actualResult?: string;
    }>, "many">;
    error: z.ZodOptional<z.ZodString>;
    stackTrace: z.ZodOptional<z.ZodString>;
    screenshots: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metrics: z.ZodDefault<z.ZodObject<{
        memoryUsage: z.ZodOptional<z.ZodNumber>;
        cpuUsage: z.ZodOptional<z.ZodNumber>;
        networkCalls: z.ZodDefault<z.ZodNumber>;
        databaseQueries: z.ZodDefault<z.ZodNumber>;
        responseTime: z.ZodOptional<z.ZodNumber>;
        renderTime: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        responseTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        databaseQueries?: number;
        renderTime?: number;
    }, {
        responseTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        databaseQueries?: number;
        renderTime?: number;
    }>>;
    coverage: z.ZodOptional<z.ZodObject<{
        lines: z.ZodOptional<z.ZodNumber>;
        functions: z.ZodOptional<z.ZodNumber>;
        branches: z.ZodOptional<z.ZodNumber>;
        statements: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
    }, {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
    }>>;
    artifacts: z.ZodDefault<z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        path: z.ZodString;
        type: z.ZodEnum<["log", "screenshot", "video", "report", "data"]>;
        size: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        path?: string;
        type?: "report" | "log" | "data" | "screenshot" | "video";
        name?: string;
        size?: number;
    }, {
        path?: string;
        type?: "report" | "log" | "data" | "screenshot" | "video";
        name?: string;
        size?: number;
    }>, "many">>;
}, "strip", z.ZodTypeAny, {
    status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
    artifacts?: {
        path?: string;
        type?: "report" | "log" | "data" | "screenshot" | "video";
        name?: string;
        size?: number;
    }[];
    error?: string;
    id?: string;
    environment?: string;
    coverage?: {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
    };
    metrics?: {
        responseTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        databaseQueries?: number;
        renderTime?: number;
    };
    logs?: string[];
    startTime?: string;
    endTime?: string;
    duration?: number;
    stackTrace?: string;
    screenshots?: string[];
    steps?: {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        error?: string;
        id?: string;
        metrics?: Record<string, number>;
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        screenshots?: string[];
        actualResult?: string;
    }[];
    testId?: string;
}, {
    status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
    artifacts?: {
        path?: string;
        type?: "report" | "log" | "data" | "screenshot" | "video";
        name?: string;
        size?: number;
    }[];
    error?: string;
    id?: string;
    environment?: string;
    coverage?: {
        branches?: number;
        lines?: number;
        functions?: number;
        statements?: number;
    };
    metrics?: {
        responseTime?: number;
        cpuUsage?: number;
        memoryUsage?: number;
        networkCalls?: number;
        databaseQueries?: number;
        renderTime?: number;
    };
    logs?: string[];
    startTime?: string;
    endTime?: string;
    duration?: number;
    stackTrace?: string;
    screenshots?: string[];
    steps?: {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        error?: string;
        id?: string;
        metrics?: Record<string, number>;
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        screenshots?: string[];
        actualResult?: string;
    }[];
    testId?: string;
}>;
export type TestResult = z.infer<typeof TestResultSchema>;
export declare const TestSuiteSchema: z.ZodObject<{
    id: z.ZodString;
    name: z.ZodString;
    description: z.ZodString;
    category: z.ZodEnum<["unit", "integration", "e2e", "performance", "security", "accessibility", "compatibility", "regression", "smoke", "contract"]>;
    tests: z.ZodArray<z.ZodString, "many">;
    fixtures: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    configuration: z.ZodDefault<z.ZodObject<{
        parallel: z.ZodDefault<z.ZodBoolean>;
        maxConcurrency: z.ZodDefault<z.ZodNumber>;
        timeout: z.ZodDefault<z.ZodNumber>;
        retries: z.ZodDefault<z.ZodNumber>;
        skipOnFailure: z.ZodDefault<z.ZodBoolean>;
        failFast: z.ZodDefault<z.ZodBoolean>;
    }, "strip", z.ZodTypeAny, {
        timeout?: number;
        parallel?: boolean;
        maxConcurrency?: number;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
    }, {
        timeout?: number;
        parallel?: boolean;
        maxConcurrency?: number;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
    }>>;
    setup: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    teardown: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metadata: z.ZodObject<{
        estimatedDuration: z.ZodOptional<z.ZodNumber>;
        priority: z.ZodDefault<z.ZodEnum<["low", "medium", "high", "critical"]>>;
        schedule: z.ZodOptional<z.ZodString>;
        owner: z.ZodOptional<z.ZodString>;
        tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        priority?: "critical" | "low" | "medium" | "high";
        schedule?: string;
        tags?: string[];
        owner?: string;
        estimatedDuration?: number;
    }, {
        priority?: "critical" | "low" | "medium" | "high";
        schedule?: string;
        tags?: string[];
        owner?: string;
        estimatedDuration?: number;
    }>;
}, "strip", z.ZodTypeAny, {
    name?: string;
    id?: string;
    tests?: string[];
    description?: string;
    category?: "unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke";
    metadata?: {
        priority?: "critical" | "low" | "medium" | "high";
        schedule?: string;
        tags?: string[];
        owner?: string;
        estimatedDuration?: number;
    };
    configuration?: {
        timeout?: number;
        parallel?: boolean;
        maxConcurrency?: number;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
    };
    setup?: string[];
    teardown?: string[];
    fixtures?: string[];
}, {
    name?: string;
    id?: string;
    tests?: string[];
    description?: string;
    category?: "unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke";
    metadata?: {
        priority?: "critical" | "low" | "medium" | "high";
        schedule?: string;
        tags?: string[];
        owner?: string;
        estimatedDuration?: number;
    };
    configuration?: {
        timeout?: number;
        parallel?: boolean;
        maxConcurrency?: number;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
    };
    setup?: string[];
    teardown?: string[];
    fixtures?: string[];
}>;
export type TestSuite = z.infer<typeof TestSuiteSchema>;
export declare const TestExecutionConfigSchema: z.ZodObject<{
    environment: z.ZodString;
    parallel: z.ZodDefault<z.ZodBoolean>;
    maxConcurrency: z.ZodDefault<z.ZodNumber>;
    timeout: z.ZodDefault<z.ZodNumber>;
    retries: z.ZodDefault<z.ZodNumber>;
    skipOnFailure: z.ZodDefault<z.ZodBoolean>;
    failFast: z.ZodDefault<z.ZodBoolean>;
    generateReport: z.ZodDefault<z.ZodBoolean>;
    captureScreenshots: z.ZodDefault<z.ZodBoolean>;
    recordVideo: z.ZodDefault<z.ZodBoolean>;
    collectLogs: z.ZodDefault<z.ZodBoolean>;
    measureCoverage: z.ZodDefault<z.ZodBoolean>;
    outputDir: z.ZodDefault<z.ZodString>;
    reportFormat: z.ZodDefault<z.ZodArray<z.ZodEnum<["json", "html", "xml", "junit"]>, "many">>;
    filters: z.ZodDefault<z.ZodObject<{
        categories: z.ZodOptional<z.ZodArray<z.ZodEnum<["unit", "integration", "e2e", "performance", "security", "accessibility", "compatibility", "regression", "smoke", "contract"]>, "many">>;
        tags: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
        severity: z.ZodOptional<z.ZodArray<z.ZodEnum<["critical", "major", "minor", "info"]>, "many">>;
        exclude: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        exclude?: string[];
        severity?: ("critical" | "major" | "minor" | "info")[];
        categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
        tags?: string[];
    }, {
        exclude?: string[];
        severity?: ("critical" | "major" | "minor" | "info")[];
        categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
        tags?: string[];
    }>>;
}, "strip", z.ZodTypeAny, {
    timeout?: number;
    environment?: string;
    parallel?: boolean;
    maxConcurrency?: number;
    generateReport?: boolean;
    outputDir?: string;
    retries?: number;
    skipOnFailure?: boolean;
    failFast?: boolean;
    captureScreenshots?: boolean;
    recordVideo?: boolean;
    collectLogs?: boolean;
    measureCoverage?: boolean;
    reportFormat?: ("json" | "html" | "xml" | "junit")[];
    filters?: {
        exclude?: string[];
        severity?: ("critical" | "major" | "minor" | "info")[];
        categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
        tags?: string[];
    };
}, {
    timeout?: number;
    environment?: string;
    parallel?: boolean;
    maxConcurrency?: number;
    generateReport?: boolean;
    outputDir?: string;
    retries?: number;
    skipOnFailure?: boolean;
    failFast?: boolean;
    captureScreenshots?: boolean;
    recordVideo?: boolean;
    collectLogs?: boolean;
    measureCoverage?: boolean;
    reportFormat?: ("json" | "html" | "xml" | "junit")[];
    filters?: {
        exclude?: string[];
        severity?: ("critical" | "major" | "minor" | "info")[];
        categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
        tags?: string[];
    };
}>;
export type TestExecutionConfig = z.infer<typeof TestExecutionConfigSchema>;
export declare const TestExecutionSummarySchema: z.ZodObject<{
    id: z.ZodString;
    startTime: z.ZodString;
    endTime: z.ZodString;
    duration: z.ZodNumber;
    environment: z.ZodString;
    configuration: z.ZodObject<{
        environment: z.ZodString;
        parallel: z.ZodDefault<z.ZodBoolean>;
        maxConcurrency: z.ZodDefault<z.ZodNumber>;
        timeout: z.ZodDefault<z.ZodNumber>;
        retries: z.ZodDefault<z.ZodNumber>;
        skipOnFailure: z.ZodDefault<z.ZodBoolean>;
        failFast: z.ZodDefault<z.ZodBoolean>;
        generateReport: z.ZodDefault<z.ZodBoolean>;
        captureScreenshots: z.ZodDefault<z.ZodBoolean>;
        recordVideo: z.ZodDefault<z.ZodBoolean>;
        collectLogs: z.ZodDefault<z.ZodBoolean>;
        measureCoverage: z.ZodDefault<z.ZodBoolean>;
        outputDir: z.ZodDefault<z.ZodString>;
        reportFormat: z.ZodDefault<z.ZodArray<z.ZodEnum<["json", "html", "xml", "junit"]>, "many">>;
        filters: z.ZodDefault<z.ZodObject<{
            categories: z.ZodOptional<z.ZodArray<z.ZodEnum<["unit", "integration", "e2e", "performance", "security", "accessibility", "compatibility", "regression", "smoke", "contract"]>, "many">>;
            tags: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
            severity: z.ZodOptional<z.ZodArray<z.ZodEnum<["critical", "major", "minor", "info"]>, "many">>;
            exclude: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
        }, "strip", z.ZodTypeAny, {
            exclude?: string[];
            severity?: ("critical" | "major" | "minor" | "info")[];
            categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
            tags?: string[];
        }, {
            exclude?: string[];
            severity?: ("critical" | "major" | "minor" | "info")[];
            categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
            tags?: string[];
        }>>;
    }, "strip", z.ZodTypeAny, {
        timeout?: number;
        environment?: string;
        parallel?: boolean;
        maxConcurrency?: number;
        generateReport?: boolean;
        outputDir?: string;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
        captureScreenshots?: boolean;
        recordVideo?: boolean;
        collectLogs?: boolean;
        measureCoverage?: boolean;
        reportFormat?: ("json" | "html" | "xml" | "junit")[];
        filters?: {
            exclude?: string[];
            severity?: ("critical" | "major" | "minor" | "info")[];
            categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
            tags?: string[];
        };
    }, {
        timeout?: number;
        environment?: string;
        parallel?: boolean;
        maxConcurrency?: number;
        generateReport?: boolean;
        outputDir?: string;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
        captureScreenshots?: boolean;
        recordVideo?: boolean;
        collectLogs?: boolean;
        measureCoverage?: boolean;
        reportFormat?: ("json" | "html" | "xml" | "junit")[];
        filters?: {
            exclude?: string[];
            severity?: ("critical" | "major" | "minor" | "info")[];
            categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
            tags?: string[];
        };
    }>;
    statistics: z.ZodObject<{
        total: z.ZodNumber;
        passed: z.ZodNumber;
        failed: z.ZodNumber;
        skipped: z.ZodNumber;
        timeout: z.ZodNumber;
        error: z.ZodNumber;
        passRate: z.ZodNumber;
        coverage: z.ZodOptional<z.ZodObject<{
            lines: z.ZodOptional<z.ZodNumber>;
            functions: z.ZodOptional<z.ZodNumber>;
            branches: z.ZodOptional<z.ZodNumber>;
            statements: z.ZodOptional<z.ZodNumber>;
        }, "strip", z.ZodTypeAny, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        }, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        }>>;
    }, "strip", z.ZodTypeAny, {
        error?: number;
        timeout?: number;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        failed?: number;
        passed?: number;
        total?: number;
        skipped?: number;
        passRate?: number;
    }, {
        error?: number;
        timeout?: number;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        failed?: number;
        passed?: number;
        total?: number;
        skipped?: number;
        passRate?: number;
    }>;
    results: z.ZodArray<z.ZodObject<{
        id: z.ZodString;
        testId: z.ZodString;
        status: z.ZodEnum<["pending", "running", "passed", "failed", "skipped", "timeout", "error"]>;
        startTime: z.ZodString;
        endTime: z.ZodOptional<z.ZodString>;
        duration: z.ZodNumber;
        environment: z.ZodString;
        steps: z.ZodArray<z.ZodObject<{
            id: z.ZodString;
            status: z.ZodEnum<["pending", "running", "passed", "failed", "skipped", "timeout", "error"]>;
            startTime: z.ZodString;
            endTime: z.ZodOptional<z.ZodString>;
            duration: z.ZodNumber;
            actualResult: z.ZodOptional<z.ZodString>;
            error: z.ZodOptional<z.ZodString>;
            screenshots: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
            logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
            metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
        }, "strip", z.ZodTypeAny, {
            status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
            error?: string;
            id?: string;
            metrics?: Record<string, number>;
            logs?: string[];
            startTime?: string;
            endTime?: string;
            duration?: number;
            screenshots?: string[];
            actualResult?: string;
        }, {
            status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
            error?: string;
            id?: string;
            metrics?: Record<string, number>;
            logs?: string[];
            startTime?: string;
            endTime?: string;
            duration?: number;
            screenshots?: string[];
            actualResult?: string;
        }>, "many">;
        error: z.ZodOptional<z.ZodString>;
        stackTrace: z.ZodOptional<z.ZodString>;
        screenshots: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        metrics: z.ZodDefault<z.ZodObject<{
            memoryUsage: z.ZodOptional<z.ZodNumber>;
            cpuUsage: z.ZodOptional<z.ZodNumber>;
            networkCalls: z.ZodDefault<z.ZodNumber>;
            databaseQueries: z.ZodDefault<z.ZodNumber>;
            responseTime: z.ZodOptional<z.ZodNumber>;
            renderTime: z.ZodOptional<z.ZodNumber>;
        }, "strip", z.ZodTypeAny, {
            responseTime?: number;
            cpuUsage?: number;
            memoryUsage?: number;
            networkCalls?: number;
            databaseQueries?: number;
            renderTime?: number;
        }, {
            responseTime?: number;
            cpuUsage?: number;
            memoryUsage?: number;
            networkCalls?: number;
            databaseQueries?: number;
            renderTime?: number;
        }>>;
        coverage: z.ZodOptional<z.ZodObject<{
            lines: z.ZodOptional<z.ZodNumber>;
            functions: z.ZodOptional<z.ZodNumber>;
            branches: z.ZodOptional<z.ZodNumber>;
            statements: z.ZodOptional<z.ZodNumber>;
        }, "strip", z.ZodTypeAny, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        }, {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        }>>;
        artifacts: z.ZodDefault<z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            path: z.ZodString;
            type: z.ZodEnum<["log", "screenshot", "video", "report", "data"]>;
            size: z.ZodOptional<z.ZodNumber>;
        }, "strip", z.ZodTypeAny, {
            path?: string;
            type?: "report" | "log" | "data" | "screenshot" | "video";
            name?: string;
            size?: number;
        }, {
            path?: string;
            type?: "report" | "log" | "data" | "screenshot" | "video";
            name?: string;
            size?: number;
        }>, "many">>;
    }, "strip", z.ZodTypeAny, {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        artifacts?: {
            path?: string;
            type?: "report" | "log" | "data" | "screenshot" | "video";
            name?: string;
            size?: number;
        }[];
        error?: string;
        id?: string;
        environment?: string;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        metrics?: {
            responseTime?: number;
            cpuUsage?: number;
            memoryUsage?: number;
            networkCalls?: number;
            databaseQueries?: number;
            renderTime?: number;
        };
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        stackTrace?: string;
        screenshots?: string[];
        steps?: {
            status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
            error?: string;
            id?: string;
            metrics?: Record<string, number>;
            logs?: string[];
            startTime?: string;
            endTime?: string;
            duration?: number;
            screenshots?: string[];
            actualResult?: string;
        }[];
        testId?: string;
    }, {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        artifacts?: {
            path?: string;
            type?: "report" | "log" | "data" | "screenshot" | "video";
            name?: string;
            size?: number;
        }[];
        error?: string;
        id?: string;
        environment?: string;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        metrics?: {
            responseTime?: number;
            cpuUsage?: number;
            memoryUsage?: number;
            networkCalls?: number;
            databaseQueries?: number;
            renderTime?: number;
        };
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        stackTrace?: string;
        screenshots?: string[];
        steps?: {
            status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
            error?: string;
            id?: string;
            metrics?: Record<string, number>;
            logs?: string[];
            startTime?: string;
            endTime?: string;
            duration?: number;
            screenshots?: string[];
            actualResult?: string;
        }[];
        testId?: string;
    }>, "many">;
    failures: z.ZodArray<z.ZodObject<{
        testId: z.ZodString;
        testName: z.ZodString;
        error: z.ZodString;
        stackTrace: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        error?: string;
        stackTrace?: string;
        testId?: string;
        testName?: string;
    }, {
        error?: string;
        stackTrace?: string;
        testId?: string;
        testName?: string;
    }>, "many">;
    artifacts: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        path: z.ZodString;
        size: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        path?: string;
        name?: string;
        size?: number;
    }, {
        path?: string;
        name?: string;
        size?: number;
    }>, "many">;
    metadata: z.ZodDefault<z.ZodObject<{
        nodeVersion: z.ZodOptional<z.ZodString>;
        platform: z.ZodOptional<z.ZodString>;
        browser: z.ZodOptional<z.ZodString>;
        browserVersion: z.ZodOptional<z.ZodString>;
        resolution: z.ZodOptional<z.ZodString>;
        commit: z.ZodOptional<z.ZodString>;
        branch: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        platform?: string;
        browser?: string;
        branch?: string;
        nodeVersion?: string;
        browserVersion?: string;
        resolution?: string;
        commit?: string;
    }, {
        platform?: string;
        browser?: string;
        branch?: string;
        nodeVersion?: string;
        browserVersion?: string;
        resolution?: string;
        commit?: string;
    }>>;
}, "strip", z.ZodTypeAny, {
    artifacts?: {
        path?: string;
        name?: string;
        size?: number;
    }[];
    id?: string;
    environment?: string;
    startTime?: string;
    endTime?: string;
    results?: {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        artifacts?: {
            path?: string;
            type?: "report" | "log" | "data" | "screenshot" | "video";
            name?: string;
            size?: number;
        }[];
        error?: string;
        id?: string;
        environment?: string;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        metrics?: {
            responseTime?: number;
            cpuUsage?: number;
            memoryUsage?: number;
            networkCalls?: number;
            databaseQueries?: number;
            renderTime?: number;
        };
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        stackTrace?: string;
        screenshots?: string[];
        steps?: {
            status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
            error?: string;
            id?: string;
            metrics?: Record<string, number>;
            logs?: string[];
            startTime?: string;
            endTime?: string;
            duration?: number;
            screenshots?: string[];
            actualResult?: string;
        }[];
        testId?: string;
    }[];
    statistics?: {
        error?: number;
        timeout?: number;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        failed?: number;
        passed?: number;
        total?: number;
        skipped?: number;
        passRate?: number;
    };
    duration?: number;
    failures?: {
        error?: string;
        stackTrace?: string;
        testId?: string;
        testName?: string;
    }[];
    metadata?: {
        platform?: string;
        browser?: string;
        branch?: string;
        nodeVersion?: string;
        browserVersion?: string;
        resolution?: string;
        commit?: string;
    };
    configuration?: {
        timeout?: number;
        environment?: string;
        parallel?: boolean;
        maxConcurrency?: number;
        generateReport?: boolean;
        outputDir?: string;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
        captureScreenshots?: boolean;
        recordVideo?: boolean;
        collectLogs?: boolean;
        measureCoverage?: boolean;
        reportFormat?: ("json" | "html" | "xml" | "junit")[];
        filters?: {
            exclude?: string[];
            severity?: ("critical" | "major" | "minor" | "info")[];
            categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
            tags?: string[];
        };
    };
}, {
    artifacts?: {
        path?: string;
        name?: string;
        size?: number;
    }[];
    id?: string;
    environment?: string;
    startTime?: string;
    endTime?: string;
    results?: {
        status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
        artifacts?: {
            path?: string;
            type?: "report" | "log" | "data" | "screenshot" | "video";
            name?: string;
            size?: number;
        }[];
        error?: string;
        id?: string;
        environment?: string;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        metrics?: {
            responseTime?: number;
            cpuUsage?: number;
            memoryUsage?: number;
            networkCalls?: number;
            databaseQueries?: number;
            renderTime?: number;
        };
        logs?: string[];
        startTime?: string;
        endTime?: string;
        duration?: number;
        stackTrace?: string;
        screenshots?: string[];
        steps?: {
            status?: "error" | "pending" | "timeout" | "running" | "failed" | "passed" | "skipped";
            error?: string;
            id?: string;
            metrics?: Record<string, number>;
            logs?: string[];
            startTime?: string;
            endTime?: string;
            duration?: number;
            screenshots?: string[];
            actualResult?: string;
        }[];
        testId?: string;
    }[];
    statistics?: {
        error?: number;
        timeout?: number;
        coverage?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
        failed?: number;
        passed?: number;
        total?: number;
        skipped?: number;
        passRate?: number;
    };
    duration?: number;
    failures?: {
        error?: string;
        stackTrace?: string;
        testId?: string;
        testName?: string;
    }[];
    metadata?: {
        platform?: string;
        browser?: string;
        branch?: string;
        nodeVersion?: string;
        browserVersion?: string;
        resolution?: string;
        commit?: string;
    };
    configuration?: {
        timeout?: number;
        environment?: string;
        parallel?: boolean;
        maxConcurrency?: number;
        generateReport?: boolean;
        outputDir?: string;
        retries?: number;
        skipOnFailure?: boolean;
        failFast?: boolean;
        captureScreenshots?: boolean;
        recordVideo?: boolean;
        collectLogs?: boolean;
        measureCoverage?: boolean;
        reportFormat?: ("json" | "html" | "xml" | "junit")[];
        filters?: {
            exclude?: string[];
            severity?: ("critical" | "major" | "minor" | "info")[];
            categories?: ("unit" | "integration" | "e2e" | "performance" | "security" | "contract" | "accessibility" | "compatibility" | "regression" | "smoke")[];
            tags?: string[];
        };
    };
}>;
export type TestExecutionSummary = z.infer<typeof TestExecutionSummarySchema>;
export interface TestRunner {
    readonly id: string;
    readonly name: string;
    readonly category: TestCategory;
    canRun(test: TestCase): boolean;
    runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult>;
    runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary>;
    setup?(environment: TestEnvironment): Promise<void>;
    teardown?(environment: TestEnvironment): Promise<void>;
    beforeTest?(test: TestCase): Promise<void>;
    afterTest?(test: TestCase, result: TestResult): Promise<void>;
}
export interface TestReporter {
    readonly name: string;
    readonly format: string;
    generateReport(summary: TestExecutionSummary): Promise<string>;
    saveReport(content: string, filePath: string): Promise<void>;
}
export interface IntegrationTestConfig {
    environments: TestEnvironment[];
    defaultEnvironment: string;
    runners: TestRunner[];
    reporters: TestReporter[];
    globalTimeout: number;
    globalRetries: number;
    parallelSuites: boolean;
    maxSuiteConcurrency: number;
    artifactRetention: {
        days: number;
        maxSize: number;
    };
    notifications: {
        enabled: boolean;
        channels: string[];
        onFailure: boolean;
        onSuccess: boolean;
    };
}
export interface TestDiscovery {
    discoverTests(patterns: string[]): Promise<TestCase[]>;
    discoverSuites(patterns: string[]): Promise<TestSuite[]>;
    discoverFixtures(patterns: string[]): Promise<TestFixture[]>;
}
export interface TestExecutionContext {
    testId: string;
    suiteId?: string;
    environment: TestEnvironment;
    config: TestExecutionConfig;
    fixtures: Map<string, TestFixture>;
    sharedData: Map<string, any>;
    logger: {
        info: (message: string) => void;
        warn: (message: string) => void;
        error: (message: string) => void;
        debug: (message: string) => void;
    };
    metrics: {
        startTimer: (name: string) => void;
        endTimer: (name: string) => number;
        increment: (name: string, value?: number) => void;
        gauge: (name: string, value: number) => void;
    };
}
export type E2EStepType = 'navigate' | 'click' | 'type' | 'select' | 'wait' | 'verify' | 'screenshot' | 'custom' | 'api_call' | 'database_query';
export interface E2ETestStep {
    type: E2EStepType;
    selector?: string;
    value?: string;
    timeout?: number;
    retry?: boolean;
    screenshot?: boolean;
    description: string;
    data?: Record<string, any>;
    validation?: {
        type: 'text' | 'attribute' | 'css' | 'count' | 'exists';
        expected: any;
        actual?: any;
    };
}
export interface ContractTest {
    provider: string;
    consumer: string;
    interactions: Array<{
        description: string;
        request: {
            method: string;
            path: string;
            headers?: Record<string, string>;
            body?: any;
        };
        response: {
            status: number;
            headers?: Record<string, string>;
            body?: any;
        };
    }>;
    metadata: {
        version: string;
        createdAt: string;
        tags: string[];
    };
}
export interface PerformanceMetrics {
    responseTime: {
        min: number;
        max: number;
        avg: number;
        p50: number;
        p95: number;
        p99: number;
    };
    throughput: {
        requestsPerSecond: number;
        totalRequests: number;
    };
    resource: {
        cpuUsage: number;
        memoryUsage: number;
        diskIO: number;
        networkIO: number;
    };
    errors: {
        total: number;
        rate: number;
        types: Record<string, number>;
    };
    custom: Record<string, number>;
}
