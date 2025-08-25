// ---- agents/domain-types.d.ts ----
/**
 * @fileoverview Domain Types for Unified Agent System
 * Phase 2: Agent System Refactoring - Domain Modeling Implementation
 * Core domain types for unified agent architecture per ae-framework-v2.yml
 */
/**
 * Task types supported by the unified agent system
 */
export declare enum TaskType {
    INTENT_ANALYSIS = "intent-analysis",
    FORMAL_SPECIFICATION = "formal-specification",
    TEST_GENERATION = "test-generation",
    CODE_GENERATION = "code-generation",
    VERIFICATION = "verification",
    VALIDATION = "validation",
    DEPLOYMENT = "deployment",
    QUALITY_ASSURANCE = "quality-assurance",
    PHASE_VALIDATION = "phase-validation"
}
/**
 * Task specification structure for unified processing
 */
export interface TaskSpecification {
    requirements: string;
    acceptance: string[];
    context: Record<string, any>;
}
/**
 * Unified task definition for all agent types
 */
export interface AgentTask {
    id: string;
    type: TaskType;
    specification: TaskSpecification;
    metadata: {
        priority: number;
        estimatedComplexity: number;
        dependencies?: string[];
        deadline?: Date;
    };
}
/**
 * Task execution result with validation
 */
export interface TaskResult {
    success: boolean;
    taskId: string;
    artifacts: string[];
    validation: {
        typeScriptCompliant: boolean;
        strictModeCompatible?: boolean;
        errorCount: number;
        testsPassing?: boolean;
    };
    tddCompliance?: {
        testsFirst: boolean;
        redPhaseCompleted: boolean;
        greenPhaseCompleted: boolean;
        refactorPhaseCompleted?: boolean;
    };
    metrics?: {
        testCoverage: number;
        executionTime: number;
        qualityScore: number;
    };
    phaseValidation?: {
        readyForNextPhase: boolean;
        completionCriteria: string[];
    };
    errors?: string[];
}
/**
 * Agent context for phase and project state
 */
export interface AgentContext {
    projectRoot: string;
    phase: string;
    tddEnabled: boolean;
    strictMode?: boolean;
    coverageThreshold?: number;
}
/**
 * Unified agent configuration
 */
export interface AgentConfig {
    id: string;
    type: string;
    capabilities: string[];
    context: AgentContext;
}
/**
 * Agent state for lifecycle management
 */
export interface AgentState {
    initialized: boolean;
    currentTask?: string;
    tasksCompleted: number;
    totalExecutionTime: number;
    averageQualityScore: number;
}
/**
 * Quality metrics for agent output validation
 */
export interface QualityMetrics {
    testCoverage: number;
    codeComplexity: number;
    typeScriptErrors: number;
    lintWarnings: number;
    performanceScore: number;
}
/**
 * Validation result structure
 */
export interface ValidationResult {
    success: boolean;
    message: string;
    details: Array<{
        check: string;
        passed: boolean;
        message: string;
        value?: any;
    }>;
}

// ---- api/middleware/security-headers.d.ts ----
/**
 * Security Headers Middleware
 * Implements basic HTTP security headers for the AE-Framework API
 */
import { FastifyInstance } from 'fastify';
export interface SecurityHeadersOptions {
    /** Enable/disable all security headers */
    enabled?: boolean;
    /** Content Security Policy */
    contentSecurityPolicy?: {
        enabled?: boolean;
        directives?: string;
    };
    /** X-Frame-Options */
    frameOptions?: {
        enabled?: boolean;
        value?: 'DENY' | 'SAMEORIGIN' | string;
    };
    /** X-Content-Type-Options */
    contentTypeOptions?: {
        enabled?: boolean;
    };
    /** Referrer-Policy */
    referrerPolicy?: {
        enabled?: boolean;
        value?: string;
    };
    /** Strict-Transport-Security */
    strictTransportSecurity?: {
        enabled?: boolean;
        maxAge?: number;
        includeSubDomains?: boolean;
        preload?: boolean;
    };
    /** X-XSS-Protection */
    xssProtection?: {
        enabled?: boolean;
        value?: string;
    };
    /** Permissions-Policy */
    permissionsPolicy?: {
        enabled?: boolean;
        directives?: string;
    };
}
/**
 * Fastify plugin for security headers
 */
export declare function securityHeadersPlugin(fastify: FastifyInstance, options?: SecurityHeadersOptions): Promise<void>;
/**
 * Environment-specific security configurations
 */
export declare const securityConfigurations: {
    development: SecurityHeadersOptions;
    testing: SecurityHeadersOptions;
    production: SecurityHeadersOptions;
};
/**
 * Get security configuration for current environment
 */
export declare function getSecurityConfiguration(environment?: string): SecurityHeadersOptions;
export default securityHeadersPlugin;

// ---- api/routes/reservations.d.ts ----
import { FastifyInstance } from 'fastify';
import { InventoryService } from '../../domain/services.js';
export declare function reservationRoutes(fastify: FastifyInstance, options: {
    inventoryService: InventoryService;
}): Promise<void>;

// ---- api/server.d.ts ----
import { FastifyInstance } from "fastify";
/**
 * Create and configure Fastify server instance
 */
export declare function createServer(): Promise<FastifyInstance>;
export default function getServer(): Promise<FastifyInstance<import("fastify").RawServerDefault, import("http").IncomingMessage, import("http").ServerResponse<import("http").IncomingMessage>, import("fastify").FastifyBaseLogger, import("fastify").FastifyTypeProviderDefault>>;

// ---- core/assertNever.d.ts ----
/**
 * Exhaustive type checking utility function
 */
export declare function assertNever(x: never, msg?: string): never;

// ---- core/config.d.ts ----
import { z } from 'zod';
export declare const AeConfigSchema: z.ZodObject<{
    tddGuard: z.ZodDefault<z.ZodObject<{
        enabled: z.ZodDefault<z.ZodBoolean>;
        onlyChanged: z.ZodDefault<z.ZodBoolean>;
        changedSince: z.ZodDefault<z.ZodString>;
        include: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        exclude: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        allowSkipWithEnv: z.ZodDefault<z.ZodString>;
        ciOnly: z.ZodDefault<z.ZodBoolean>;
    }, "strip", z.ZodTypeAny, {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    }, {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    }>>;
    qa: z.ZodDefault<z.ZodObject<{
        coverageThreshold: z.ZodDefault<z.ZodObject<{
            branches: z.ZodDefault<z.ZodNumber>;
            lines: z.ZodDefault<z.ZodNumber>;
            functions: z.ZodDefault<z.ZodNumber>;
            statements: z.ZodDefault<z.ZodNumber>;
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
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    }, {
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    }>>;
    bench: z.ZodDefault<z.ZodObject<{
        warmupMs: z.ZodDefault<z.ZodNumber>;
        iterations: z.ZodDefault<z.ZodNumber>;
        seed: z.ZodDefault<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    }, {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    }>>;
}, "strict", z.ZodTypeAny, {
    tddGuard?: {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    };
    qa?: {
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    };
    bench?: {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    };
}, {
    tddGuard?: {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    };
    qa?: {
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    };
    bench?: {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    };
}>;
export type AeConfig = z.infer<typeof AeConfigSchema>;
export declare function loadConfig(): Promise<AeConfig>;

// ---- core/errors.d.ts ----
export type AppError = {
    code: 'E_EXEC';
    step: string;
    detail?: string;
} | {
    code: 'E_PARSE';
    step: string;
    detail?: string;
} | {
    code: 'E_TIMEOUT';
    step: string;
    ms: number;
} | {
    code: 'E_CONFIG';
    key: string;
    detail?: string;
};

// ---- core/exec.d.ts ----
import { type Result } from './result.js';
import type { AppError } from './errors.js';
export declare function run(step: string, cmd: string, args: string[], opts?: any): Promise<Result<{
    stdout: string;
}, AppError>>;

// ---- core/result.d.ts ----
export type Ok<T> = {
    ok: true;
    value: T;
};
export type Err<E extends {
    code: string;
}> = {
    ok: false;
    error: E;
};
export type Result<T, E extends {
    code: string;
} = {
    code: string;
    message?: string;
}> = Ok<T> | Err<E>;
export declare const ok: <T>(value: T) => Ok<T>;
export declare const err: <E extends {
    code: string;
}>(e: E) => Err<E>;
export declare function isOk<T, E extends {
    code: string;
}>(r: Result<T, E>): r is Ok<T>;
export declare function isErr<T, E extends {
    code: string;
}>(r: Result<T, E>): r is Err<E>;
export declare function unwrap<T, E extends {
    code: string;
}>(r: Result<T, E>): T;

// ---- core/seed.d.ts ----
export declare function getSeed(): number | undefined;

// ---- domain/contracts.d.ts ----
import { z } from "zod";
export declare const Reservation: z.ZodObject<{
    orderId: z.ZodString;
    itemId: z.ZodString;
    quantity: z.ZodNumber;
}, "strip", z.ZodTypeAny, {
    orderId?: string;
    itemId?: string;
    quantity?: number;
}, {
    orderId?: string;
    itemId?: string;
    quantity?: number;
}>;
export type Reservation = z.infer<typeof Reservation>;

// ---- domain/entities.d.ts ----
export interface Item {
    id: string;
    name: string;
    stock: number;
    reserved: number;
}
export interface ReservationEntity {
    id: string;
    orderId: string;
    itemId: string;
    quantity: number;
    createdAt: Date;
    status: 'pending' | 'confirmed' | 'cancelled';
}
export declare class InsufficientStockError extends Error {
    constructor(itemId: string, requested: number, available: number);
}

// ---- domain/services.d.ts ----
import { Item, ReservationEntity } from './entities.js';
import { Reservation } from './contracts.js';
export interface InventoryService {
    checkAvailability(itemId: string, quantity: number): Promise<boolean>;
    createReservation(reservation: Reservation): Promise<ReservationEntity>;
    getItem(itemId: string): Promise<Item | null>;
}
export declare class InventoryServiceImpl implements InventoryService {
    private _db;
    constructor(_db: any);
    checkAvailability(itemId: string, quantity: number): Promise<boolean>;
    createReservation(reservation: Reservation): Promise<ReservationEntity>;
    getItem(_itemId: string): Promise<Item | null>;
}

// ---- health/health-endpoint.d.ts ----
/**
 * Health Check Endpoint for ae-framework
 * Phase 1.4: Docker production optimization health checks
 */
import { FastifyInstance } from 'fastify';
export interface HealthStatus {
    status: 'healthy' | 'unhealthy' | 'degraded';
    timestamp: string;
    uptime: number;
    version: string;
    environment: string;
    checks: {
        memory: {
            status: 'ok' | 'warning' | 'critical';
            used: number;
            total: number;
            percentage: number;
        };
        system: {
            status: 'ok' | 'error';
            nodeVersion: string;
            platform: string;
        };
        telemetry: {
            status: 'ok' | 'error';
            message: string;
        };
    };
}
export declare function registerHealthEndpoint(fastify: FastifyInstance): Promise<void>;

// ---- index.d.ts ----
export {};

// ---- infra/db.d.ts ----
import pg from 'pg';
export declare class Database {
    private pool;
    constructor(connectionString: string);
    query(text: string, params?: any[]): Promise<import("pg").QueryResult<any>>;
    transaction<T>(callback: (client: pg.PoolClient) => Promise<T>): Promise<T>;
    close(): Promise<void>;
}
export declare function initDatabase(db: Database): Promise<void>;

// ---- infra/telemetry.d.ts ----
import { NodeSDK } from '@opentelemetry/sdk-node';
export declare function initTelemetry(serviceName?: string): NodeSDK;

// ---- packages/spec-compiler/src/compiler.d.ts ----
import { AEIR, CompileOptions, SpecLintReport } from './types.js';
export declare class AESpecCompiler {
    /**
     * Compile AE-Spec markdown to AE-IR JSON
     */
    compile(options: CompileOptions): Promise<AEIR>;
    /**
     * Lint AE-IR for quality issues with strict schema validation
     */
    lint(ir: AEIR): Promise<SpecLintReport>;
    private parseMarkdownToIR;
    private extractSections;
    private parseGlossary;
    private parseDomain;
    private parseInvariants;
    private parseUsecases;
    private parseStateMachines;
    private parseAPI;
    private parseUI;
    private parseNFR;
    private validateStructure;
    private validateBusinessLogic;
    private validateConsistency;
    private validateCompleteness;
    private validateStrictSchema;
}

// ---- packages/spec-compiler/src/index.d.ts ----
/**
 * @ae-framework/spec-compiler
 *
 * AE-Spec to AE-IR compiler for single source of truth (SSOT)
 * Transforms natural language specifications into structured intermediate representation
 */
export { AESpecCompiler } from './compiler.js';
export type { AEIR, SpecLintReport, SpecLintIssue, CompileOptions, LintOptions, } from './types.js';
export interface AESpecCompilerInterface {
    compile(options: import('./types.js').CompileOptions): Promise<import('./types.js').AEIR>;
    lint(ir: import('./types.js').AEIR): Promise<import('./types.js').SpecLintReport>;
}
import { AESpecCompiler } from './compiler.js';
export default AESpecCompiler;

// ---- packages/spec-compiler/src/strict-schema.d.ts ----
/**
 * Strict AE-IR Schema with Zod Validation
 * Enhanced schema with comprehensive validation rules
 */
import { z } from 'zod';
export declare const StrictAEIRSchema: z.ZodEffects<z.ZodObject<{
    version: z.ZodString;
    metadata: z.ZodEffects<z.ZodObject<{
        name: z.ZodString;
        description: z.ZodOptional<z.ZodString>;
        version: z.ZodOptional<z.ZodString>;
        created: z.ZodString;
        updated: z.ZodString;
    }, "strict", z.ZodTypeAny, {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    }, {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    }>, {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    }, {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    }>;
    glossary: z.ZodEffects<z.ZodArray<z.ZodObject<{
        term: z.ZodString;
        definition: z.ZodString;
        aliases: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
    }, "strict", z.ZodTypeAny, {
        definition?: string;
        term?: string;
        aliases?: string[];
    }, {
        definition?: string;
        term?: string;
        aliases?: string[];
    }>, "many">, {
        definition?: string;
        term?: string;
        aliases?: string[];
    }[], {
        definition?: string;
        term?: string;
        aliases?: string[];
    }[]>;
    domain: z.ZodEffects<z.ZodArray<z.ZodEffects<z.ZodObject<{
        name: z.ZodString;
        description: z.ZodOptional<z.ZodString>;
        fields: z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            type: z.ZodEnum<["string", "number", "boolean", "date", "uuid", "email", "url", "json", "array", "object"]>;
            required: z.ZodDefault<z.ZodBoolean>;
            constraints: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
            description: z.ZodOptional<z.ZodString>;
        }, "strict", z.ZodTypeAny, {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }, {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }>, "many">;
        relationships: z.ZodOptional<z.ZodArray<z.ZodObject<{
            type: z.ZodEnum<["oneToOne", "oneToMany", "manyToMany"]>;
            target: z.ZodString;
            field: z.ZodOptional<z.ZodString>;
            description: z.ZodOptional<z.ZodString>;
        }, "strict", z.ZodTypeAny, {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }, {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }>, "many">>;
    }, "strict", z.ZodTypeAny, {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }, {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }>, {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }, {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }>, "many">, {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }[], {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }[]>;
    invariants: z.ZodArray<z.ZodObject<{
        id: z.ZodString;
        description: z.ZodString;
        expression: z.ZodString;
        entities: z.ZodArray<z.ZodString, "many">;
        severity: z.ZodEnum<["error", "warning"]>;
    }, "strict", z.ZodTypeAny, {
        id?: string;
        severity?: "error" | "warning";
        description?: string;
        entities?: string[];
        expression?: string;
    }, {
        id?: string;
        severity?: "error" | "warning";
        description?: string;
        entities?: string[];
        expression?: string;
    }>, "many">;
    usecases: z.ZodArray<z.ZodEffects<z.ZodObject<{
        name: z.ZodString;
        description: z.ZodOptional<z.ZodString>;
        actor: z.ZodString;
        preconditions: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
        postconditions: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
        steps: z.ZodArray<z.ZodObject<{
            step: z.ZodNumber;
            description: z.ZodString;
            type: z.ZodEnum<["action", "validation", "computation"]>;
        }, "strict", z.ZodTypeAny, {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }, {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }>, "many">;
    }, "strict", z.ZodTypeAny, {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }, {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }>, {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }, {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }>, "many">;
    statemachines: z.ZodOptional<z.ZodArray<z.ZodEffects<z.ZodObject<{
        name: z.ZodString;
        entity: z.ZodString;
        states: z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            description: z.ZodOptional<z.ZodString>;
            isInitial: z.ZodDefault<z.ZodBoolean>;
            isFinal: z.ZodDefault<z.ZodBoolean>;
        }, "strict", z.ZodTypeAny, {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }, {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }>, "many">;
        transitions: z.ZodArray<z.ZodObject<{
            from: z.ZodString;
            to: z.ZodString;
            trigger: z.ZodString;
            condition: z.ZodOptional<z.ZodString>;
            action: z.ZodOptional<z.ZodString>;
        }, "strict", z.ZodTypeAny, {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }, {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }>, "many">;
    }, "strict", z.ZodTypeAny, {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }, {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }>, {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }, {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }>, "many">>;
    api: z.ZodArray<z.ZodObject<{
        method: z.ZodEnum<["GET", "POST", "PUT", "PATCH", "DELETE"]>;
        path: z.ZodString;
        summary: z.ZodOptional<z.ZodString>;
        description: z.ZodOptional<z.ZodString>;
        parameters: z.ZodOptional<z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            in: z.ZodEnum<["path", "query", "header", "body"]>;
            type: z.ZodEnum<["string", "number", "boolean", "array", "object"]>;
            required: z.ZodDefault<z.ZodBoolean>;
            description: z.ZodOptional<z.ZodString>;
        }, "strict", z.ZodTypeAny, {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }, {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }>, "many">>;
        request: z.ZodOptional<z.ZodObject<{
            contentType: z.ZodString;
            schema: z.ZodOptional<z.ZodAny>;
        }, "strict", z.ZodTypeAny, {
            schema?: any;
            contentType?: string;
        }, {
            schema?: any;
            contentType?: string;
        }>>;
        response: z.ZodOptional<z.ZodObject<{
            statusCode: z.ZodNumber;
            contentType: z.ZodString;
            schema: z.ZodOptional<z.ZodAny>;
        }, "strict", z.ZodTypeAny, {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        }, {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        }>>;
        errors: z.ZodOptional<z.ZodArray<z.ZodObject<{
            statusCode: z.ZodNumber;
            description: z.ZodString;
        }, "strict", z.ZodTypeAny, {
            statusCode?: number;
            description?: string;
        }, {
            statusCode?: number;
            description?: string;
        }>, "many">>;
    }, "strict", z.ZodTypeAny, {
        path?: string;
        response?: {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        };
        summary?: string;
        request?: {
            schema?: any;
            contentType?: string;
        };
        method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
        errors?: {
            statusCode?: number;
            description?: string;
        }[];
        description?: string;
        parameters?: {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }[];
    }, {
        path?: string;
        response?: {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        };
        summary?: string;
        request?: {
            schema?: any;
            contentType?: string;
        };
        method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
        errors?: {
            statusCode?: number;
            description?: string;
        }[];
        description?: string;
        parameters?: {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }[];
    }>, "many">;
    ui: z.ZodOptional<z.ZodObject<{
        viewModels: z.ZodOptional<z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            entity: z.ZodString;
            fields: z.ZodArray<z.ZodObject<{
                name: z.ZodString;
                type: z.ZodEnum<["display", "input", "action"]>;
                component: z.ZodOptional<z.ZodString>;
                validation: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
            }, "strict", z.ZodTypeAny, {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }, {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }>, "many">;
        }, "strict", z.ZodTypeAny, {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }, {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }>, "many">>;
        pages: z.ZodOptional<z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            path: z.ZodString;
            viewModel: z.ZodString;
            layout: z.ZodOptional<z.ZodString>;
        }, "strict", z.ZodTypeAny, {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }, {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }>, "many">>;
        workflows: z.ZodOptional<z.ZodArray<z.ZodObject<{
            name: z.ZodString;
            steps: z.ZodArray<z.ZodObject<{
                page: z.ZodString;
                condition: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                condition?: string;
                page?: string;
            }, {
                condition?: string;
                page?: string;
            }>, "many">;
        }, "strict", z.ZodTypeAny, {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }, {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }>, "many">>;
    }, "strict", z.ZodTypeAny, {
        viewModels?: {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }[];
        pages?: {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }[];
        workflows?: {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }[];
    }, {
        viewModels?: {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }[];
        pages?: {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }[];
        workflows?: {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }[];
    }>>;
    nfr: z.ZodOptional<z.ZodObject<{
        performance: z.ZodOptional<z.ZodObject<{
            responseTime: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodNumber>>;
            throughput: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodNumber>>;
            concurrency: z.ZodOptional<z.ZodNumber>;
        }, "strict", z.ZodTypeAny, {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        }, {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        }>>;
        security: z.ZodOptional<z.ZodObject<{
            authentication: z.ZodOptional<z.ZodArray<z.ZodEnum<["oauth2", "jwt", "basic", "apikey", "saml"]>, "many">>;
            authorization: z.ZodOptional<z.ZodArray<z.ZodEnum<["rbac", "abac", "acl", "scope-based"]>, "many">>;
            encryption: z.ZodOptional<z.ZodArray<z.ZodEnum<["tls", "aes", "rsa", "end-to-end"]>, "many">>;
        }, "strict", z.ZodTypeAny, {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        }, {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        }>>;
        reliability: z.ZodOptional<z.ZodObject<{
            availability: z.ZodOptional<z.ZodNumber>;
            recovery: z.ZodOptional<z.ZodString>;
        }, "strict", z.ZodTypeAny, {
            availability?: number;
            recovery?: string;
        }, {
            availability?: number;
            recovery?: string;
        }>>;
        scalability: z.ZodOptional<z.ZodObject<{
            users: z.ZodOptional<z.ZodNumber>;
            dataSize: z.ZodOptional<z.ZodString>;
        }, "strict", z.ZodTypeAny, {
            dataSize?: string;
            users?: number;
        }, {
            dataSize?: string;
            users?: number;
        }>>;
    }, "strict", z.ZodTypeAny, {
        performance?: {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        };
        security?: {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        };
        scalability?: {
            dataSize?: string;
            users?: number;
        };
        reliability?: {
            availability?: number;
            recovery?: string;
        };
    }, {
        performance?: {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        };
        security?: {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        };
        scalability?: {
            dataSize?: string;
            users?: number;
        };
        reliability?: {
            availability?: number;
            recovery?: string;
        };
    }>>;
}, "strict", z.ZodTypeAny, {
    version?: string;
    invariants?: {
        id?: string;
        severity?: "error" | "warning";
        description?: string;
        entities?: string[];
        expression?: string;
    }[];
    domain?: {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }[];
    api?: {
        path?: string;
        response?: {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        };
        summary?: string;
        request?: {
            schema?: any;
            contentType?: string;
        };
        method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
        errors?: {
            statusCode?: number;
            description?: string;
        }[];
        description?: string;
        parameters?: {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }[];
    }[];
    ui?: {
        viewModels?: {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }[];
        pages?: {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }[];
        workflows?: {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }[];
    };
    metadata?: {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    };
    glossary?: {
        definition?: string;
        term?: string;
        aliases?: string[];
    }[];
    usecases?: {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }[];
    statemachines?: {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }[];
    nfr?: {
        performance?: {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        };
        security?: {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        };
        scalability?: {
            dataSize?: string;
            users?: number;
        };
        reliability?: {
            availability?: number;
            recovery?: string;
        };
    };
}, {
    version?: string;
    invariants?: {
        id?: string;
        severity?: "error" | "warning";
        description?: string;
        entities?: string[];
        expression?: string;
    }[];
    domain?: {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }[];
    api?: {
        path?: string;
        response?: {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        };
        summary?: string;
        request?: {
            schema?: any;
            contentType?: string;
        };
        method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
        errors?: {
            statusCode?: number;
            description?: string;
        }[];
        description?: string;
        parameters?: {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }[];
    }[];
    ui?: {
        viewModels?: {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }[];
        pages?: {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }[];
        workflows?: {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }[];
    };
    metadata?: {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    };
    glossary?: {
        definition?: string;
        term?: string;
        aliases?: string[];
    }[];
    usecases?: {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }[];
    statemachines?: {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }[];
    nfr?: {
        performance?: {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        };
        security?: {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        };
        scalability?: {
            dataSize?: string;
            users?: number;
        };
        reliability?: {
            availability?: number;
            recovery?: string;
        };
    };
}>, {
    version?: string;
    invariants?: {
        id?: string;
        severity?: "error" | "warning";
        description?: string;
        entities?: string[];
        expression?: string;
    }[];
    domain?: {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }[];
    api?: {
        path?: string;
        response?: {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        };
        summary?: string;
        request?: {
            schema?: any;
            contentType?: string;
        };
        method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
        errors?: {
            statusCode?: number;
            description?: string;
        }[];
        description?: string;
        parameters?: {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }[];
    }[];
    ui?: {
        viewModels?: {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }[];
        pages?: {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }[];
        workflows?: {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }[];
    };
    metadata?: {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    };
    glossary?: {
        definition?: string;
        term?: string;
        aliases?: string[];
    }[];
    usecases?: {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }[];
    statemachines?: {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }[];
    nfr?: {
        performance?: {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        };
        security?: {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        };
        scalability?: {
            dataSize?: string;
            users?: number;
        };
        reliability?: {
            availability?: number;
            recovery?: string;
        };
    };
}, {
    version?: string;
    invariants?: {
        id?: string;
        severity?: "error" | "warning";
        description?: string;
        entities?: string[];
        expression?: string;
    }[];
    domain?: {
        name?: string;
        description?: string;
        relationships?: {
            type?: "oneToOne" | "oneToMany" | "manyToMany";
            description?: string;
            field?: string;
            target?: string;
        }[];
        fields?: {
            type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
            name?: string;
            constraints?: string[];
            description?: string;
            required?: boolean;
        }[];
    }[];
    api?: {
        path?: string;
        response?: {
            statusCode?: number;
            schema?: any;
            contentType?: string;
        };
        summary?: string;
        request?: {
            schema?: any;
            contentType?: string;
        };
        method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
        errors?: {
            statusCode?: number;
            description?: string;
        }[];
        description?: string;
        parameters?: {
            type?: "string" | "number" | "boolean" | "object" | "array";
            name?: string;
            description?: string;
            in?: "path" | "query" | "body" | "header";
            required?: boolean;
        }[];
    }[];
    ui?: {
        viewModels?: {
            name?: string;
            entity?: string;
            fields?: {
                validation?: string[];
                type?: "input" | "display" | "action";
                name?: string;
                component?: string;
            }[];
        }[];
        pages?: {
            path?: string;
            name?: string;
            viewModel?: string;
            layout?: string;
        }[];
        workflows?: {
            name?: string;
            steps?: {
                condition?: string;
                page?: string;
            }[];
        }[];
    };
    metadata?: {
        name?: string;
        version?: string;
        created?: string;
        description?: string;
        updated?: string;
    };
    glossary?: {
        definition?: string;
        term?: string;
        aliases?: string[];
    }[];
    usecases?: {
        name?: string;
        description?: string;
        actor?: string;
        preconditions?: string[];
        postconditions?: string[];
        steps?: {
            type?: "validation" | "action" | "computation";
            step?: number;
            description?: string;
        }[];
    }[];
    statemachines?: {
        name?: string;
        states?: {
            name?: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }[];
        transitions?: {
            from?: string;
            condition?: string;
            action?: string;
            to?: string;
            trigger?: string;
        }[];
        entity?: string;
    }[];
    nfr?: {
        performance?: {
            throughput?: Record<string, number>;
            concurrency?: number;
            responseTime?: Record<string, number>;
        };
        security?: {
            authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
            authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
            encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
        };
        scalability?: {
            dataSize?: string;
            users?: number;
        };
        reliability?: {
            availability?: number;
            recovery?: string;
        };
    };
}>;
export type StrictAEIR = z.infer<typeof StrictAEIRSchema>;
export declare function validateAEIR(data: unknown): {
    success: true;
    data: StrictAEIR;
} | {
    success: false;
    errors: z.ZodError;
};
export declare function createAEIRValidator(): {
    validate: typeof validateAEIR;
    schema: z.ZodEffects<z.ZodObject<{
        version: z.ZodString;
        metadata: z.ZodEffects<z.ZodObject<{
            name: z.ZodString;
            description: z.ZodOptional<z.ZodString>;
            version: z.ZodOptional<z.ZodString>;
            created: z.ZodString;
            updated: z.ZodString;
        }, "strict", z.ZodTypeAny, {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        }, {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        }>, {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        }, {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        }>;
        glossary: z.ZodEffects<z.ZodArray<z.ZodObject<{
            term: z.ZodString;
            definition: z.ZodString;
            aliases: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
        }, "strict", z.ZodTypeAny, {
            definition?: string;
            term?: string;
            aliases?: string[];
        }, {
            definition?: string;
            term?: string;
            aliases?: string[];
        }>, "many">, {
            definition?: string;
            term?: string;
            aliases?: string[];
        }[], {
            definition?: string;
            term?: string;
            aliases?: string[];
        }[]>;
        domain: z.ZodEffects<z.ZodArray<z.ZodEffects<z.ZodObject<{
            name: z.ZodString;
            description: z.ZodOptional<z.ZodString>;
            fields: z.ZodArray<z.ZodObject<{
                name: z.ZodString;
                type: z.ZodEnum<["string", "number", "boolean", "date", "uuid", "email", "url", "json", "array", "object"]>;
                required: z.ZodDefault<z.ZodBoolean>;
                constraints: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
                description: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }, {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }>, "many">;
            relationships: z.ZodOptional<z.ZodArray<z.ZodObject<{
                type: z.ZodEnum<["oneToOne", "oneToMany", "manyToMany"]>;
                target: z.ZodString;
                field: z.ZodOptional<z.ZodString>;
                description: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }, {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }>, "many">>;
        }, "strict", z.ZodTypeAny, {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }, {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }>, {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }, {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }>, "many">, {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }[], {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }[]>;
        invariants: z.ZodArray<z.ZodObject<{
            id: z.ZodString;
            description: z.ZodString;
            expression: z.ZodString;
            entities: z.ZodArray<z.ZodString, "many">;
            severity: z.ZodEnum<["error", "warning"]>;
        }, "strict", z.ZodTypeAny, {
            id?: string;
            severity?: "error" | "warning";
            description?: string;
            entities?: string[];
            expression?: string;
        }, {
            id?: string;
            severity?: "error" | "warning";
            description?: string;
            entities?: string[];
            expression?: string;
        }>, "many">;
        usecases: z.ZodArray<z.ZodEffects<z.ZodObject<{
            name: z.ZodString;
            description: z.ZodOptional<z.ZodString>;
            actor: z.ZodString;
            preconditions: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
            postconditions: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
            steps: z.ZodArray<z.ZodObject<{
                step: z.ZodNumber;
                description: z.ZodString;
                type: z.ZodEnum<["action", "validation", "computation"]>;
            }, "strict", z.ZodTypeAny, {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }, {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }>, "many">;
        }, "strict", z.ZodTypeAny, {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }, {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }>, {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }, {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }>, "many">;
        statemachines: z.ZodOptional<z.ZodArray<z.ZodEffects<z.ZodObject<{
            name: z.ZodString;
            entity: z.ZodString;
            states: z.ZodArray<z.ZodObject<{
                name: z.ZodString;
                description: z.ZodOptional<z.ZodString>;
                isInitial: z.ZodDefault<z.ZodBoolean>;
                isFinal: z.ZodDefault<z.ZodBoolean>;
            }, "strict", z.ZodTypeAny, {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }, {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }>, "many">;
            transitions: z.ZodArray<z.ZodObject<{
                from: z.ZodString;
                to: z.ZodString;
                trigger: z.ZodString;
                condition: z.ZodOptional<z.ZodString>;
                action: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }, {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }>, "many">;
        }, "strict", z.ZodTypeAny, {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }, {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }>, {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }, {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }>, "many">>;
        api: z.ZodArray<z.ZodObject<{
            method: z.ZodEnum<["GET", "POST", "PUT", "PATCH", "DELETE"]>;
            path: z.ZodString;
            summary: z.ZodOptional<z.ZodString>;
            description: z.ZodOptional<z.ZodString>;
            parameters: z.ZodOptional<z.ZodArray<z.ZodObject<{
                name: z.ZodString;
                in: z.ZodEnum<["path", "query", "header", "body"]>;
                type: z.ZodEnum<["string", "number", "boolean", "array", "object"]>;
                required: z.ZodDefault<z.ZodBoolean>;
                description: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }, {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }>, "many">>;
            request: z.ZodOptional<z.ZodObject<{
                contentType: z.ZodString;
                schema: z.ZodOptional<z.ZodAny>;
            }, "strict", z.ZodTypeAny, {
                schema?: any;
                contentType?: string;
            }, {
                schema?: any;
                contentType?: string;
            }>>;
            response: z.ZodOptional<z.ZodObject<{
                statusCode: z.ZodNumber;
                contentType: z.ZodString;
                schema: z.ZodOptional<z.ZodAny>;
            }, "strict", z.ZodTypeAny, {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            }, {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            }>>;
            errors: z.ZodOptional<z.ZodArray<z.ZodObject<{
                statusCode: z.ZodNumber;
                description: z.ZodString;
            }, "strict", z.ZodTypeAny, {
                statusCode?: number;
                description?: string;
            }, {
                statusCode?: number;
                description?: string;
            }>, "many">>;
        }, "strict", z.ZodTypeAny, {
            path?: string;
            response?: {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            };
            summary?: string;
            request?: {
                schema?: any;
                contentType?: string;
            };
            method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
            errors?: {
                statusCode?: number;
                description?: string;
            }[];
            description?: string;
            parameters?: {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }[];
        }, {
            path?: string;
            response?: {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            };
            summary?: string;
            request?: {
                schema?: any;
                contentType?: string;
            };
            method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
            errors?: {
                statusCode?: number;
                description?: string;
            }[];
            description?: string;
            parameters?: {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }[];
        }>, "many">;
        ui: z.ZodOptional<z.ZodObject<{
            viewModels: z.ZodOptional<z.ZodArray<z.ZodObject<{
                name: z.ZodString;
                entity: z.ZodString;
                fields: z.ZodArray<z.ZodObject<{
                    name: z.ZodString;
                    type: z.ZodEnum<["display", "input", "action"]>;
                    component: z.ZodOptional<z.ZodString>;
                    validation: z.ZodOptional<z.ZodArray<z.ZodString, "many">>;
                }, "strict", z.ZodTypeAny, {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }, {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }>, "many">;
            }, "strict", z.ZodTypeAny, {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }, {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }>, "many">>;
            pages: z.ZodOptional<z.ZodArray<z.ZodObject<{
                name: z.ZodString;
                path: z.ZodString;
                viewModel: z.ZodString;
                layout: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }, {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }>, "many">>;
            workflows: z.ZodOptional<z.ZodArray<z.ZodObject<{
                name: z.ZodString;
                steps: z.ZodArray<z.ZodObject<{
                    page: z.ZodString;
                    condition: z.ZodOptional<z.ZodString>;
                }, "strict", z.ZodTypeAny, {
                    condition?: string;
                    page?: string;
                }, {
                    condition?: string;
                    page?: string;
                }>, "many">;
            }, "strict", z.ZodTypeAny, {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }, {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }>, "many">>;
        }, "strict", z.ZodTypeAny, {
            viewModels?: {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }[];
            pages?: {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }[];
            workflows?: {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }[];
        }, {
            viewModels?: {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }[];
            pages?: {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }[];
            workflows?: {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }[];
        }>>;
        nfr: z.ZodOptional<z.ZodObject<{
            performance: z.ZodOptional<z.ZodObject<{
                responseTime: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodNumber>>;
                throughput: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodNumber>>;
                concurrency: z.ZodOptional<z.ZodNumber>;
            }, "strict", z.ZodTypeAny, {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            }, {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            }>>;
            security: z.ZodOptional<z.ZodObject<{
                authentication: z.ZodOptional<z.ZodArray<z.ZodEnum<["oauth2", "jwt", "basic", "apikey", "saml"]>, "many">>;
                authorization: z.ZodOptional<z.ZodArray<z.ZodEnum<["rbac", "abac", "acl", "scope-based"]>, "many">>;
                encryption: z.ZodOptional<z.ZodArray<z.ZodEnum<["tls", "aes", "rsa", "end-to-end"]>, "many">>;
            }, "strict", z.ZodTypeAny, {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            }, {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            }>>;
            reliability: z.ZodOptional<z.ZodObject<{
                availability: z.ZodOptional<z.ZodNumber>;
                recovery: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                availability?: number;
                recovery?: string;
            }, {
                availability?: number;
                recovery?: string;
            }>>;
            scalability: z.ZodOptional<z.ZodObject<{
                users: z.ZodOptional<z.ZodNumber>;
                dataSize: z.ZodOptional<z.ZodString>;
            }, "strict", z.ZodTypeAny, {
                dataSize?: string;
                users?: number;
            }, {
                dataSize?: string;
                users?: number;
            }>>;
        }, "strict", z.ZodTypeAny, {
            performance?: {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            };
            security?: {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            };
            scalability?: {
                dataSize?: string;
                users?: number;
            };
            reliability?: {
                availability?: number;
                recovery?: string;
            };
        }, {
            performance?: {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            };
            security?: {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            };
            scalability?: {
                dataSize?: string;
                users?: number;
            };
            reliability?: {
                availability?: number;
                recovery?: string;
            };
        }>>;
    }, "strict", z.ZodTypeAny, {
        version?: string;
        invariants?: {
            id?: string;
            severity?: "error" | "warning";
            description?: string;
            entities?: string[];
            expression?: string;
        }[];
        domain?: {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }[];
        api?: {
            path?: string;
            response?: {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            };
            summary?: string;
            request?: {
                schema?: any;
                contentType?: string;
            };
            method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
            errors?: {
                statusCode?: number;
                description?: string;
            }[];
            description?: string;
            parameters?: {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }[];
        }[];
        ui?: {
            viewModels?: {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }[];
            pages?: {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }[];
            workflows?: {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }[];
        };
        metadata?: {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        };
        glossary?: {
            definition?: string;
            term?: string;
            aliases?: string[];
        }[];
        usecases?: {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }[];
        statemachines?: {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }[];
        nfr?: {
            performance?: {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            };
            security?: {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            };
            scalability?: {
                dataSize?: string;
                users?: number;
            };
            reliability?: {
                availability?: number;
                recovery?: string;
            };
        };
    }, {
        version?: string;
        invariants?: {
            id?: string;
            severity?: "error" | "warning";
            description?: string;
            entities?: string[];
            expression?: string;
        }[];
        domain?: {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }[];
        api?: {
            path?: string;
            response?: {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            };
            summary?: string;
            request?: {
                schema?: any;
                contentType?: string;
            };
            method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
            errors?: {
                statusCode?: number;
                description?: string;
            }[];
            description?: string;
            parameters?: {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }[];
        }[];
        ui?: {
            viewModels?: {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }[];
            pages?: {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }[];
            workflows?: {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }[];
        };
        metadata?: {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        };
        glossary?: {
            definition?: string;
            term?: string;
            aliases?: string[];
        }[];
        usecases?: {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }[];
        statemachines?: {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }[];
        nfr?: {
            performance?: {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            };
            security?: {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            };
            scalability?: {
                dataSize?: string;
                users?: number;
            };
            reliability?: {
                availability?: number;
                recovery?: string;
            };
        };
    }>, {
        version?: string;
        invariants?: {
            id?: string;
            severity?: "error" | "warning";
            description?: string;
            entities?: string[];
            expression?: string;
        }[];
        domain?: {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }[];
        api?: {
            path?: string;
            response?: {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            };
            summary?: string;
            request?: {
                schema?: any;
                contentType?: string;
            };
            method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
            errors?: {
                statusCode?: number;
                description?: string;
            }[];
            description?: string;
            parameters?: {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }[];
        }[];
        ui?: {
            viewModels?: {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }[];
            pages?: {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }[];
            workflows?: {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }[];
        };
        metadata?: {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        };
        glossary?: {
            definition?: string;
            term?: string;
            aliases?: string[];
        }[];
        usecases?: {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }[];
        statemachines?: {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }[];
        nfr?: {
            performance?: {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            };
            security?: {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            };
            scalability?: {
                dataSize?: string;
                users?: number;
            };
            reliability?: {
                availability?: number;
                recovery?: string;
            };
        };
    }, {
        version?: string;
        invariants?: {
            id?: string;
            severity?: "error" | "warning";
            description?: string;
            entities?: string[];
            expression?: string;
        }[];
        domain?: {
            name?: string;
            description?: string;
            relationships?: {
                type?: "oneToOne" | "oneToMany" | "manyToMany";
                description?: string;
                field?: string;
                target?: string;
            }[];
            fields?: {
                type?: "string" | "number" | "boolean" | "object" | "date" | "array" | "url" | "json" | "email" | "uuid";
                name?: string;
                constraints?: string[];
                description?: string;
                required?: boolean;
            }[];
        }[];
        api?: {
            path?: string;
            response?: {
                statusCode?: number;
                schema?: any;
                contentType?: string;
            };
            summary?: string;
            request?: {
                schema?: any;
                contentType?: string;
            };
            method?: "DELETE" | "GET" | "PATCH" | "POST" | "PUT";
            errors?: {
                statusCode?: number;
                description?: string;
            }[];
            description?: string;
            parameters?: {
                type?: "string" | "number" | "boolean" | "object" | "array";
                name?: string;
                description?: string;
                in?: "path" | "query" | "body" | "header";
                required?: boolean;
            }[];
        }[];
        ui?: {
            viewModels?: {
                name?: string;
                entity?: string;
                fields?: {
                    validation?: string[];
                    type?: "input" | "display" | "action";
                    name?: string;
                    component?: string;
                }[];
            }[];
            pages?: {
                path?: string;
                name?: string;
                viewModel?: string;
                layout?: string;
            }[];
            workflows?: {
                name?: string;
                steps?: {
                    condition?: string;
                    page?: string;
                }[];
            }[];
        };
        metadata?: {
            name?: string;
            version?: string;
            created?: string;
            description?: string;
            updated?: string;
        };
        glossary?: {
            definition?: string;
            term?: string;
            aliases?: string[];
        }[];
        usecases?: {
            name?: string;
            description?: string;
            actor?: string;
            preconditions?: string[];
            postconditions?: string[];
            steps?: {
                type?: "validation" | "action" | "computation";
                step?: number;
                description?: string;
            }[];
        }[];
        statemachines?: {
            name?: string;
            states?: {
                name?: string;
                description?: string;
                isInitial?: boolean;
                isFinal?: boolean;
            }[];
            transitions?: {
                from?: string;
                condition?: string;
                action?: string;
                to?: string;
                trigger?: string;
            }[];
            entity?: string;
        }[];
        nfr?: {
            performance?: {
                throughput?: Record<string, number>;
                concurrency?: number;
                responseTime?: Record<string, number>;
            };
            security?: {
                authorization?: ("rbac" | "abac" | "acl" | "scope-based")[];
                authentication?: ("jwt" | "basic" | "oauth2" | "apikey" | "saml")[];
                encryption?: ("tls" | "aes" | "rsa" | "end-to-end")[];
            };
            scalability?: {
                dataSize?: string;
                users?: number;
            };
            reliability?: {
                availability?: number;
                recovery?: string;
            };
        };
    }>;
    validatePartial: (data: Partial<StrictAEIR>) => {
        success: boolean;
        data: StrictAEIR;
        error?: undefined;
    } | {
        success: boolean;
        error: {
            errors: {
                message: string;
            }[];
        };
        data?: undefined;
    };
    getReadableErrors: (error: z.ZodError) => {
        path: string;
        message: string;
        code: "invalid_literal" | "invalid_type" | "invalid_enum_value" | "invalid_union" | "unrecognized_keys" | "invalid_union_discriminator" | "invalid_arguments" | "invalid_return_type" | "invalid_string" | "not_multiple_of" | "custom" | "invalid_intersection_types" | "invalid_date" | "not_finite" | "too_big" | "too_small";
    }[];
};

// ---- packages/spec-compiler/src/types.d.ts ----
/**
 * AE-IR (AI-Enhanced Intermediate Representation) Types
 * Single Source of Truth for ae-framework specifications
 */
export interface AEIR {
    /** Version of the AE-IR format */
    version: string;
    /** Project metadata */
    metadata: {
        name: string;
        description?: string;
        version?: string;
        created: string;
        updated: string;
    };
    /** Business glossary and terminology */
    glossary: Array<{
        term: string;
        definition: string;
        aliases?: string[];
    }>;
    /** Domain entities and their structure */
    domain: Array<{
        name: string;
        description?: string;
        fields: Array<{
            name: string;
            type: string;
            required?: boolean;
            constraints?: string[];
            description?: string;
        }>;
        relationships?: Array<{
            type: 'oneToOne' | 'oneToMany' | 'manyToMany';
            target: string;
            field?: string;
            description?: string;
        }>;
    }>;
    /** Business invariants and rules */
    invariants: Array<{
        id: string;
        description: string;
        expression: string;
        entities: string[];
        severity: 'error' | 'warning';
    }>;
    /** Use cases and business processes */
    usecases: Array<{
        name: string;
        description?: string;
        actor: string;
        preconditions?: string[];
        postconditions?: string[];
        steps: Array<{
            step: number;
            description: string;
            type: 'action' | 'validation' | 'computation';
        }>;
    }>;
    /** State machines (optional) */
    statemachines?: Array<{
        name: string;
        entity: string;
        states: Array<{
            name: string;
            description?: string;
            isInitial?: boolean;
            isFinal?: boolean;
        }>;
        transitions: Array<{
            from: string;
            to: string;
            trigger: string;
            condition?: string;
            action?: string;
        }>;
    }>;
    /** API specifications */
    api: Array<{
        method: 'GET' | 'POST' | 'PUT' | 'PATCH' | 'DELETE';
        path: string;
        summary?: string;
        description?: string;
        parameters?: Array<{
            name: string;
            in: 'path' | 'query' | 'header' | 'body';
            type: string;
            required?: boolean;
            description?: string;
        }>;
        request?: {
            contentType: string;
            schema?: any;
        };
        response?: {
            statusCode: number;
            contentType: string;
            schema?: any;
        };
        errors?: Array<{
            statusCode: number;
            description: string;
        }>;
    }>;
    /** UI/UX specifications */
    ui?: {
        viewModels?: Array<{
            name: string;
            entity: string;
            fields: Array<{
                name: string;
                type: 'display' | 'input' | 'action';
                component?: string;
                validation?: string[];
            }>;
        }>;
        pages?: Array<{
            name: string;
            path: string;
            viewModel: string;
            layout?: string;
        }>;
        workflows?: Array<{
            name: string;
            steps: Array<{
                page: string;
                condition?: string;
            }>;
        }>;
    };
    /** Non-functional requirements */
    nfr?: {
        performance?: {
            responseTime?: Record<string, number>;
            throughput?: Record<string, number>;
            concurrency?: number;
        };
        security?: {
            authentication?: string[];
            authorization?: string[];
            encryption?: string[];
        };
        reliability?: {
            availability?: number;
            recovery?: string;
        };
        scalability?: {
            users?: number;
            dataSize?: string;
        };
    };
}
export interface SpecLintIssue {
    id: string;
    severity: 'error' | 'warn' | 'info';
    message: string;
    location?: {
        section?: string;
        line?: number;
        column?: number;
    };
    suggestion?: string;
}
export interface SpecLintReport {
    passed: boolean;
    issues: SpecLintIssue[];
    summary: {
        errors: number;
        warnings: number;
        infos: number;
    };
}
export interface CompileOptions {
    /** Input markdown file path */
    inputPath: string;
    /** Output JSON file path (optional) */
    outputPath?: string;
    /** Validation options */
    validate?: boolean;
    /** Include source locations in output */
    sourceMap?: boolean;
}
export interface LintOptions {
    /** Maximum allowed errors */
    maxErrors?: number;
    /** Maximum allowed warnings */
    maxWarnings?: number;
    /** Rules to ignore */
    ignoreRules?: string[];
    /** Custom rule configurations */
    ruleConfigs?: Record<string, any>;
}

// ---- providers/index.d.ts ----
export interface LLM {
    name: string;
    complete(input: {
        system?: string;
        prompt: string;
        temperature?: number;
    }): Promise<string>;
}
export declare function loadLLM(): Promise<LLM>;

// ---- providers/llm-anthropic.d.ts ----
import type { LLM } from './index.js';
declare const AnthropicProvider: LLM;
export default AnthropicProvider;

// ---- providers/llm-echo.d.ts ----
import type { LLM } from './index.js';
declare const Echo: LLM;
export default Echo;

// ---- providers/llm-gemini.d.ts ----
import type { LLM } from './index.js';
declare const GeminiProvider: LLM;
export default GeminiProvider;

// ---- providers/llm-openai.d.ts ----
import type { LLM } from './index.js';
declare const OpenAIProvider: LLM;
export default OpenAIProvider;

// ---- providers/recorder.d.ts ----
import type { LLM } from './index.js';
export declare function withRecorder(base: LLM, opts?: {
    dir?: string;
    replay?: boolean;
}): LLM;

// ---- schemas/llm.d.ts ----
import { z } from 'zod';
export declare const OpenAIChat: z.ZodObject<{
    choices: z.ZodArray<z.ZodObject<{
        message: z.ZodObject<{
            content: z.ZodDefault<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            content?: string;
        }, {
            content?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        message?: {
            content?: string;
        };
    }, {
        message?: {
            content?: string;
        };
    }>, "atleastone">;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    choices: z.ZodArray<z.ZodObject<{
        message: z.ZodObject<{
            content: z.ZodDefault<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            content?: string;
        }, {
            content?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        message?: {
            content?: string;
        };
    }, {
        message?: {
            content?: string;
        };
    }>, "atleastone">;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    choices: z.ZodArray<z.ZodObject<{
        message: z.ZodObject<{
            content: z.ZodDefault<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            content?: string;
        }, {
            content?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        message?: {
            content?: string;
        };
    }, {
        message?: {
            content?: string;
        };
    }>, "atleastone">;
}, z.ZodTypeAny, "passthrough">>;
export declare const AnthropicMsg: z.ZodObject<{
    content: z.ZodAny;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    content: z.ZodAny;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    content: z.ZodAny;
}, z.ZodTypeAny, "passthrough">>;
export declare const GeminiResp: z.ZodObject<{
    response: z.ZodAny;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    response: z.ZodAny;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    response: z.ZodAny;
}, z.ZodTypeAny, "passthrough">>;
export declare const BenchmarkResult: z.ZodObject<{
    summary: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        hz: z.ZodNumber;
        meanMs: z.ZodNumber;
        sdMs: z.ZodOptional<z.ZodNumber>;
        samples: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        name?: string;
        hz?: number;
        meanMs?: number;
        sdMs?: number;
        samples?: number;
    }, {
        name?: string;
        hz?: number;
        meanMs?: number;
        sdMs?: number;
        samples?: number;
    }>, "many">;
    date: z.ZodOptional<z.ZodString>;
    env: z.ZodOptional<z.ZodAny>;
    config: z.ZodOptional<z.ZodAny>;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    summary: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        hz: z.ZodNumber;
        meanMs: z.ZodNumber;
        sdMs: z.ZodOptional<z.ZodNumber>;
        samples: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        name?: string;
        hz?: number;
        meanMs?: number;
        sdMs?: number;
        samples?: number;
    }, {
        name?: string;
        hz?: number;
        meanMs?: number;
        sdMs?: number;
        samples?: number;
    }>, "many">;
    date: z.ZodOptional<z.ZodString>;
    env: z.ZodOptional<z.ZodAny>;
    config: z.ZodOptional<z.ZodAny>;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    summary: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        hz: z.ZodNumber;
        meanMs: z.ZodNumber;
        sdMs: z.ZodOptional<z.ZodNumber>;
        samples: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        name?: string;
        hz?: number;
        meanMs?: number;
        sdMs?: number;
        samples?: number;
    }, {
        name?: string;
        hz?: number;
        meanMs?: number;
        sdMs?: number;
        samples?: number;
    }>, "many">;
    date: z.ZodOptional<z.ZodString>;
    env: z.ZodOptional<z.ZodAny>;
    config: z.ZodOptional<z.ZodAny>;
}, z.ZodTypeAny, "passthrough">>;

// ---- src/agents/adapters/intent-agent-adapter.d.ts ----
/**
 * Intent Agent Adapter
 * Adapts the existing IntentAgent to the standardized AE Framework interface
 */
import { StandardAEAgent, ProcessingContext, PhaseResult, ValidationResult, AgentCapabilities, IntentInput, IntentOutput } from '../interfaces/standard-interfaces.js';
/**
 * Adapter that wraps IntentAgent to conform to standard interface
 */
export declare class IntentAgentAdapter implements StandardAEAgent<IntentInput, IntentOutput> {
    private intentAgent;
    readonly agentName = "IntentAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "intent";
    constructor();
    /**
     * Standardized processing method
     */
    process(input: IntentInput, context?: ProcessingContext): Promise<PhaseResult<IntentOutput>>;
    /**
     * Validate input according to standard interface
     */
    validateInput(input: IntentInput): ValidationResult;
    /**
     * Get agent capabilities
     */
    getCapabilities(): AgentCapabilities;
    private extractBusinessModel;
    private extractKeyProcesses;
    private extractSuccessMetrics;
    private extractAssumptions;
    private calculateConfidenceScore;
    private generateWarnings;
    private generateInputHash;
}

// ---- src/agents/adapters/task-adapters.d.ts ----
/**
 * Task Agent Adapters
 * Adapts existing task adapters to standardized AE Framework interface
 */
import { StandardAEAgent, ProcessingContext, PhaseResult, ValidationResult, AgentCapabilities, RequirementsInput, RequirementsOutput, UserStoriesInput, UserStoriesOutput, ValidationInput, ValidationOutput, DomainModelingInput, DomainModelingOutput } from '../interfaces/standard-interfaces.js';
/**
 * Natural Language Requirements Adapter
 */
export declare class RequirementsAgentAdapter implements StandardAEAgent<RequirementsInput, RequirementsOutput> {
    private nlpAgent;
    readonly agentName = "RequirementsAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "requirements";
    constructor();
    process(input: RequirementsInput, context?: ProcessingContext): Promise<PhaseResult<RequirementsOutput>>;
    validateInput(input: RequirementsInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildNaturalLanguageInput;
    private extractStructuredRequirements;
    private categorizeRequirement;
    private calculateConfidence;
    private generateWarnings;
    private buildErrorResult;
}
/**
 * User Stories Agent Adapter
 */
export declare class UserStoriesAgentAdapter implements StandardAEAgent<UserStoriesInput, UserStoriesOutput> {
    private storiesAgent;
    readonly agentName = "UserStoriesAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "user-stories";
    constructor();
    process(input: UserStoriesInput, context?: ProcessingContext): Promise<PhaseResult<UserStoriesOutput>>;
    validateInput(input: UserStoriesInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildStoriesInput;
    private transformStories;
    private extractAcceptanceCriteria;
    private generateTestScenarios;
    private buildTraceabilityMatrix;
    private buildErrorResult;
}
/**
 * Validation Agent Adapter
 */
export declare class ValidationAgentAdapter implements StandardAEAgent<ValidationInput, ValidationOutput> {
    private validationAgent;
    readonly agentName = "ValidationAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "validation";
    constructor();
    process(input: ValidationInput, context?: ProcessingContext): Promise<PhaseResult<ValidationOutput>>;
    validateInput(input: ValidationInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildValidationReport;
    private calculateQualityScore;
    private buildErrorResult;
}
/**
 * Domain Modeling Agent Adapter
 */
export declare class DomainModelingAgentAdapter implements StandardAEAgent<DomainModelingInput, DomainModelingOutput> {
    private domainAgent;
    readonly agentName = "DomainModelingAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "domain-modeling";
    constructor();
    process(input: DomainModelingInput, context?: ProcessingContext): Promise<PhaseResult<DomainModelingOutput>>;
    validateInput(input: DomainModelingInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildDomainPrompt;
    private transformDomainResult;
    private buildErrorResult;
}

// ---- src/agents/adapters/ui-ux-agent-adapter.d.ts ----
/**
 * UI/UX Agent Adapter (Placeholder Implementation)
 * Provides a standardized interface for UI/UX generation phase
 * TODO: Replace with actual UI/UX generation agent when available
 */
import { StandardAEAgent, ProcessingContext, PhaseResult, ValidationResult, AgentCapabilities, UIUXInput, UIUXOutput } from '../interfaces/standard-interfaces.js';
/**
 * Placeholder UI/UX Agent Adapter
 * Generates basic UI/UX artifacts based on domain model and user stories
 */
export declare class UIUXAgentAdapter implements StandardAEAgent<UIUXInput, UIUXOutput> {
    readonly agentName = "UIUXAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "ui-ux-generation";
    process(input: UIUXInput, context?: ProcessingContext): Promise<PhaseResult<UIUXOutput>>;
    validateInput(input: UIUXInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private generateWireframes;
    private generateWireframeComponents;
    private generateUserFlows;
    private groupStoriesByFlow;
    private generateUIComponents;
    private generateDesignSystem;
    private generatePrototypes;
    private mapTypeToInputType;
    private buildErrorResult;
}

// ---- src/agents/base-agent.d.ts ----
/**
 * Base Agent class for all ae-framework agents
 * Provides common functionality for phase state management and steering documents
 */
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { SteeringLoader } from '../utils/steering-loader.js';
import { ValidationResult } from '../cli/types.js';
/**
 * Generic agent output interface for validation
 */
export interface AgentOutput {
    type: 'requirements' | 'specifications' | 'tests' | 'code' | 'verification' | 'deployment' | 'generic';
    content: string;
    artifacts: string[];
    metadata?: Record<string, any>;
    quality?: {
        score: number;
        metrics: Record<string, number>;
    };
}
export declare abstract class BaseAgent {
    protected phaseStateManager: PhaseStateManager;
    protected steeringLoader: SteeringLoader;
    protected phaseName: PhaseType;
    constructor(phaseName: PhaseType);
    /**
     * Initialize phase if not already started
     */
    protected initializePhase(): Promise<void>;
    /**
     * Check if can proceed with current phase
     */
    protected canProceed(): Promise<{
        canProceed: boolean;
        reason?: string;
    }>;
    /**
     * Complete current phase with artifacts
     */
    protected completePhase(artifacts: string[]): Promise<void>;
    /**
     * Get steering context for the agent
     */
    protected getSteeringContext(): Promise<string>;
    /**
     * Get steering documents
     */
    protected getSteeringDocuments(): Promise<Record<string, string>>;
    /**
     * Log phase activity
     */
    protected logActivity(activity: string, metadata?: any): Promise<void>;
    /**
     * Get artifacts from previous phase
     */
    protected getPreviousPhaseArtifacts(): Promise<string[]>;
    /**
     * Check if approvals are required
     */
    protected requiresApproval(): Promise<boolean>;
    /**
     * Generate phase report
     */
    protected generatePhaseReport(): Promise<string>;
    /**
     * Default safe validation method
     * Concrete agents should override this with their specific validation logic
     * Default implementation always passes to prevent system failures
     */
    protected validate(output: AgentOutput): Promise<ValidationResult>;
    /**
     * Wrapper method to ensure validation is always called safely
     * This method should be called by concrete agents after generating output
     */
    protected validateOutput(output: AgentOutput): Promise<ValidationResult>;
    /**
     * Safe logging method that never throws exceptions
     * Falls back to console logging if phase state logging fails
     */
    private safeLogActivity;
}

// ---- src/agents/code-generation-agent.d.ts ----
/**
 * Code Generation Agent
 * Phase 4 of ae-framework: Automated code generation from tests and specifications
 */
export interface CodeGenerationRequest {
    tests: TestFile[];
    specifications?: Specification;
    architecture?: ArchitecturePattern;
    language: 'typescript' | 'javascript' | 'python' | 'go' | 'rust' | 'elixir';
    framework?: string;
    style?: CodingStyle;
}
export interface TestFile {
    path: string;
    content: string;
    type: 'unit' | 'integration' | 'e2e';
}
export interface Specification {
    openapi?: string;
    tla?: string;
    contracts?: Contract[];
    requirements?: string[];
}
export interface Contract {
    name: string;
    preconditions: string[];
    postconditions: string[];
    invariants: string[];
}
export interface ArchitecturePattern {
    pattern: 'mvc' | 'hexagonal' | 'clean' | 'ddd' | 'microservice';
    layers?: Layer[];
    dependencies?: Dependency[];
}
export interface Layer {
    name: string;
    responsibilities: string[];
    allowedDependencies: string[];
}
export interface Dependency {
    from: string;
    to: string;
    type: 'uses' | 'implements' | 'extends';
}
export interface CodingStyle {
    naming: 'camelCase' | 'snake_case' | 'PascalCase';
    indentation: 'spaces' | 'tabs';
    indentSize?: number;
    maxLineLength?: number;
    preferConst?: boolean;
    preferArrowFunctions?: boolean;
}
export interface GeneratedCode {
    files: CodeFile[];
    structure: ProjectStructure;
    dependencies: string[];
    testResults: TestResult[];
    coverage: number;
    suggestions: string[];
}
export interface CodeFile {
    path: string;
    content: string;
    purpose: string;
    tests: string[];
}
export interface ProjectStructure {
    directories: string[];
    entryPoint: string;
    configFiles: ConfigFile[];
}
export interface ConfigFile {
    name: string;
    content: string;
    purpose: string;
}
export interface TestResult {
    test: string;
    status: 'passing' | 'failing' | 'pending';
    error?: string;
}
export declare class CodeGenerationAgent {
    /**
     * Generate code from tests (TDD approach)
     */
    generateCodeFromTests(request: CodeGenerationRequest): Promise<GeneratedCode>;
    /**
     * Generate code from OpenAPI specification
     */
    generateFromOpenAPI(spec: string, options: {
        framework: 'fastify' | 'express' | 'koa';
        database?: 'postgres' | 'mongodb' | 'mysql';
        includeValidation?: boolean;
        includeAuth?: boolean;
    }): Promise<GeneratedCode>;
    /**
     * Apply design patterns to code
     */
    applyDesignPatterns(code: string, patterns: string[]): Promise<string>;
    /**
     * Optimize code for performance
     */
    optimizePerformance(code: string, metrics: {
        targetResponseTime?: number;
        targetMemoryUsage?: number;
        targetCPUUsage?: number;
    }): Promise<{
        optimizedCode: string;
        improvements: PerformanceImprovement[];
        benchmarks: Benchmark[];
    }>;
    /**
     * Add security features to code
     */
    addSecurityFeatures(code: string, requirements: {
        authentication?: 'jwt' | 'oauth' | 'basic';
        authorization?: 'rbac' | 'abac' | 'simple';
        encryption?: boolean;
        rateLimit?: boolean;
        cors?: boolean;
    }): Promise<string>;
    /**
     * Generate error handling code
     */
    generateErrorHandling(code: string, strategy: {
        type: 'try-catch' | 'result-type' | 'middleware';
        logging?: boolean;
        recovery?: boolean;
        userFriendly?: boolean;
    }): Promise<string>;
    /**
     * Generate database access layer
     */
    generateDataAccessLayer(schema: DatabaseSchema, options: {
        orm?: 'typeorm' | 'prisma' | 'sequelize' | 'none';
        database: 'postgres' | 'mysql' | 'mongodb' | 'sqlite';
        includeTransactions?: boolean;
        includeMigrations?: boolean;
    }): Promise<GeneratedCode>;
    /**
     * Refactor existing code
     */
    refactorCode(code: string, goals: {
        reduceComplexity?: boolean;
        improveDRY?: boolean;
        improveNaming?: boolean;
        extractMethods?: boolean;
        introducePatterns?: string[];
    }): Promise<{
        refactoredCode: string;
        changes: RefactoringChange[];
        metrics: CodeMetrics;
    }>;
    private analyzeTests;
    private designArchitecture;
    private generateImplementation;
    private generateFunctionImplementation;
    private generateElixirFunction;
    private generatePhoenixModule;
    private generateTSFunction;
    private generatePythonFunction;
    private generateRustFunction;
    private generateGoFunction;
    private getFileExtension;
    private getTestExtension;
    private getSourceDirectory;
    private getTestDirectory;
    private capitalize;
    private runTests;
    private calculateCoverage;
    private generateSuggestions;
    private generateValidationMiddleware;
    private generateAuthMiddleware;
    private generateServerSetup;
    private parseOpenAPI;
    private generateRouteHandler;
    private generateModel;
    private createProjectStructure;
    private identifyDependencies;
    private getFrameworkDependencies;
    private applySingletonPattern;
    private applyFactoryPattern;
    private applyObserverPattern;
    private applyStrategyPattern;
    private applyDecoratorPattern;
    private applyRepositoryPattern;
    private identifyBottlenecks;
    private optimizeBottleneck;
    private applyOptimization;
    private runBenchmarks;
    private addAuthentication;
    private addAuthorization;
    private addEncryption;
    private addRateLimiting;
    private addCORS;
    private wrapInTryCatch;
    private convertToResultType;
    private addErrorMiddleware;
    private addErrorLogging;
    private addRecoveryMechanisms;
    private addUserFriendlyErrors;
    private generateEntity;
    private generateRepository;
    private generateDatabaseConnection;
    private generateMigrations;
    private generateTransactionHelpers;
    private createDataLayerStructure;
    private getORMDependencies;
    private reduceComplexity;
    private eliminateDuplication;
    private improveNaming;
    private extractMethods;
    private calculateMetrics;
}
interface DatabaseSchema {
    tables: Table[];
    relations: Relation[];
}
interface Table {
    name: string;
    columns: Column[];
    indexes: Index[];
}
interface Column {
    name: string;
    type: string;
    nullable: boolean;
    primary?: boolean;
    unique?: boolean;
}
interface Index {
    name: string;
    columns: string[];
    unique: boolean;
}
interface Relation {
    from: string;
    to: string;
    type: 'one-to-one' | 'one-to-many' | 'many-to-many';
}
interface PerformanceImprovement {
    location: string;
    type: string;
    description: string;
    impact: 'high' | 'medium' | 'low';
}
interface Benchmark {
    name: string;
    before: number;
    after: number;
    improvement: number;
}
interface RefactoringChange {
    type: string;
    location: string;
    description: string;
}
interface CodeMetrics {
    complexity: number;
    maintainability: number;
    duplication: number;
    testCoverage: number;
}
export {};

// ---- src/agents/container-agent.d.ts ----
/**
 * Container Agent - Phase 3 of Issue #37
 * Integrates container-based verification environments with the ae-framework
 */
import { ContainerManagerConfig } from '../services/container/container-manager.js';
export interface AgentResult<T = any> {
    success: boolean;
    message: string;
    data?: T;
    error?: string;
}
export interface ContainerAgentConfig extends ContainerManagerConfig {
    containerfilesPath?: string;
    registryConfig?: {
        url: string;
        username?: string;
        password?: string;
    };
    buildConfig?: {
        parallel: boolean;
        maxConcurrentBuilds: number;
        cacheEnabled: boolean;
    };
}
export interface ContainerVerificationRequest {
    projectPath: string;
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    jobName?: string;
    timeout?: number;
    buildImages?: boolean;
    environment?: Record<string, string>;
}
export interface ContainerBuildRequest {
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    baseImage?: string;
    tag?: string;
    push?: boolean;
    buildArgs?: Record<string, string>;
}
export interface ContainerStatusResult {
    engine: {
        name: string;
        version: string;
        available: boolean;
    };
    jobs: {
        active: number;
        completed: number;
        failed: number;
        total: number;
    };
    resources: {
        containers: number;
        images: number;
        volumes: number;
    };
    health: boolean;
}
export declare class ContainerAgent {
    private containerManager;
    private config;
    private initialized;
    constructor(config?: ContainerAgentConfig);
    /**
     * Initialize the container agent and underlying systems
     */
    initialize(): Promise<AgentResult>;
    /**
     * Run verification job in container
     */
    runVerification(request: ContainerVerificationRequest): Promise<AgentResult>;
    /**
     * Build verification container image
     */
    buildVerificationImage(request: ContainerBuildRequest): Promise<AgentResult>;
    /**
     * Get verification job status
     */
    getJobStatus(jobId: string): Promise<AgentResult>;
    /**
     * List verification jobs
     */
    listJobs(filter?: {
        status?: 'pending' | 'running' | 'completed' | 'failed';
        language?: string;
    }): Promise<AgentResult>;
    /**
     * Cancel running verification job
     */
    cancelJob(jobId: string): Promise<AgentResult>;
    /**
     * Get container agent and system status
     */
    getStatus(): Promise<AgentResult<ContainerStatusResult>>;
    /**
     * Cleanup old containers and resources
     */
    cleanup(options?: {
        maxAge?: number;
        keepCompleted?: number;
        force?: boolean;
    }): Promise<AgentResult>;
    /**
     * List available container engines
     */
    listEngines(): Promise<AgentResult>;
    /**
     * Shutdown container agent
     */
    shutdown(): Promise<AgentResult>;
    private ensureInitialized;
    private createDefaultContainerfiles;
    private setupEventHandlers;
}

// ---- src/agents/domain-modeling-task-adapter.d.ts ----
/**
 * Domain Modeling Task Adapter for Claude Code
 *
 * This adapter integrates Phase 5 (Domain Modeling) processing with Claude Code's
 * Task tool, enabling seamless domain analysis, entity modeling, and
 * architectural design workflows.
 */
import { TaskRequest, TaskResponse } from './task-types.js';
export interface DomainEntity {
    name: string;
    type: 'aggregate' | 'entity' | 'value_object' | 'service' | 'repository';
    description: string;
    attributes: EntityAttribute[];
    methods: EntityMethod[];
    relationships: EntityRelationship[];
    businessRules: string[];
    invariants: string[];
}
export interface EntityAttribute {
    name: string;
    type: string;
    required: boolean;
    description: string;
    constraints: string[];
}
export interface EntityMethod {
    name: string;
    parameters: Parameter[];
    returnType: string;
    description: string;
    businessRule?: string;
}
export interface Parameter {
    name: string;
    type: string;
    required: boolean;
}
export interface EntityRelationship {
    type: 'composition' | 'aggregation' | 'association' | 'inheritance' | 'dependency';
    target: string;
    cardinality: string;
    description: string;
}
export interface DomainModel {
    entities: DomainEntity[];
    boundedContexts: BoundedContext[];
    domainServices: DomainService[];
    aggregates: AggregateRoot[];
    ubiquitousLanguage: UbiquitousLanguageTerm[];
    businessRules: BusinessRule[];
}
export interface BoundedContext {
    name: string;
    description: string;
    entities: string[];
    services: string[];
    responsibilities: string[];
    interfaces: ContextInterface[];
}
export interface ContextInterface {
    name: string;
    type: 'command' | 'query' | 'event';
    description: string;
    contract: string;
}
export interface DomainService {
    name: string;
    description: string;
    operations: ServiceOperation[];
    dependencies: string[];
}
export interface ServiceOperation {
    name: string;
    description: string;
    inputs: Parameter[];
    outputs: Parameter[];
    businessRule: string;
}
export interface AggregateRoot {
    name: string;
    description: string;
    entities: string[];
    valueObjects: string[];
    businessRules: string[];
    invariants: string[];
}
export interface UbiquitousLanguageTerm {
    term: string;
    definition: string;
    context: string;
    synonyms: string[];
    relatedTerms: string[];
}
export interface BusinessRule {
    id: string;
    name: string;
    description: string;
    type: 'constraint' | 'derivation' | 'existence' | 'action_enabler';
    entities: string[];
    conditions: string[];
    actions: string[];
}
export declare class DomainModelingTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for Domain Modeling tasks from Claude Code
     */
    handleDomainModelingTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive domain modeling guidance for Claude Code
     */
    provideProactiveGuidance(context: {
        recentFiles: string[];
        recentActions: string[];
        userIntent: string;
    }): Promise<{
        shouldIntervene: boolean;
        intervention: {
            type: 'warning' | 'suggestion' | 'block';
            message: string;
            recommendedActions: string[];
        };
    }>;
    private handleDomainAnalysis;
    private handleEntityIdentification;
    private handleAggregateModeling;
    private handleBoundedContextDefinition;
    private handleBusinessRuleExtraction;
    private handleUbiquitousLanguageCreation;
    private handleDomainServiceDesign;
    private handleDomainModelValidation;
    private handleGenericDomainModeling;
    private classifyTask;
    private extractDomainInput;
    private extractEntityInput;
    private extractAggregateInput;
    private extractContextInput;
    private extractBusinessRuleInput;
    private extractLanguageInput;
    private extractServiceInput;
    private extractModelInput;
    private extractGenericInput;
    private analyzeDomain;
    private identifyEntities;
    private modelAggregates;
    private defineBoundedContexts;
    private extractBusinessRules;
    private createUbiquitousLanguage;
    private designDomainServices;
    private validateDomainModel;
    private performGenericDomainAnalysis;
    private analyzeRecentActivity;
}
export declare const createDomainModelingTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};

// ---- src/agents/domain-types.d.ts ----
/**
 * @fileoverview Domain Types for Unified Agent System
 * Phase 2: Agent System Refactoring - Domain Modeling Implementation
 * Core domain types for unified agent architecture per ae-framework-v2.yml
 */
/**
 * Task types supported by the unified agent system
 */
export declare enum TaskType {
    INTENT_ANALYSIS = "intent-analysis",
    FORMAL_SPECIFICATION = "formal-specification",
    TEST_GENERATION = "test-generation",
    CODE_GENERATION = "code-generation",
    VERIFICATION = "verification",
    VALIDATION = "validation",
    DEPLOYMENT = "deployment",
    QUALITY_ASSURANCE = "quality-assurance",
    PHASE_VALIDATION = "phase-validation"
}
/**
 * Task specification structure for unified processing
 */
export interface TaskSpecification {
    requirements: string;
    acceptance: string[];
    context: Record<string, any>;
}
/**
 * Unified task definition for all agent types
 */
export interface AgentTask {
    id: string;
    type: TaskType;
    specification: TaskSpecification;
    metadata: {
        priority: number;
        estimatedComplexity: number;
        dependencies?: string[];
        deadline?: Date;
    };
}
/**
 * Task execution result with validation
 */
export interface TaskResult {
    success: boolean;
    taskId: string;
    artifacts: string[];
    validation: {
        typeScriptCompliant: boolean;
        strictModeCompatible?: boolean;
        errorCount: number;
        testsPassing?: boolean;
    };
    tddCompliance?: {
        testsFirst: boolean;
        redPhaseCompleted: boolean;
        greenPhaseCompleted: boolean;
        refactorPhaseCompleted?: boolean;
    };
    metrics?: {
        testCoverage: number;
        executionTime: number;
        qualityScore: number;
    };
    phaseValidation?: {
        readyForNextPhase: boolean;
        completionCriteria: string[];
    };
    errors?: string[];
}
/**
 * Agent context for phase and project state
 */
export interface AgentContext {
    projectRoot: string;
    phase: string;
    tddEnabled: boolean;
    strictMode?: boolean;
    coverageThreshold?: number;
}
/**
 * Unified agent configuration
 */
export interface AgentConfig {
    id: string;
    type: string;
    capabilities: string[];
    context: AgentContext;
}
/**
 * Agent state for lifecycle management
 */
export interface AgentState {
    initialized: boolean;
    currentTask?: string;
    tasksCompleted: number;
    totalExecutionTime: number;
    averageQualityScore: number;
}
/**
 * Quality metrics for agent output validation
 */
export interface QualityMetrics {
    testCoverage: number;
    codeComplexity: number;
    typeScriptErrors: number;
    lintWarnings: number;
    performanceScore: number;
}
/**
 * Validation result structure
 */
export interface ValidationResult {
    success: boolean;
    message: string;
    details: Array<{
        check: string;
        passed: boolean;
        message: string;
        value?: any;
    }>;
}

// ---- src/agents/examples/pipeline-integration-example.d.ts ----
/**
 * AE Framework Pipeline Integration Example
 * Demonstrates how to use the standardized pipeline for benchmark integration
 */
/**
 * Example: Complete AE Framework Pipeline Execution
 */
export declare function runCompleteAEFrameworkPipeline(): Promise<import("../pipeline/ae-framework-pipeline.js").PipelineResult>;
/**
 * Example: Individual Phase Execution
 */
export declare function runIndividualPhaseExample(): Promise<import("../interfaces/standard-interfaces.js").PhaseResult<unknown>>;
/**
 * Example: Pipeline Capabilities Inspection
 */
export declare function inspectPipelineCapabilities(): void;
/**
 * Example: Benchmark Integration
 * Shows how to integrate with req2run-benchmark using standardized pipeline
 */
export declare function benchmarkIntegrationExample(): Promise<import("../pipeline/ae-framework-pipeline.js").PipelineResult>;
export default runCompleteAEFrameworkPipeline;

// ---- src/agents/formal-agent.d.ts ----
import { z } from "zod";
export declare const FormalAgentConfig: z.ZodObject<{
    outputFormat: z.ZodDefault<z.ZodEnum<["tla+", "alloy", "z-notation", "openapi", "asyncapi", "graphql"]>>;
    validationLevel: z.ZodDefault<z.ZodEnum<["basic", "comprehensive", "formal-verification"]>>;
    generateDiagrams: z.ZodDefault<z.ZodBoolean>;
    enableModelChecking: z.ZodDefault<z.ZodBoolean>;
}, "strip", z.ZodTypeAny, {
    outputFormat?: "tla+" | "alloy" | "z-notation" | "openapi" | "asyncapi" | "graphql";
    validationLevel?: "basic" | "comprehensive" | "formal-verification";
    generateDiagrams?: boolean;
    enableModelChecking?: boolean;
}, {
    outputFormat?: "tla+" | "alloy" | "z-notation" | "openapi" | "asyncapi" | "graphql";
    validationLevel?: "basic" | "comprehensive" | "formal-verification";
    generateDiagrams?: boolean;
    enableModelChecking?: boolean;
}>;
export type FormalAgentConfig = z.infer<typeof FormalAgentConfig>;
export interface FormalSpecification {
    id: string;
    type: "tla+" | "alloy" | "z-notation" | "state-machine" | "contracts" | "api-spec";
    title: string;
    content: string;
    metadata: {
        version: string;
        author: string;
        created: Date;
        lastModified: Date;
        dependencies: string[];
        properties: string[];
    };
    validation: {
        status: "valid" | "invalid" | "pending";
        errors: ValidationError[];
        warnings: ValidationWarning[];
    };
}
export interface ValidationError {
    type: string;
    message: string;
    location?: {
        line: number;
        column: number;
    };
    severity: "error" | "warning" | "info";
}
export interface ValidationWarning {
    type: string;
    message: string;
    suggestion?: string;
}
export interface APISpecification {
    format: "openapi" | "asyncapi" | "graphql";
    version: string;
    content: string;
    endpoints: Endpoint[];
    schemas: SchemaDefinition[];
}
export interface Endpoint {
    path: string;
    method: string;
    description: string;
    parameters: Parameter[];
    responses: Response[];
    contracts: Contract[];
}
export interface Parameter {
    name: string;
    type: string;
    required: boolean;
    description?: string;
    constraints?: Constraint[];
}
export interface Response {
    status: number;
    description: string;
    schema?: string;
}
export interface SchemaDefinition {
    name: string;
    type: "object" | "array" | "primitive";
    properties: Record<string, any>;
    constraints: Constraint[];
}
export interface Constraint {
    type: "range" | "pattern" | "enum" | "custom";
    value: any;
    description?: string;
}
export interface Contract {
    type: "precondition" | "postcondition" | "invariant";
    expression: string;
    description: string;
}
export interface StateMachine {
    name: string;
    states: State[];
    transitions: Transition[];
    initialState: string;
    finalStates: string[];
    invariants: string[];
}
export interface State {
    name: string;
    type: "initial" | "intermediate" | "final" | "error";
    properties: Record<string, any>;
    invariants: string[];
}
export interface Transition {
    from: string;
    to: string;
    event: string;
    guard?: string;
    action?: string;
}
export interface ModelCheckingResult {
    specification: string;
    properties: PropertyResult[];
    counterExamples: CounterExample[];
    statistics: {
        statesExplored: number;
        timeElapsed: number;
        memoryUsed: number;
    };
}
export interface PropertyResult {
    name: string;
    satisfied: boolean;
    description: string;
    counterExample?: CounterExample;
}
export interface CounterExample {
    trace: TraceStep[];
    description: string;
}
export interface TraceStep {
    state: Record<string, any>;
    action: string;
    timestamp: number;
}
/**
 * Formal Agent - Phase 2 of ae-framework
 * Bridges Intent (Phase 1) and Tests (Phase 3) by generating formal, verifiable specifications
 */
export declare class FormalAgent {
    private config;
    private specifications;
    constructor(config?: Partial<FormalAgentConfig>);
    /**
     * Generate formal specifications from requirements
     */
    generateFormalSpecification(requirements: string, type?: "tla+" | "alloy" | "z-notation", options?: {
        includeDiagrams?: boolean;
        generateProperties?: boolean;
    }): Promise<FormalSpecification>;
    /**
     * Create API specifications (OpenAPI, AsyncAPI, GraphQL)
     */
    createAPISpecification(requirements: string, format?: "openapi" | "asyncapi" | "graphql", options?: {
        includeExamples?: boolean;
        generateContracts?: boolean;
    }): Promise<APISpecification>;
    /**
     * Generate state machines from requirements
     */
    generateStateMachine(requirements: string, options?: {
        generateInvariants?: boolean;
        includeDiagrams?: boolean;
    }): Promise<StateMachine>;
    /**
     * Create Design by Contract specifications
     */
    createContracts(functionSignature: string, requirements: string, options?: {
        includeInvariants?: boolean;
    }): Promise<Contract[]>;
    /**
     * Validate specification consistency and correctness
     */
    validateSpecification(specification: FormalSpecification): Promise<{
        status: "valid" | "invalid" | "pending";
        errors: ValidationError[];
        warnings: ValidationWarning[];
    }>;
    /**
     * Run formal model checking on specifications
     */
    runModelChecking(specification: FormalSpecification, properties?: string[], options?: {
        timeout?: number;
        maxStates?: number;
    }): Promise<ModelCheckingResult>;
    /**
     * Generate UML and sequence diagrams
     */
    generateDiagrams(specification: FormalSpecification, types?: ("sequence" | "state" | "class" | "component")[]): Promise<{
        type: string;
        content: string;
    }[]>;
    private generateId;
    private generateTLASpec;
    private generateAlloySpec;
    private generateZSpec;
    private generateOpenAPISpec;
    private generateAsyncAPISpec;
    private generateGraphQLSchema;
    private extractTitle;
    private extractModuleName;
    private extractVariables;
    private extractConstants;
    private extractActions;
    private extractEndpoints;
    private generateSchemas;
    private extractStates;
    private extractTransitions;
    private extractPreconditions;
    private extractPostconditions;
    private extractInvariants;
    private validateTLASpec;
    private validateAlloySpec;
    private validateZSpec;
    private validateStateMachine;
    private validateContracts;
    private validateAPISpec;
    private checkProperty;
    private estimateStatesExplored;
    private generateSequenceDiagram;
    private generateStateDiagram;
    private generateClassDiagram;
    private generateComponentDiagram;
    private generateSafetyProperty;
    private extractTLAProperties;
    private extractAlloyProperties;
    private extractZProperties;
    private extractAlloySignatures;
    private extractAlloyFacts;
    private extractAlloyPredicates;
    private extractZSchemas;
    private extractZOperations;
    private extractStateMachineName;
    private generateInvariants;
    private getParameterLocation;
    private mapToGraphQLType;
    getSpecifications(): FormalSpecification[];
    getSpecification(id: string): FormalSpecification | undefined;
    getConfig(): FormalAgentConfig;
    updateConfig(newConfig: Partial<FormalAgentConfig>): void;
}

// ---- src/agents/intent-agent.d.ts ----
/**
 * Intent Agent
 * Phase 1 of ae-framework: Requirements gathering and intent analysis
 */
export interface IntentAnalysisRequest {
    sources: RequirementSource[];
    context?: ProjectContext;
    analysisDepth?: 'basic' | 'detailed' | 'comprehensive';
    outputFormat?: 'structured' | 'narrative' | 'both';
}
export interface RequirementSource {
    type: 'text' | 'document' | 'conversation' | 'issue' | 'email' | 'diagram';
    content: string;
    metadata?: SourceMetadata;
}
export interface SourceMetadata {
    author?: string;
    date?: Date;
    priority?: 'critical' | 'high' | 'medium' | 'low';
    tags?: string[];
    references?: string[];
}
export interface ProjectContext {
    domain: string;
    existingSystem?: boolean;
    constraints?: Constraint[];
    stakeholders?: Stakeholder[];
    glossary?: GlossaryTerm[];
}
export interface Constraint {
    type: 'technical' | 'business' | 'regulatory' | 'resource';
    description: string;
    impact: 'high' | 'medium' | 'low';
    source?: string;
}
export interface Stakeholder {
    name: string;
    role: string;
    concerns: string[];
    influenceLevel: 'high' | 'medium' | 'low';
}
export interface GlossaryTerm {
    term: string;
    definition: string;
    context?: string;
}
export interface IntentAnalysisResult {
    requirements: Requirement[];
    userStories: UserStory[];
    useCases: UseCase[];
    constraints: Constraint[];
    assumptions: Assumption[];
    risks: Risk[];
    domainModel: DomainModel;
    ambiguities: Ambiguity[];
    suggestions: string[];
    traceability: RequirementTrace[];
    primaryIntent: string;
}
export interface Requirement {
    id: string;
    type: 'functional' | 'non-functional' | 'business' | 'technical';
    category: string;
    description: string;
    rationale?: string;
    priority: 'must' | 'should' | 'could' | 'wont';
    acceptance: AcceptanceCriteria[];
    source: string;
    status: 'draft' | 'reviewed' | 'approved' | 'implemented';
    dependencies?: string[];
}
export interface AcceptanceCriteria {
    given: string;
    when: string;
    then: string;
}
export interface UserStory {
    id: string;
    title: string;
    narrative: {
        asA: string;
        iWant: string;
        soThat: string;
    };
    acceptance: AcceptanceCriteria[];
    points?: number;
    priority: 'high' | 'medium' | 'low';
    requirements: string[];
}
export interface UseCase {
    id: string;
    name: string;
    actors: string[];
    preconditions: string[];
    mainFlow: Step[];
    alternativeFlows: Flow[];
    postconditions: string[];
    exceptions: Exception[];
}
export interface Step {
    number: number;
    actor: string;
    action: string;
    system: string;
}
export interface Flow {
    name: string;
    trigger: string;
    steps: Step[];
}
export interface Exception {
    condition: string;
    handling: string;
}
export interface Assumption {
    id: string;
    description: string;
    impact: 'high' | 'medium' | 'low';
    validation: string;
}
export interface Risk {
    id: string;
    description: string;
    probability: 'high' | 'medium' | 'low';
    impact: 'high' | 'medium' | 'low';
    mitigation: string;
}
export interface DomainModel {
    entities: Entity[];
    relationships: Relationship[];
    boundedContexts: BoundedContext[];
    aggregates: Aggregate[];
}
export interface Entity {
    name: string;
    attributes: Attribute[];
    behaviors: string[];
    invariants: string[];
}
export interface Attribute {
    name: string;
    type: string;
    required: boolean;
    constraints?: string[];
}
export interface Relationship {
    from: string;
    to: string;
    type: 'has' | 'uses' | 'contains' | 'references';
    cardinality: '1-1' | '1-n' | 'n-1' | 'n-n';
}
export interface BoundedContext {
    name: string;
    entities: string[];
    ubiquitousLanguage: GlossaryTerm[];
}
export interface Aggregate {
    root: string;
    entities: string[];
    invariants: string[];
}
export interface Ambiguity {
    text: string;
    type: 'vague' | 'conflicting' | 'incomplete' | 'undefined';
    location: string;
    suggestion: string;
    severity: 'high' | 'medium' | 'low';
}
export interface RequirementTrace {
    requirementId: string;
    linkedTo: {
        specifications?: string[];
        tests?: string[];
        code?: string[];
        documentation?: string[];
    };
}
export declare class IntentAgent {
    private requirementCounter;
    private steeringLoader;
    constructor();
    /**
     * Helper method to create a simple intent analysis request from text
     * Addresses API usability issues by providing a more intuitive interface
     */
    static createSimpleRequest(content: string, options?: {
        sourceType?: RequirementSource['type'];
        domain?: string;
        analysisDepth?: IntentAnalysisRequest['analysisDepth'];
        outputFormat?: IntentAnalysisRequest['outputFormat'];
    }): IntentAnalysisRequest;
    /**
     * Helper method to create request from benchmark specification
     * Specifically designed for req2run-benchmark integration
     */
    static createBenchmarkRequest(spec: {
        title: string;
        description: string;
        requirements: Array<{
            id: string;
            description: string;
            priority: string;
        }>;
        constraints: any;
        metadata: {
            created_by: string;
            created_at: string;
            category: string;
            difficulty: string;
        };
    }): IntentAnalysisRequest;
    /**
     * Analyze requirements and extract intent
     */
    analyzeIntent(request: IntentAnalysisRequest): Promise<IntentAnalysisResult>;
    /**
     * Extract requirements from natural language
     */
    extractFromNaturalLanguage(text: string): Promise<Requirement[]>;
    /**
     * Generate user stories from requirements
     */
    createUserStories(requirements: Requirement[]): Promise<UserStory[]>;
    /**
     * Build domain model from requirements
     */
    buildDomainModelFromRequirements(requirements: Requirement[], context?: ProjectContext): Promise<DomainModel>;
    /**
     * Detect and resolve ambiguities
     */
    detectAmbiguities(sources: RequirementSource[]): Promise<Ambiguity[]>;
    /**
     * Validate requirements completeness
     */
    validateCompleteness(requirements: Requirement[]): Promise<{
        complete: boolean;
        missing: string[];
        coverage: number;
    }>;
    /**
     * Generate specification templates
     */
    generateSpecificationTemplates(requirements: Requirement[]): Promise<{
        gherkin: string[];
        openapi: object;
        asyncapi: object;
        graphql: string;
    }>;
    /**
     * Prioritize requirements using MoSCoW method
     */
    prioritizeRequirements(requirements: Requirement[], constraints: Constraint[]): Promise<Requirement[]>;
    /**
     * Generate acceptance criteria
     */
    generateAcceptanceCriteria(requirement: Requirement): Promise<AcceptanceCriteria[]>;
    /**
     * Analyze stakeholder concerns
     */
    analyzeStakeholderConcerns(stakeholders: Stakeholder[], requirements: Requirement[]): Promise<{
        addressed: Map<string, string[]>;
        unaddressed: Map<string, string[]>;
        conflicts: Array<{
            stakeholder1: string;
            stakeholder2: string;
            issue: string;
        }>;
    }>;
    private extractRequirements;
    private extractFromSource;
    private parseDocument;
    private extractFromConversation;
    private parseIssue;
    private extractFromEmail;
    private extractFromDiagram;
    private parseRequirements;
    private determineRequirementType;
    private determineCategory;
    private determinePriority;
    private generateUserStories;
    private generateUserStoryTitle;
    private generateUserStoryNarrative;
    private generateUseCases;
    private buildDomainModel;
    private extractEntities;
    private identifyRelationships;
    private defineBoundedContexts;
    private identifyAggregates;
    private identifyConstraints;
    private identifyAssumptions;
    private analyzeRisks;
    private generateSuggestions;
    private createTraceability;
    private parseNaturalLanguageRequirement;
    private requirementToUserStory;
    private prioritizeUserStories;
    private generateGherkinScenarios;
    private generateOpenAPISpec;
    private generateAsyncAPISpec;
    private generateGraphQLSchema;
    private findConflicts;
    private areConflicting;
    /**
     * Parse requirements with steering document context
     */
    private parseRequirementsWithSteering;
    /**
     * Get steering-aware suggestions
     */
    getSteeringAwareSuggestions(): Promise<string[]>;
    /**
     * Extract primary intent from requirements
     */
    private extractPrimaryIntent;
}

// ---- src/agents/intent-task-adapter.d.ts ----
/**
 * Intent Task Adapter for Claude Code
 *
 * This adapter integrates Intent Agent with Claude Code's Task tool,
 * enabling seamless Phase 1 Intent workflow integration and proactive assistance.
 */
export interface TaskRequest {
    description: string;
    prompt: string;
    subagent_type: string;
}
export interface TaskResponse {
    summary: string;
    analysis: string;
    recommendations: string[];
    nextActions: string[];
    warnings: string[];
    shouldBlockProgress: boolean;
}
export declare class IntentTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for Intent-related tasks from Claude Code
     */
    handleIntentTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive Intent suggestions for Claude Code's autonomous operation
     */
    provideProactiveGuidance(context: {
        recentFiles: string[];
        recentActions: string[];
        userIntent: string;
    }): Promise<{
        shouldIntervene: boolean;
        intervention: {
            type: 'warning' | 'suggestion' | 'block';
            message: string;
            recommendedActions: string[];
        };
    }>;
    private handleRequirementsAnalysis;
    private handleNaturalLanguageExtraction;
    private handleUserStoryCreation;
    private handleCompletenessValidation;
    private handleDomainModeling;
    private handleGenericIntentGuidance;
    private classifyTask;
    private extractRequirementSources;
    private extractProjectContext;
    private extractTextContent;
    private extractRequirementsList;
    private formatIntentAnalysis;
    private formatExtractedRequirements;
    private formatUserStories;
    private formatCompletenessValidation;
    private formatDomainModel;
    private generateIntentRecommendations;
    private identifyIntentWarnings;
    private analyzeRecentActivity;
}
export declare const createIntentTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};

// ---- src/agents/interfaces/standard-interfaces.d.ts ----
/**
 * Standard AE Framework Agent Interfaces
 * Provides consistent input/output patterns for agent pipeline integration
 */
/**
 * Standard processing context shared across all agents
 */
export interface ProcessingContext {
    projectId?: string;
    domain?: string;
    previousPhaseResults?: PhaseResult[];
    metadata?: Record<string, any>;
    requestId?: string;
    timestamp?: string;
}
/**
 * Standardized phase result wrapper
 */
export interface PhaseResult<T = any> {
    success: boolean;
    data: T;
    metadata: PhaseMetadata;
    errors?: AgentError[];
    warnings?: string[];
    phase: PhaseType;
}
/**
 * Phase execution metadata
 */
export interface PhaseMetadata {
    phase: PhaseType;
    agentName: string;
    startTime: Date;
    endTime: Date;
    duration: number;
    version: string;
    inputHash?: string;
    confidence?: number;
}
/**
 * Standardized error format
 */
export interface AgentError {
    code: string;
    message: string;
    phase: PhaseType;
    severity: 'error' | 'warning' | 'info';
    context?: Record<string, any>;
    stack?: string;
}
/**
 * Phase types supported by the AE Framework pipeline
 */
export type PhaseType = 'intent' | 'requirements' | 'user-stories' | 'validation' | 'domain-modeling' | 'ui-ux-generation';
/**
 * Standard agent interface - all AE Framework agents should implement this
 */
export interface StandardAEAgent<TInput = any, TOutput = any> {
    readonly agentName: string;
    readonly version: string;
    readonly supportedPhase: PhaseType;
    /**
     * Main processing method - standardized across all agents
     */
    process(input: TInput, context?: ProcessingContext): Promise<PhaseResult<TOutput>>;
    /**
     * Validate input before processing
     */
    validateInput(input: TInput): ValidationResult;
    /**
     * Get agent metadata and capabilities
     */
    getCapabilities(): AgentCapabilities;
}
/**
 * Input validation result
 */
export interface ValidationResult {
    valid: boolean;
    errors: string[];
    warnings: string[];
}
/**
 * Agent capabilities description
 */
export interface AgentCapabilities {
    supportedInputTypes: string[];
    outputSchema: string;
    requiredContext: string[];
    optionalContext: string[];
    maxInputSize?: number;
    estimatedProcessingTime?: number;
}
/**
 * Pipeline data flow interfaces
 */
export interface IntentInput {
    sources: RequirementSource[];
    context?: ProjectContext;
}
export interface IntentOutput {
    primaryIntent: string;
    requirements: Requirement[];
    stakeholders: Stakeholder[];
    constraints: Constraint[];
    businessContext: BusinessContext;
    confidenceScore: number;
}
export interface RequirementsInput {
    intentAnalysis: IntentOutput;
    additionalRequirements?: string;
}
export interface RequirementsOutput {
    structured: StructuredRequirement[];
    summary: string;
    gaps: string[];
    processedRequirements: string;
    naturalLanguageRequirements: string;
}
export interface UserStoriesInput {
    requirements: RequirementsOutput;
    stakeholders: Stakeholder[];
}
export interface UserStoriesOutput {
    stories: UserStory[];
    acceptanceCriteria: AcceptanceCriteria[];
    traceabilityMatrix: TraceabilityMatrix;
    success: boolean;
}
export interface ValidationInput {
    userStories: UserStoriesOutput;
    requirements: RequirementsOutput;
    constraints: Constraint[];
}
export interface ValidationOutput {
    validatedStories: UserStory[];
    validationReport: ValidationReport;
    conflicts: Conflict[];
    recommendations: string[];
}
export interface DomainModelingInput {
    validatedUserStories: ValidationOutput;
    requirements: RequirementsOutput;
    businessContext: BusinessContext;
}
export interface DomainModelingOutput {
    entities: DomainEntity[];
    relationships: EntityRelationship[];
    valueObjects: ValueObject[];
    aggregates: Aggregate[];
    services: DomainService[];
    boundedContexts: BoundedContext[];
}
export interface UIUXInput {
    domainModel: DomainModelingOutput;
    userStories: UserStoriesOutput;
    stakeholders: Stakeholder[];
}
export interface UIUXOutput {
    wireframes: Wireframe[];
    userFlows: UserFlow[];
    components: UIComponent[];
    designSystem: DesignSystem;
    prototypes: Prototype[];
}
/**
 * Supporting type definitions
 */
export interface RequirementSource {
    type: 'text' | 'document' | 'specification' | 'conversation';
    content: string;
    metadata?: Record<string, any>;
}
export interface ProjectContext {
    domain: string;
    organization?: string;
    existingSystem?: boolean;
    constraints?: Constraint[];
    stakeholders?: Stakeholder[];
    glossary?: GlossaryTerm[];
}
export interface Requirement {
    id: string;
    description: string;
    type: 'functional' | 'non-functional' | 'constraint';
    priority: 'must' | 'should' | 'could' | 'won\'t';
    source: string;
    acceptance_criteria: string[];
}
export interface Stakeholder {
    name: string;
    role: string;
    concerns: string[];
    influenceLevel: 'high' | 'medium' | 'low';
}
export interface Constraint {
    type: 'technical' | 'business' | 'regulatory' | 'resource';
    description: string;
    impact: 'high' | 'medium' | 'low';
    source?: string;
}
export interface BusinessContext {
    domain: string;
    businessModel: string;
    keyProcesses: string[];
    success_metrics: string[];
    assumptions: string[];
}
export interface GlossaryTerm {
    term: string;
    definition: string;
    context?: string;
}
export interface StructuredRequirement extends Requirement {
    category: string;
    dependencies: string[];
    risks: string[];
}
export interface UserStory {
    id: string;
    title: string;
    description: string;
    asA: string;
    iWant: string;
    soThat: string;
    acceptanceCriteria: string[];
    priority: 'high' | 'medium' | 'low';
    storyPoints?: number;
    tags?: string[];
}
export interface AcceptanceCriteria {
    storyId: string;
    criteria: string[];
    testScenarios: TestScenario[];
}
export interface TestScenario {
    given: string;
    when: string;
    then: string;
}
export interface TraceabilityMatrix {
    requirements: Record<string, string[]>;
    coverage: number;
    gaps: string[];
}
export interface ValidationReport {
    totalStories: number;
    validatedStories: number;
    conflicts: number;
    coverage: number;
    quality_score: number;
}
export interface Conflict {
    type: 'requirement' | 'story' | 'constraint';
    description: string;
    affected: string[];
    severity: 'high' | 'medium' | 'low';
    recommendation: string;
}
export interface DomainEntity {
    name: string;
    attributes: EntityAttribute[];
    methods: EntityMethod[];
    invariants: string[];
    isAggregateRoot: boolean;
}
export interface EntityAttribute {
    name: string;
    type: string;
    required: boolean;
    description?: string;
}
export interface EntityMethod {
    name: string;
    parameters: MethodParameter[];
    returnType: string;
    description: string;
}
export interface MethodParameter {
    name: string;
    type: string;
    required: boolean;
}
export interface EntityRelationship {
    from: string;
    to: string;
    type: 'one-to-one' | 'one-to-many' | 'many-to-many';
    description: string;
}
export interface ValueObject {
    name: string;
    attributes: EntityAttribute[];
    invariants: string[];
}
export interface Aggregate {
    name: string;
    root: string;
    entities: string[];
    valueObjects: string[];
    invariants: string[];
}
export interface DomainService {
    name: string;
    methods: EntityMethod[];
    dependencies: string[];
}
export interface BoundedContext {
    name: string;
    description: string;
    entities: string[];
    services: string[];
    aggregates: string[];
}
export interface Wireframe {
    name: string;
    type: 'low-fidelity' | 'high-fidelity';
    components: WireframeComponent[];
    userFlow: string;
}
export interface WireframeComponent {
    type: string;
    properties: Record<string, any>;
    children?: WireframeComponent[];
}
export interface UserFlow {
    name: string;
    steps: UserFlowStep[];
    triggers: string[];
    outcomes: string[];
}
export interface UserFlowStep {
    action: string;
    screen: string;
    nextStep?: string;
    conditions?: string[];
}
export interface UIComponent {
    name: string;
    type: string;
    props: ComponentProp[];
    states: ComponentState[];
    interactions: ComponentInteraction[];
}
export interface ComponentProp {
    name: string;
    type: string;
    required: boolean;
    description?: string;
}
export interface ComponentState {
    name: string;
    description: string;
    triggers: string[];
}
export interface ComponentInteraction {
    event: string;
    action: string;
    feedback: string;
}
export interface DesignSystem {
    colors: Record<string, string>;
    typography: TypographyScale;
    spacing: SpacingScale;
    components: ComponentLibrary;
}
export interface TypographyScale {
    fonts: Record<string, string>;
    sizes: Record<string, string>;
    weights: Record<string, number>;
}
export interface SpacingScale {
    base: number;
    scale: Record<string, number>;
}
export interface ComponentLibrary {
    [componentName: string]: UIComponent;
}
export interface Prototype {
    name: string;
    type: 'static' | 'interactive';
    screens: Screen[];
    interactions: PrototypeInteraction[];
}
export interface Screen {
    name: string;
    wireframe: string;
    components: UIComponent[];
}
export interface PrototypeInteraction {
    from: string;
    to: string;
    trigger: string;
    transition: string;
}

// ---- src/agents/natural-language-task-adapter.d.ts ----
/**
 * Natural Language Requirements Task Adapter for Claude Code
 *
 * This adapter integrates Phase 2 (Natural Language Requirements) processing
 * with Claude Code's Task tool, enabling seamless requirements analysis and
 * natural language processing workflows.
 */
import { TaskRequest, TaskResponse, ProactiveGuidanceContext, ProactiveGuidanceResult } from './task-types.js';
export interface RequirementDocument {
    title: string;
    content: string;
    source: string;
    type: 'functional' | 'non-functional' | 'business' | 'technical';
    priority: 'high' | 'medium' | 'low';
    stakeholder?: string;
}
export interface ProcessedRequirements {
    structured: RequirementDocument[];
    summary: string;
    gaps: string[];
    conflicts: string[];
    ambiguities: string[];
    clarificationNeeded: string[];
    processedRequirements?: string;
    naturalLanguageRequirements?: string;
}
export declare class NaturalLanguageTaskAdapter {
    private agent;
    private static readonly MAX_REQUIREMENTS_BEFORE_CONFLICTS;
    constructor();
    /**
     * Main handler for Natural Language Requirements tasks from Claude Code
     */
    handleNaturalLanguageTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive natural language processing guidance for Claude Code
     */
    provideProactiveGuidance(context: ProactiveGuidanceContext): Promise<ProactiveGuidanceResult>;
    private handleRequirementsAnalysis;
    private handleEntityExtraction;
    private handleCompletenessValidation;
    private handleAmbiguityResolution;
    private handleRequirementsStructuring;
    private handleGapIdentification;
    private handleGenericNLProcessing;
    private classifyTask;
    private extractRequirementsText;
    processNaturalLanguageRequirements(text: string): Promise<ProcessedRequirements>;
    private inferRequirementType;
    private inferPriority;
    private identifyStructuralGaps;
    private detectConflicts;
    private detectAmbiguousLanguage;
    private generateClarificationQuestions;
    private extractBusinessEntities;
    private validateRequirementsCompleteness;
    private identifyAmbiguities;
    private structureRequirements;
    private identifyRequirementGaps;
    private performGenericNLAnalysis;
    private analyzeRecentActivity;
}
export declare const createNaturalLanguageTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: ProactiveGuidanceContext) => Promise<ProactiveGuidanceResult>;
};

// ---- src/agents/operate-agent.d.ts ----
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

// ---- src/agents/pipeline/ae-framework-pipeline.d.ts ----
/**
 * AE Framework Pipeline Orchestrator
 * Provides standardized pipeline execution for the 6-phase AE Framework workflow
 */
import { ProcessingContext, PhaseResult, PhaseType, StandardAEAgent, IntentInput, AgentError } from '../interfaces/standard-interfaces.js';
/**
 * Pipeline execution configuration
 */
export interface PipelineConfig {
    projectId: string;
    domain: string;
    enableParallelProcessing?: boolean;
    validateInputs?: boolean;
    retryFailures?: boolean;
    maxRetries?: number;
    timeoutMs?: number;
}
/**
 * Pipeline execution result
 */
export interface PipelineResult {
    success: boolean;
    config: PipelineConfig;
    phases: PhaseResult[];
    totalDuration: number;
    errors: AgentError[];
    metadata: PipelineMetadata;
}
/**
 * Pipeline metadata
 */
export interface PipelineMetadata {
    startTime: Date;
    endTime: Date;
    version: string;
    agentsUsed: string[];
    dataFlowTrace: DataFlowTrace[];
}
/**
 * Data flow tracing for debugging
 */
export interface DataFlowTrace {
    phase: PhaseType;
    inputSize: number;
    outputSize: number;
    transformations: string[];
}
/**
 * AE Framework Pipeline orchestrator class
 */
export declare class AEFrameworkPipeline {
    private agents;
    private config;
    constructor(config: PipelineConfig);
    /**
     * Register an agent for a specific phase
     */
    registerAgent(phase: PhaseType, agent: StandardAEAgent): void;
    /**
     * Execute complete 6-phase AE Framework pipeline
     */
    executePipeline(input: IntentInput): Promise<PipelineResult>;
    /**
     * Execute a single phase with error handling and retries
     */
    executePhase<TInput, TOutput>(phase: PhaseType, input: TInput, context?: ProcessingContext): Promise<PhaseResult<TOutput>>;
    /**
     * Get pipeline status and capabilities
     */
    getPipelineCapabilities(): Record<PhaseType, any>;
    /**
     * Validate pipeline configuration
     */
    validatePipeline(): {
        valid: boolean;
        missing: PhaseType[];
        errors: string[];
    };
    private buildPipelineResult;
    private traceDataFlow;
    private withTimeout;
    private delay;
}

// ---- src/agents/rust-verification-agent.d.ts ----
/**
 * Enhanced Rust Formal Verification Agent
 * Phase 2 of Issue #33: Advanced Rust formal verification with Prusti, Kani, and CBMC
 */
export interface RustVerificationRequest {
    projectPath: string;
    sourceFiles: RustSourceFile[];
    verificationTools: VerificationTool[];
    options: VerificationOptions;
}
export interface RustSourceFile {
    path: string;
    content: string;
    annotations?: RustAnnotation[];
}
export interface RustAnnotation {
    type: 'precondition' | 'postcondition' | 'invariant' | 'assert' | 'assume' | 'contract';
    line: number;
    content: string;
}
export type VerificationTool = 'prusti' | 'kani' | 'cbmc' | 'miri' | 'loom';
export interface VerificationOptions {
    timeout?: number;
    memoryLimit?: number;
    unwindLimit?: number;
    strictMode?: boolean;
    generateReport?: boolean;
    checkOverflow?: boolean;
    checkConcurrency?: boolean;
}
export interface RustVerificationResult {
    tool: VerificationTool;
    success: boolean;
    results: VerificationCheck[];
    performance: PerformanceMetrics;
    report?: VerificationReport;
    errors: VerificationError[];
    warnings: VerificationWarning[];
}
export interface VerificationCheck {
    type: 'safety' | 'liveness' | 'functional' | 'memory' | 'concurrency';
    description: string;
    status: 'passed' | 'failed' | 'timeout' | 'unknown';
    location?: SourceLocation;
    details?: string;
    counterexample?: string;
}
export interface PerformanceMetrics {
    executionTime: number;
    memoryUsage: number;
    codeSize: number;
    verificationComplexity: 'low' | 'medium' | 'high' | 'very-high';
}
export interface VerificationReport {
    summary: string;
    statistics: {
        totalChecks: number;
        passedChecks: number;
        failedChecks: number;
        coverage: number;
    };
    recommendations: string[];
    toolSpecificResults: Record<string, any>;
}
export interface VerificationError {
    tool: VerificationTool;
    type: string;
    message: string;
    location?: SourceLocation;
    severity: 'critical' | 'error' | 'warning';
}
export interface VerificationWarning {
    tool: VerificationTool;
    type: string;
    message: string;
    location?: SourceLocation;
    suggestion?: string;
}
export interface SourceLocation {
    file: string;
    line: number;
    column: number;
    function?: string;
}
export declare class RustVerificationAgent {
    private installedTools;
    constructor();
    /**
     * Main verification entry point - runs multiple verification tools
     */
    verifyRustProject(request: RustVerificationRequest): Promise<RustVerificationResult[]>;
    /**
     * Run Prusti verification (Rust ownership and borrowing verification)
     */
    private runPrustiVerification;
    /**
     * Run Kani verification (bounded model checking for Rust)
     */
    private runKaniVerification;
    /**
     * Run CBMC verification (bounded model checking)
     */
    private runCBMCVerification;
    /**
     * Run Miri verification (interpreter for unsafe Rust)
     */
    private runMiriVerification;
    /**
     * Detect installed verification tools
     */
    private detectInstalledTools;
    private runVerificationTool;
    private runLoomVerification;
    private validateProjectStructure;
    private prepareProjectForVerification;
    private addAnnotationsToFile;
    private formatAnnotation;
    private parsePrustiOutput;
    private parseKaniOutput;
    private parseCBMCOutput;
    private parseMiriOutput;
    private estimateMemoryUsage;
    private calculateCodeSize;
    private assessComplexity;
    private generateCombinedReport;
    private generateSummary;
    /**
     * Get list of available verification tools
     */
    getAvailableTools(): VerificationTool[];
    /**
     * Check if a specific tool is available
     */
    isToolAvailable(tool: VerificationTool): boolean;
}

// ---- src/agents/task-types.d.ts ----
/**
 * Common types for Claude Code Task Tool integration
 */
export interface TaskRequest {
    description: string;
    prompt: string;
    subagent_type: string;
    context?: any;
}
export interface TaskResponse {
    summary: string;
    analysis: string;
    recommendations: string[];
    nextActions: string[];
    warnings: string[];
    shouldBlockProgress: boolean;
}
export interface TaskHandler {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance?: (context: ProactiveGuidanceContext) => Promise<ProactiveGuidanceResult>;
}
export interface ProactiveGuidanceContext {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
}
export interface ProactiveGuidanceResult {
    shouldIntervene: boolean;
    intervention: {
        type: 'warning' | 'suggestion' | 'block';
        message: string;
        recommendedActions: string[];
    };
}

// ---- src/agents/tdd-agent.d.ts ----
/**
 * TDD Agent for Claude Code
 *
 * This agent provides intelligent TDD guidance and enforcement specifically
 * designed for Claude Code's Task tool and workflow integration.
 */
export interface TDDAgentConfig {
    strictMode: boolean;
    coverageThreshold: number;
    testFramework: 'vitest' | 'jest' | 'mocha';
    blockCodeWithoutTests: boolean;
    enableRealTimeGuidance: boolean;
}
export interface TDDContext {
    projectPath: string;
    currentPhase: string;
    feature?: string;
    lastAction?: string;
    testResults?: TestResults;
}
export interface TestResults {
    passed: number;
    failed: number;
    coverage: number;
    errors: string[];
}
export interface TDDTask {
    type: 'validate' | 'guide' | 'enforce' | 'analyze';
    description: string;
    priority: 'high' | 'medium' | 'low';
    action: string;
    expectedOutcome: string;
}
export declare class TDDAgent {
    private config;
    private context;
    constructor(config: TDDAgentConfig, context: TDDContext);
    /**
     * Main entry point for TDD guidance requests
     * Designed to be called by Claude Code's Task tool
     */
    provideTDDGuidance(request: string): Promise<{
        analysis: string;
        tasks: TDDTask[];
        nextSteps: string[];
        warnings: string[];
    }>;
    /**
     * Real-time TDD enforcement during development
     * Called when Claude Code detects code changes
     */
    enforceRealTimeTDD(event: {
        type: 'file_created' | 'file_modified' | 'test_run';
        file?: string;
        content?: string;
    }): Promise<{
        shouldBlock: boolean;
        message: string;
        correctionTasks: TDDTask[];
    }>;
    /**
     * Generate step-by-step TDD guidance for a specific feature
     */
    generateFeatureTDDPlan(feature: string): Promise<{
        phases: Array<{
            name: string;
            description: string;
            tasks: TDDTask[];
            validationCriteria: string[];
        }>;
        riskFactors: string[];
        estimatedEffort: string;
    }>;
    /**
     * Intelligent test suggestion based on code analysis
     */
    suggestTestsForCode(codeFile: string, codeContent: string): Promise<{
        testFile: string;
        testContent: string;
        testCases: Array<{
            name: string;
            description: string;
            importance: 'critical' | 'important' | 'nice-to-have';
            template: string;
        }>;
    }>;
    /**
     * Continuous TDD compliance monitoring
     */
    monitorTDDCompliance(): Promise<{
        complianceScore: number;
        violations: Array<{
            type: string;
            severity: 'error' | 'warning' | 'info';
            description: string;
            recommendation: string;
            autoFixAvailable: boolean;
        }>;
        trends: {
            improving: boolean;
            recentViolations: number;
            coverageTrend: 'up' | 'down' | 'stable';
        };
    }>;
    private analyzeCurrentState;
    private generateTDDTasks;
    private generateNextSteps;
    private identifyWarnings;
    private formatAnalysis;
    private handleFileCreation;
    private handleFileModification;
    private handleTestRun;
    private generateRedPhaseTasks;
    private generateGreenPhaseTasks;
    private generateRefactorPhaseTasks;
    private identifyRiskFactors;
    private estimateEffort;
    private analyzeCodeStructure;
    private generateTestFilePath;
    private generateTestCases;
    private generateTestFileContent;
    private checkForCorrespondingTest;
    private detectViolations;
    private calculateComplianceScore;
    private analyzeTrends;
}

// ---- src/agents/tdd-task-adapter.d.ts ----
/**
 * TDD Task Adapter for Claude Code
 *
 * This adapter integrates TDD guidance with Claude Code's Task tool,
 * enabling seamless TDD workflow integration and proactive assistance.
 */
export interface TaskRequest {
    description: string;
    prompt: string;
    subagent_type: string;
}
export interface TaskResponse {
    summary: string;
    analysis: string;
    recommendations: string[];
    nextActions: string[];
    warnings: string[];
    shouldBlockProgress: boolean;
}
export declare class TDDTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for TDD-related tasks from Claude Code
     */
    handleTDDTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive TDD suggestions for Claude Code's autonomous operation
     */
    provideProviacticeGuidance(context: {
        recentFiles: string[];
        recentActions: string[];
        userIntent: string;
    }): Promise<{
        shouldIntervene: boolean;
        intervention: {
            type: 'warning' | 'suggestion' | 'block';
            message: string;
            recommendedActions: string[];
        };
    }>;
    private handleFeatureImplementation;
    private handleTDDValidation;
    private handleDevelopmentGuidance;
    private handleComplianceEnforcement;
    private handleCodeAnalysis;
    private handleGenericTDDGuidance;
    private classifyTask;
    private extractFeatureName;
    private extractFilePath;
    private detectCurrentPhase;
    private analyzeRecentActivity;
}
export declare const createTDDTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};

// ---- src/agents/test-generation-agent.d.ts ----
/**
 * Test Generation Agent
 * 自動的にテストケースを生成し、包括的なテスト戦略を提供
 */
export interface TestGenerationRequest {
    feature: string;
    requirements?: string[];
    codeFile?: string;
    testFramework: 'vitest' | 'jest' | 'mocha' | 'exunit';
}
export interface GeneratedTest {
    testFile: string;
    testContent: string;
    testCases: TestCase[];
    coverage: TestCoverage;
    recommendations: string[];
}
export interface TestCase {
    name: string;
    type: 'unit' | 'integration' | 'e2e' | 'property' | 'contract';
    description: string;
    priority: 'critical' | 'high' | 'medium' | 'low';
    code: string;
    dataGenerators?: PropertyGenerator[];
}
export interface PropertyGenerator {
    name: string;
    type: string;
    constraints: string[];
    generator: string;
}
export interface TestCoverage {
    functional: string[];
    edgeCases: string[];
    errorHandling: string[];
    performance: string[];
    security: string[];
}
export declare class TestGenerationAgent {
    /**
     * 要件からテストケースを自動生成
     */
    generateTestsFromRequirements(request: TestGenerationRequest): Promise<GeneratedTest>;
    /**
     * コードからテストを逆生成（リバースTDD）
     */
    generateTestsFromCode(codeFile: string): Promise<GeneratedTest>;
    /**
     * Property-Based Testing の自動設計
     */
    generatePropertyTests(contract: {
        function: string;
        inputs: Array<{
            name: string;
            type: string;
            constraints?: string[];
        }>;
        outputs: {
            type: string;
            constraints?: string[];
        };
        invariants: string[];
    }): Promise<TestCase[]>;
    /**
     * BDD シナリオの自動生成
     */
    generateBDDScenarios(userStory: {
        title: string;
        asA: string;
        iWant: string;
        soThat: string;
        acceptanceCriteria: string[];
    }): Promise<string>;
    /**
     * 統合テスト戦略の立案
     */
    planIntegrationTests(architecture: {
        services: Array<{
            name: string;
            dependencies: string[];
        }>;
        dataFlow: Array<{
            from: string;
            to: string;
            data: string;
        }>;
    }): Promise<{
        testPlan: IntegrationTestPlan;
        mockStrategy: MockStrategy;
        testOrder: string[];
    }>;
    /**
     * セキュリティテストの自動生成
     */
    generateSecurityTests(endpoint: {
        path: string;
        method: string;
        authentication: boolean;
        authorization?: string[];
        inputs: any[];
    }): Promise<TestCase[]>;
    /**
     * パフォーマンステストの設計
     */
    designPerformanceTests(sla: {
        responseTime: number;
        throughput: number;
        concurrentUsers: number;
        availability: number;
    }): Promise<{
        loadTests: LoadTest[];
        stressTests: StressTest[];
        spikeTests: SpikeTest[];
        soakTests: SoakTest[];
    }>;
    private analyzeAndGenerateTestCases;
    private analyzeCode;
    private generateTestFileContent;
    private generateExUnitTestContent;
    private convertToExUnitTest;
    private toElixirModuleName;
    private generatePropertyTestCode;
    private generateArbitrary;
    private extractFunctions;
    private extractClasses;
    private calculateComplexity;
    private generateImports;
    private determineTestFilePath;
    private analyzeCoverage;
    private generateRecommendations;
    private identifyEdgeCases;
    private generateHappyPathTest;
    private generateErrorHandlingTest;
    private generateEdgeCaseTest;
    private generateTestCasesFromAnalysis;
    private generateCodeBasedRecommendations;
    private createDataGenerators;
    private detectEdgeCaseProperties;
    private criteriaToScenario;
    private generateEdgeCaseScenarios;
    private identifyCriticalPaths;
    private identifyIntegrationPoints;
    private generateUnitIntegrationTests;
    private generateServiceIntegrationTests;
    private generateE2ETests;
    private calculateIntegrationCoverage;
    private determineMockStrategy;
    private optimizeTestExecutionOrder;
    private generateInjectionTest;
    private generateAuthenticationTest;
    private generateAuthorizationTest;
    private generateXSSTest;
    private generateCSRFTest;
    private generateFuzzingTest;
    private generateLoadTests;
    private generateStressTests;
    private generateSpikeTests;
    private generateSoakTests;
    private inferFeatureName;
    private extractDependencies;
    private detectPatterns;
    private invariantToAssertion;
    private applyConstraint;
}
interface IntegrationTestPlan {
    phases: Array<{
        name: string;
        tests: any[];
    }>;
    coverage: number;
}
interface MockStrategy {
    approach: 'full' | 'partial' | 'none';
    mocks: Array<{
        service: string;
        type: string;
    }>;
}
interface LoadTest {
    name: string;
    duration: number;
    users: number;
    rampUp: number;
}
interface StressTest extends LoadTest {
    breakingPoint: boolean;
}
interface SpikeTest extends LoadTest {
    spikeMultiplier: number;
}
interface SoakTest extends LoadTest {
    sustainedDuration: number;
}
export {};

// ---- src/agents/unified-agent.d.ts ----
/**
 * @fileoverview Unified Agent Implementation
 * Phase 2: Agent System Refactoring - Core unified agent architecture
 * Implements domain modeling and TDD as specified in ae-framework-v2.yml
 */
import { AgentTask, TaskResult, AgentConfig, AgentState, AgentContext } from './domain-types.js';
/**
 * Unified Agent class implementing domain model architecture
 * Replaces all individual agent types with a single unified approach
 */
export declare class UnifiedAgent {
    private config;
    private state;
    private phaseStateManager;
    private steeringLoader;
    constructor(config: AgentConfig);
    /**
     * Initialize agent for operation
     */
    initialize(): Promise<void>;
    /**
     * Core task processing method - unified interface for all task types
     */
    processTask(task: AgentTask): Promise<TaskResult>;
    /**
     * Execute task based on type - unified implementation
     */
    private executeTaskByType;
    /**
     * Handle code generation tasks
     */
    private handleCodeGeneration;
    /**
     * Handle test generation tasks
     */
    private handleTestGeneration;
    /**
     * Handle validation tasks
     */
    private handleValidation;
    /**
     * Handle quality assurance tasks
     */
    private handleQualityAssurance;
    /**
     * Handle phase validation tasks
     */
    private handlePhaseValidation;
    /**
     * Handle intent analysis tasks
     */
    private handleIntentAnalysis;
    /**
     * Handle formal specification tasks
     */
    private handleFormalSpecification;
    /**
     * Handle verification tasks
     */
    private handleVerification;
    /**
     * Handle deployment tasks
     */
    private handleDeployment;
    /**
     * Handle generic tasks
     */
    private handleGenericTask;
    /**
     * Validate task result against acceptance criteria
     */
    private validateTaskResult;
    /**
     * Update internal metrics after task completion
     */
    private updateTaskMetrics;
    /**
     * Log activity to phase state manager
     */
    private logActivity;
    getType(): string;
    getCapabilities(): string[];
    getContext(): AgentContext;
    getState(): AgentState;
}

// ---- src/agents/user-stories-task-adapter.d.ts ----
/**
 * User Stories Task Adapter for Claude Code
 *
 * This adapter integrates Phase 3 (User Stories Creation) processing
 * with Claude Code's Task tool, enabling seamless user story generation,
 * validation, and management workflows.
 */
import { TaskRequest, TaskResponse } from './task-types.js';
export interface UserStory {
    id: string;
    title: string;
    description: string;
    asA: string;
    iWant: string;
    soThat: string;
    acceptanceCriteria: string[];
    priority: 'high' | 'medium' | 'low';
    storyPoints: number;
    epic?: string;
    dependencies: string[];
    testScenarios: string[];
}
export interface UserStorySet {
    stories: UserStory[];
    epics: string[];
    totalStoryPoints: number;
    completenessScore: number;
    gaps: string[];
    conflicts: string[];
}
export declare class UserStoriesTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for User Stories tasks from Claude Code
     */
    handleUserStoriesTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive user story guidance for Claude Code
     */
    provideProactiveGuidance(context: {
        recentFiles: string[];
        recentActions: string[];
        userIntent: string;
    }): Promise<{
        shouldIntervene: boolean;
        intervention: {
            type: 'warning' | 'suggestion' | 'block';
            message: string;
            recommendedActions: string[];
        };
    }>;
    private handleStoryGeneration;
    private handleStoryValidation;
    private handleStoryPrioritization;
    private handleStoryEstimation;
    private handleAcceptanceCriteriaCreation;
    private handleEpicOrganization;
    private handleDependencyIdentification;
    private handleGenericStoryProcessing;
    private classifyTask;
    private extractRequirementsInput;
    private extractStoriesInput;
    private extractStoryInput;
    generateUserStories(input: string): Promise<UserStorySet>;
    private validateUserStories;
    private prioritizeUserStories;
    private estimateUserStories;
    private createAcceptanceCriteria;
    private organizeStoriesIntoEpics;
    private identifyStoryDependencies;
    private performGenericStoryAnalysis;
    private analyzeRecentActivity;
}
export declare const createUserStoriesTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};

// ---- src/agents/validation-task-adapter.d.ts ----
/**
 * Validation Task Adapter for Claude Code
 *
 * This adapter integrates Phase 4 (Validation) processing with Claude Code's
 * Task tool, enabling seamless validation workflows for requirements,
 * user stories, specifications, and code quality.
 */
import { TaskRequest, TaskResponse } from './task-types.js';
export interface ValidationResult {
    isValid: boolean;
    score: number;
    issues: ValidationIssue[];
    recommendations: string[];
    coverageReport: CoverageReport;
}
export interface ValidationIssue {
    id: string;
    type: 'error' | 'warning' | 'info';
    severity: 'critical' | 'high' | 'medium' | 'low';
    category: string;
    description: string;
    location?: string;
    suggestion?: string;
}
export interface CoverageReport {
    functional: number;
    nonFunctional: number;
    business: number;
    technical: number;
    overall: number;
}
export declare class ValidationTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for Validation tasks from Claude Code
     */
    handleValidationTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive validation guidance for Claude Code
     */
    provideProactiveGuidance(context: {
        recentFiles: string[];
        recentActions: string[];
        userIntent: string;
    }): Promise<{
        shouldIntervene: boolean;
        intervention: {
            type: 'warning' | 'suggestion' | 'block';
            message: string;
            recommendedActions: string[];
        };
    }>;
    private handleRequirementsValidation;
    private handleUserStoriesValidation;
    private handleSpecificationValidation;
    private handleTraceabilityValidation;
    private handleCompletenessValidation;
    private handleConsistencyValidation;
    private handleFeasibilityValidation;
    private handleCrossValidation;
    private handleGenericValidation;
    private classifyTask;
    private extractRequirementsInput;
    private extractStoriesInput;
    private extractSpecificationInput;
    private extractTraceabilityInput;
    private extractCompletenessInput;
    private extractConsistencyInput;
    private extractFeasibilityInput;
    private extractCrossValidationInput;
    private extractGenericInput;
    private validateRequirements;
    validateUserStories(input: any): Promise<any>;
    private validateSpecifications;
    private validateTraceability;
    private validateCompleteness;
    private validateConsistency;
    private validateFeasibility;
    private performCrossValidation;
    private performGenericValidation;
    private analyzeRecentActivity;
}
export declare const createValidationTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};

// ---- src/agents/verify-agent.d.ts ----
/**
 * Verify Agent
 * Phase 5 of ae-framework: Automated verification and quality assurance
 */
export interface VerificationRequest {
    codeFiles: CodeFile[];
    testFiles: TestFile[];
    specifications?: Specification[];
    verificationTypes: VerificationType[];
    strictMode?: boolean;
    containerConfig?: {
        enabled: boolean;
        preferredEngine?: 'docker' | 'podman';
        buildImages?: boolean;
        projectPath?: string;
    };
}
export interface CodeFile {
    path: string;
    content: string;
    language: string;
}
export interface TestFile {
    path: string;
    content: string;
    type: 'unit' | 'integration' | 'e2e' | 'property' | 'contract';
}
export interface Specification {
    type: 'openapi' | 'asyncapi' | 'graphql' | 'tla' | 'alloy';
    content: string;
    path: string;
}
export type VerificationType = 'tests' | 'coverage' | 'linting' | 'typechecking' | 'security' | 'performance' | 'accessibility' | 'contracts' | 'specifications' | 'mutations' | 'rust-verification' | 'container-verification';
export interface VerificationResult {
    passed: boolean;
    results: VerificationCheck[];
    coverage: CoverageReport;
    metrics: QualityMetrics;
    issues: Issue[];
    suggestions: string[];
    traceability: TraceabilityMatrix;
}
export interface VerificationCheck {
    type: VerificationType;
    passed: boolean;
    details: any;
    errors?: string[];
    warnings?: string[];
}
export interface TestResult {
    total: number;
    passed: number;
    failed: number;
    duration: number;
    failures: Array<{
        message: string;
        fullTitle?: string;
    }>;
}
export interface LintResult {
    errors: number;
    warnings: number;
    messages: Array<{
        severity: 'error' | 'warning';
        message: string;
        line?: number;
        column?: number;
    }>;
}
export interface BenchmarkResult {
    responseTime: number;
    throughput: number;
    errorRate: number;
    cpuUsage: number;
    memoryUsage: number;
}
export interface CoverageReport {
    line: number;
    branch: number;
    function: number;
    statement: number;
    uncoveredFiles: string[];
}
export interface QualityMetrics {
    complexity: number;
    maintainability: number;
    reliability: number;
    security: number;
    performance: number;
    testability: number;
}
export interface Issue {
    severity: 'critical' | 'high' | 'medium' | 'low';
    type: string;
    file: string;
    line?: number;
    message: string;
    fix?: string;
}
export interface TraceabilityMatrix {
    requirements: TraceItem[];
    specifications: TraceItem[];
    tests: TraceItem[];
    code: TraceItem[];
    coverage: number;
}
export interface TraceItem {
    id: string;
    description: string;
    linkedTo: string[];
    covered: boolean;
}
export declare class VerifyAgent {
    private rustVerificationAgent;
    private containerAgent?;
    constructor(options?: {
        enableContainers?: boolean;
        containerConfig?: any;
    });
    /**
     * Run comprehensive verification suite
     */
    runFullVerification(request: VerificationRequest): Promise<VerificationResult>;
    /**
     * Run specific verification type
     */
    private runVerification;
    /**
     * Run all tests
     */
    runTests(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Check code coverage
     */
    checkCoverage(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run linting checks
     */
    runLinting(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run type checking
     */
    runTypeChecking(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run security checks
     */
    runSecurityChecks(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run performance tests
     */
    runPerformanceTests(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Check accessibility
     */
    checkAccessibility(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Verify contracts
     */
    verifyContracts(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Verify specifications
     */
    verifySpecifications(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run mutation testing
     */
    runMutationTesting(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Generate coverage report
     */
    generateCoverageReport(request: VerificationRequest): Promise<CoverageReport>;
    /**
     * Calculate quality metrics
     */
    calculateQualityMetrics(request: VerificationRequest): Promise<QualityMetrics>;
    /**
     * Build traceability matrix
     */
    buildTraceabilityMatrix(request: VerificationRequest): Promise<TraceabilityMatrix>;
    /**
     * Run Rust formal verification
     */
    runRustVerification(request: VerificationRequest): Promise<VerificationCheck>;
    /**
     * Run container-based verification
     */
    private runContainerVerification;
    /**
     * Generate improvement suggestions
     */
    private generateSuggestions;
    private runTestFile;
    private lintFile;
    private checkTypes;
    private scanForVulnerabilities;
    private checkDependencies;
    private scanForSecrets;
    private runBenchmarks;
    private runContractTest;
    private validateSpecification;
    private generateMutants;
    private testMutant;
    private extractRequirements;
    private calculateTraceabilityCoverage;
    private findRustProjectPath;
    private findElixirProjectPath;
    private detectProjectLanguage;
    private selectVerificationTools;
}

// ---- src/analysis/dependency-analyzer.d.ts ----
/**
 * Dependency Analyzer for Phase 3.1 Implementation
 * Analyzes project dependencies, module relationships, and impact scope
 */
import { EventEmitter } from 'events';
import type { DependencyGraph, ImpactAnalysis, DependencyNode } from '../engines/sequential-inference-engine.js';
export interface CircularDependency {
    id: string;
    cycle: string[];
    severity: 'warning' | 'error' | 'critical';
    description: string;
    suggestions: string[];
    affectedComponents: string[];
}
export interface DependencyAnalysisRequest {
    id: string;
    projectRoot: string;
    targetFiles?: string[];
    analysisScope: 'project' | 'module' | 'file' | 'function';
    includeExternal: boolean;
    maxDepth?: number;
    excludePatterns?: string[];
    analysisTypes: DependencyAnalysisType[];
}
export type DependencyAnalysisType = 'structural' | 'functional' | 'circular' | 'impact' | 'risk' | 'optimization' | 'security' | 'performance';
export interface DependencyAnalysisResult {
    requestId: string;
    graph: DependencyGraph;
    nodes: DependencyNode[];
    circularDependencies: CircularDependency[];
    metrics: DependencyMetrics;
    riskAssessment: DependencyRiskAssessment;
    recommendations: DependencyRecommendation[];
    impactAnalysis?: ImpactAnalysis;
    optimizationSuggestions: OptimizationSuggestion[];
}
export interface DependencyMetrics {
    totalNodes: number;
    totalEdges: number;
    averageDependencies: number;
    maxDependencyDepth: number;
    circularDependencyCount: number;
    criticalPathLength: number;
    modularityScore: number;
    cohesionScore: number;
    couplingScore: number;
    stabilityIndex: number;
}
export interface DependencyRiskAssessment {
    overallRisk: 'low' | 'medium' | 'high' | 'critical';
    riskFactors: RiskFactor[];
    vulnerabilities: Vulnerability[];
    mitigationPlan: MitigationStep[];
    contingencyActions: string[];
}
export interface RiskFactor {
    id: string;
    type: 'circular' | 'deep_nesting' | 'high_coupling' | 'single_point_failure' | 'external_dependency';
    severity: 'low' | 'medium' | 'high' | 'critical';
    description: string;
    affectedComponents: string[];
    probability: number;
    impact: number;
    mitigation: string;
}
export interface Vulnerability {
    id: string;
    type: 'security' | 'performance' | 'maintenance' | 'scalability';
    description: string;
    cveId?: string;
    severity: 'low' | 'medium' | 'high' | 'critical';
    affectedVersions?: string[];
    fixVersion?: string;
    workaround?: string;
}
export interface MitigationStep {
    id: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    action: string;
    estimatedEffort: number;
    dependencies: string[];
    timeline: string;
    owner?: string;
}
export interface DependencyRecommendation {
    id: string;
    type: 'refactor' | 'upgrade' | 'remove' | 'replace' | 'optimize';
    priority: 'low' | 'medium' | 'high' | 'critical';
    title: string;
    description: string;
    benefits: string[];
    risks: string[];
    effort: 'low' | 'medium' | 'high';
    timeline: string;
}
export interface OptimizationSuggestion {
    id: string;
    category: 'performance' | 'maintainability' | 'security' | 'scalability';
    title: string;
    description: string;
    currentState: string;
    proposedState: string;
    expectedBenefit: string;
    implementationComplexity: 'low' | 'medium' | 'high';
    prerequisites: string[];
}
export interface ImpactAnalysisRequest {
    id: string;
    changes: ChangeRequest[];
    analysisDepth: 'immediate' | 'extended' | 'comprehensive';
    includeRiskAssessment: boolean;
    testSuggestions: boolean;
}
export interface ChangeRequest {
    type: 'create' | 'modify' | 'delete' | 'rename';
    target: string;
    description: string;
    estimatedSize: 'small' | 'medium' | 'large';
}
export declare class DependencyAnalyzer extends EventEmitter {
    private options;
    private inferenceEngine;
    private problemDecomposer;
    private activeAnalyses;
    private cache;
    constructor(options?: {
        cacheSize?: number;
        cacheTTL?: number;
        maxConcurrentAnalyses?: number;
        enableRealTimeMonitoring?: boolean;
    });
    /**
     * Analyze project dependencies with comprehensive analysis
     */
    analyzeDependencies(request: DependencyAnalysisRequest): Promise<DependencyAnalysisResult>;
    /**
     * Perform impact analysis for potential changes
     */
    analyzeImpact(request: ImpactAnalysisRequest): Promise<ImpactAnalysis>;
    private validateAnalysisRequest;
    private createAnalysisProblem;
    private createAnalysisQuery;
    private buildDependencyGraph;
    private detectCircularDependencies;
    private calculateDependencyMetrics;
    private assessRisks;
    private determineAnalysisComplexity;
    private generateCacheKey;
    private isCacheValid;
    private cleanupCache;
    private generateNodeId;
    private extractFileName;
    private inferNodeType;
    private estimateComplexity;
    private assessNodeImportance;
    private populateDependents;
    private buildEdges;
    private assessCycleSeverity;
    private generateCycleFixes;
    private findAffectedComponents;
    private calculateMaxDepth;
    private findCriticalPath;
    private calculateModularityScore;
    private calculateCohesionScore;
    private calculateCouplingScore;
    private calculateStabilityIndex;
    private getModuleName;
    private calculateOverallRisk;
    private createMitigationPlan;
    private generateContingencyActions;
    private generateRecommendations;
    private generateOptimizationSuggestions;
    private performImpactAnalysis;
}

// ---- src/api/middleware/security-headers.d.ts ----
/**
 * Security Headers Middleware
 * Implements basic HTTP security headers for the AE-Framework API
 */
import { FastifyInstance } from 'fastify';
export interface SecurityHeadersOptions {
    /** Enable/disable all security headers */
    enabled?: boolean;
    /** Content Security Policy */
    contentSecurityPolicy?: {
        enabled?: boolean;
        directives?: string;
    };
    /** X-Frame-Options */
    frameOptions?: {
        enabled?: boolean;
        value?: 'DENY' | 'SAMEORIGIN' | string;
    };
    /** X-Content-Type-Options */
    contentTypeOptions?: {
        enabled?: boolean;
    };
    /** Referrer-Policy */
    referrerPolicy?: {
        enabled?: boolean;
        value?: string;
    };
    /** Strict-Transport-Security */
    strictTransportSecurity?: {
        enabled?: boolean;
        maxAge?: number;
        includeSubDomains?: boolean;
        preload?: boolean;
    };
    /** X-XSS-Protection */
    xssProtection?: {
        enabled?: boolean;
        value?: string;
    };
    /** Permissions-Policy */
    permissionsPolicy?: {
        enabled?: boolean;
        directives?: string;
    };
}
/**
 * Fastify plugin for security headers
 */
export declare function securityHeadersPlugin(fastify: FastifyInstance, options?: SecurityHeadersOptions): Promise<void>;
/**
 * Environment-specific security configurations
 */
export declare const securityConfigurations: {
    development: SecurityHeadersOptions;
    testing: SecurityHeadersOptions;
    production: SecurityHeadersOptions;
};
/**
 * Get security configuration for current environment
 */
export declare function getSecurityConfiguration(environment?: string): SecurityHeadersOptions;
export default securityHeadersPlugin;

// ---- src/api/routes/reservations.d.ts ----
import { FastifyInstance } from 'fastify';
import { InventoryService } from '../../domain/services.js';
export declare function reservationRoutes(fastify: FastifyInstance, options: {
    inventoryService: InventoryService;
}): Promise<void>;

// ---- src/api/server.d.ts ----
import Fastify, { FastifyInstance } from "fastify";
/**
 * Create and configure Fastify server instance
 */
export declare function createServer(): Promise<FastifyInstance>;
export default function getServer(): Promise<Fastify.FastifyInstance<Fastify.RawServerDefault, import("http").IncomingMessage, import("http").ServerResponse<import("http").IncomingMessage>, Fastify.FastifyBaseLogger, Fastify.FastifyTypeProviderDefault>>;

// ---- src/benchmark/req2run/config/default.d.ts ----
/**
 * Default Req2Run Benchmark Configuration
 * Provides sensible defaults for benchmark execution
 */
import { BenchmarkConfig, BenchmarkCategory, DifficultyLevel } from '../types/index.js';
export declare const DEFAULT_BENCHMARK_CONFIG: BenchmarkConfig;
/**
 * Get configuration for a specific difficulty level
 */
export declare function getConfigForDifficulty(difficulty: DifficultyLevel): Partial<BenchmarkConfig>;
/**
 * Get configuration for a specific category
 */
export declare function getConfigForCategory(category: BenchmarkCategory): Partial<BenchmarkConfig>;
/**
 * Create a minimal configuration for CI/CD environments
 */
export declare function getCIConfig(): BenchmarkConfig;

// ---- src/benchmark/req2run/examples/epic-integration-example.d.ts ----
/**
 * Req2Run-Benchmark EPIC Integration Example
 * Demonstrates Phase 1 implementation of Issue #155
 * Complete AE Framework benchmark evaluation using standardized pipeline
 */
/**
 * Example: Complete Req2Run-Benchmark EPIC Integration
 * Shows how the standardized AE Framework pipeline integrates with req2run-benchmark
 */
export declare function runBenchmarkEPICDemo(): Promise<void>;
/**
 * Example: CI/CD Integration Pattern
 */
export declare function demonstrateCICDIntegration(): Promise<void>;
/**
 * Example: Performance Regression Detection
 */
export declare function demonstratePerformanceRegression(): Promise<void>;
export default runBenchmarkEPICDemo;

// ---- src/benchmark/req2run/index.d.ts ----
/**
 * Req2Run Benchmark Integration - Main Entry Point
 *
 * This module provides the main exports for the AE Framework Req2Run benchmark integration.
 * It allows users to run comprehensive performance evaluations against the Req2Run benchmark
 * dataset, measuring the framework's ability to transform requirements into executable applications.
 *
 * @example
 * ```typescript
 * import { BenchmarkRunner, DEFAULT_BENCHMARK_CONFIG } from 'ae-framework/benchmark/req2run';
 *
 * const runner = new BenchmarkRunner(DEFAULT_BENCHMARK_CONFIG);
 * const result = await runner.runBenchmark('web-api-basic-001');
 * console.log(`Score: ${result.metrics.overallScore}/100`);
 * ```
 *
 * @see https://github.com/itdojp/req2run-benchmark
 * @see https://github.com/itdojp/ae-framework/issues/155
 */
export { BenchmarkRunner } from './runners/BenchmarkRunner.js';
export { DEFAULT_BENCHMARK_CONFIG, getConfigForDifficulty, getConfigForCategory, getCIConfig } from './config/default.js';
export * from './types/index.js';
export declare const BENCHMARK_VERSION = "1.0.0";
export declare const SUPPORTED_REQ2RUN_VERSION = "1.0.0";
/**
 * Quick start function for running basic benchmarks
 *
 * @param problemIds - Array of problem IDs to run, or 'basic' for basic difficulty problems
 * @param options - Optional configuration overrides
 * @returns Promise<BenchmarkResult[]>
 *
 * @example
 * ```typescript
 * // Run basic problems
 * const results = await quickBenchmark('basic');
 *
 * // Run specific problems
 * const results = await quickBenchmark(['web-api-basic-001', 'cli-tool-basic-001']);
 * ```
 */
export declare function quickBenchmark(problemIds: string[] | 'basic' | 'intermediate' | 'advanced' | 'expert', options?: Partial<import('./types/index.js').BenchmarkConfig>): Promise<import('./types/index.js').BenchmarkResult[]>;
/**
 * Utility function to create a CI-optimized benchmark runner
 *
 * @example
 * ```typescript
 * const results = await createCIBenchmark().runBenchmarks(['basic-problem-001']);
 * ```
 */
export declare function createCIBenchmark(): any;
/**
 * Get benchmark metadata and system information
 */
export declare function getBenchmarkInfo(): Promise<{
    version: string;
    supportedReq2RunVersion: string;
    availableProblems: number;
    categories: string[];
    difficulties: string[];
    systemInfo: any;
}>;

// ---- src/benchmark/req2run/runners/BenchmarkRunner.d.ts ----
/**
 * Req2Run Benchmark Runner
 * Orchestrates the execution of AE Framework against Req2Run benchmark problems
 */
import { BenchmarkResult, BenchmarkConfig } from '../types/index.js';
export declare class BenchmarkRunner {
    private config;
    private intentAgent;
    private nlpAgent;
    private storiesAgent;
    private validationAgent;
    private domainAgent;
    constructor(config: BenchmarkConfig);
    /**
     * Run a single benchmark problem
     */
    runBenchmark(problemId: string): Promise<BenchmarkResult>;
    /**
     * Run multiple benchmark problems
     */
    runBenchmarks(problemIds: string[]): Promise<BenchmarkResult[]>;
    /**
     * Execute a single phase with error handling and metrics collection
     */
    private executePhase;
    /**
     * Initialize AE Framework agents
     */
    private initializeAgents;
    /**
     * Load problem specification from Req2Run repository
     */
    private loadProblemSpec;
    /**
     * Placeholder for UI/UX generation phase
     */
    private generateUIUX;
    /**
     * Evaluate the generated application against the problem specification
     */
    private evaluateResult;
    /**
     * Collect generated artifacts from the application
     */
    private collectArtifacts;
    /**
     * Get execution environment information
     */
    private getExecutionEnvironment;
    /**
     * Get input for a specific phase
     */
    private getPhaseInput;
    /**
     * Initialize empty artifacts structure
     */
    private initializeArtifacts;
    /**
     * Get default metrics for failed executions
     */
    private getDefaultMetrics;
    /**
     * Split array into chunks of specified size
     */
    private chunkArray;
    /**
     * Generate detailed benchmark report
     */
    private generateReport;
    /**
     * Generate Markdown report
     */
    private generateMarkdownReport;
}

// ---- src/benchmark/req2run/runners/StandardizedBenchmarkRunner.d.ts ----
/**
 * Standardized Req2Run Benchmark Runner
 * Uses the new AE Framework standardized pipeline for consistent benchmark execution
 * This replaces the original BenchmarkRunner with standardized interfaces
 */
import { BenchmarkResult, BenchmarkConfig } from '../types/index.js';
/**
 * Standardized Benchmark Runner
 * Leverages the AE Framework standardized pipeline for consistent, maintainable benchmark execution
 */
export declare class StandardizedBenchmarkRunner {
    private config;
    private pipeline;
    constructor(config: BenchmarkConfig);
    /**
     * Run a single benchmark problem using standardized pipeline
     */
    runBenchmark(problemId: string): Promise<BenchmarkResult>;
    /**
     * Run multiple benchmark problems with standardized pipeline
     */
    runBenchmarks(problemIds: string[]): Promise<BenchmarkResult[]>;
    /**
     * Get pipeline capabilities and health status
     */
    getPipelineStatus(): {
        capabilities: Record<string, any>;
        validation: {
            valid: boolean;
            missing: string[];
            errors: string[];
        };
        health: 'healthy' | 'degraded' | 'failed';
    };
    /**
     * Initialize standardized AE Framework pipeline
     */
    private initializePipeline;
    /**
     * Load and parse problem specification from req2run-benchmark
     */
    private loadProblemSpec;
    /**
     * Normalize req2run specification to AE Framework format
     */
    private normalizeSpecification;
    /**
     * Convert req2run spec to standardized pipeline input
     */
    private convertToStandardInput;
    /**
     * Convert pipeline result to benchmark result format
     */
    private convertToBenchmarkResult;
    /**
     * Calculate comprehensive benchmark metrics from pipeline results
     */
    private calculateBenchmarkMetrics;
    /**
     * Generate comprehensive benchmark report with enhanced analytics
     */
    private generateComprehensiveReport;
    private buildDescription;
    private extractRequirements;
    private extractConstraints;
    private buildSpecificationContent;
    private mapStandardPhaseToLegacy;
    private extractPhaseInput;
    private extractGeneratedArtifacts;
    private generateSourceCodeFromUI;
    private generateComponentCode;
    private generateDocumentationFromPipeline;
    private generateREADME;
    private generateConfigurationFiles;
    private assessFunctionalCoverage;
    private assessCodeQuality;
    private calculatePerformanceScore;
    private calculateThroughput;
    private generateAnalytics;
    private calculateAveragePhaseTime;
    private analyzeErrorsByPhase;
    private identifyCommonErrors;
    private generateEnhancedMarkdownReport;
    private generateCSVReport;
    private buildErrorResult;
    private getExecutionEnvironment;
    private getSimpleEnvironment;
    private initializeArtifacts;
    private getDefaultMetrics;
    private chunkArray;
}

// ---- src/benchmark/req2run/types/index.d.ts ----
/**
 * Req2Run Benchmark Integration Types
 * Core type definitions for benchmark execution and evaluation
 */
export interface RequirementSpec {
    id: string;
    title: string;
    description: string;
    category: BenchmarkCategory;
    difficulty: DifficultyLevel;
    requirements: string[];
    constraints: {
        business?: string[];
        performance?: any;
    };
    testCriteria: TestCriteria[];
    expectedOutput: ExpectedOutput;
    timeLimit?: number;
    resourceLimits?: ResourceLimits;
    metadata: {
        created_by: string;
        created_at: string;
        category: string;
        difficulty: string;
        estimated_time?: number;
    };
}
export interface BenchmarkResult {
    problemId: string;
    timestamp: Date;
    success: boolean;
    metrics: BenchmarkMetrics;
    executionDetails: ExecutionDetails;
    generatedArtifacts: GeneratedArtifacts;
    errors?: BenchmarkError[];
}
export interface BenchmarkMetrics {
    overallScore: number;
    functionalCoverage: number;
    testPassRate: number;
    performance: PerformanceMetrics;
    codeQuality: QualityMetrics;
    security: SecurityMetrics;
    timeToCompletion: number;
    resourceUsage: ResourceMetrics;
    phaseMetrics: PhaseMetrics[];
}
export interface PerformanceMetrics {
    responseTime: number;
    throughput: number;
    memoryUsage: number;
    cpuUsage: number;
    diskUsage: number;
    networkLatency?: number;
}
export interface QualityMetrics {
    codeComplexity: number;
    maintainabilityIndex: number;
    testCoverage: number;
    duplicationRatio: number;
    lintScore: number;
    typeScriptErrors: number;
}
export interface SecurityMetrics {
    vulnerabilityCount: number;
    securityScore: number;
    owaspCompliance: number;
    dependencyVulnerabilities: number;
    secretsExposed: number;
    securityHeaders: number;
}
export interface ResourceMetrics {
    maxMemoryUsage: number;
    avgCpuUsage: number;
    diskIO: number;
    networkIO: number;
    buildTime: number;
    deploymentTime: number;
}
export interface PhaseMetrics {
    phase: AEFrameworkPhase;
    duration: number;
    success: boolean;
    outputQuality: number;
    resourceUsage: ResourceMetrics;
    errors?: string[];
}
export interface ExecutionDetails {
    startTime: Date;
    endTime: Date;
    totalDuration: number;
    phaseExecutions: PhaseExecution[];
    environment: ExecutionEnvironment;
    logs: ExecutionLog[];
}
export interface PhaseExecution {
    phase: AEFrameworkPhase;
    startTime: Date;
    endTime: Date;
    duration: number;
    input: any;
    output: any;
    success: boolean;
    errors?: string[];
}
export interface GeneratedArtifacts {
    sourceCode: SourceCodeArtifact[];
    documentation: DocumentationArtifact[];
    tests: TestArtifact[];
    configuration: ConfigurationArtifact[];
    deployment: DeploymentArtifact[];
}
export interface SourceCodeArtifact {
    filename: string;
    content: string;
    language: string;
    size: number;
    linesOfCode: number;
}
export interface TestCriteria {
    id: string;
    description: string;
    type: TestType;
    weight: number;
    automated: boolean;
}
export interface ExpectedOutput {
    type: OutputType;
    format: string;
    schema?: any;
    examples: any[];
}
export declare enum BenchmarkCategory {
    WEB_API = "web-api",
    CLI_TOOL = "cli-tool",
    DATA_PROCESSING = "data-processing",
    CRYPTOGRAPHY = "cryptography",
    NETWORK_PROTOCOL = "network-protocol",
    DATABASE = "database",
    MACHINE_LEARNING = "machine-learning",
    DISTRIBUTED_SYSTEM = "distributed-system",
    AUTHENTICATION = "authentication",
    FILE_PROCESSING = "file-processing",
    REAL_TIME = "real-time",
    MICROSERVICE = "microservice",
    MONITORING = "monitoring",
    DEVOPS = "devops",
    SECURITY = "security",
    PERFORMANCE = "performance"
}
export declare enum DifficultyLevel {
    BASIC = "basic",
    INTERMEDIATE = "intermediate",
    ADVANCED = "advanced",
    EXPERT = "expert"
}
export declare enum AEFrameworkPhase {
    INTENT_ANALYSIS = "intent-analysis",
    REQUIREMENTS = "requirements",
    USER_STORIES = "user-stories",
    VALIDATION = "validation",
    DOMAIN_MODELING = "domain-modeling",
    UI_UX_GENERATION = "ui-ux-generation"
}
export declare enum TestType {
    UNIT = "unit",
    INTEGRATION = "integration",
    E2E = "e2e",
    PERFORMANCE = "performance",
    SECURITY = "security",
    USABILITY = "usability"
}
export declare enum OutputType {
    APPLICATION = "application",
    API = "api",
    LIBRARY = "library",
    SERVICE = "service",
    TOOL = "tool"
}
export interface BenchmarkConfig {
    req2runRepository: string;
    problems: BenchmarkProblemConfig[];
    execution: ExecutionConfig;
    evaluation: EvaluationConfig;
    reporting: ReportingConfig;
}
export interface BenchmarkProblemConfig {
    id: string;
    enabled: boolean;
    timeoutMs: number;
    retries: number;
    category: BenchmarkCategory;
    difficulty: DifficultyLevel;
}
export interface ExecutionConfig {
    parallel: boolean;
    maxConcurrency: number;
    resourceLimits: ResourceLimits;
    environment: string;
    docker: DockerConfig;
}
export interface ResourceLimits {
    maxMemoryMB: number;
    maxCpuPercent: number;
    maxDiskMB: number;
    maxExecutionTimeMs: number;
}
export interface DockerConfig {
    enabled: boolean;
    image: string;
    volumes: string[];
    ports: number[];
}
export interface EvaluationConfig {
    weights: MetricWeights;
    thresholds: MetricThresholds;
    scoring: ScoringConfig;
}
export interface MetricWeights {
    functional: number;
    performance: number;
    quality: number;
    security: number;
    testing: number;
}
export interface MetricThresholds {
    minOverallScore: number;
    minFunctionalCoverage: number;
    maxResponseTime: number;
    minCodeQuality: number;
    maxVulnerabilities: number;
}
export interface ScoringConfig {
    algorithm: 'weighted-average' | 'weighted-geometric' | 'custom';
    penalties: PenaltyConfig;
    bonuses: BonusConfig;
}
export interface PenaltyConfig {
    timeoutPenalty: number;
    errorPenalty: number;
    qualityPenalty: number;
}
export interface BonusConfig {
    performanceBonus: number;
    qualityBonus: number;
    securityBonus: number;
}
export interface ReportingConfig {
    formats: ReportFormat[];
    destinations: ReportDestination[];
    dashboard: DashboardConfig;
}
export declare enum ReportFormat {
    JSON = "json",
    HTML = "html",
    PDF = "pdf",
    CSV = "csv",
    MARKDOWN = "markdown"
}
export interface ReportDestination {
    type: 'file' | 'github' | 'slack' | 'email' | 'webhook';
    config: any;
}
export interface DashboardConfig {
    enabled: boolean;
    port: number;
    refreshInterval: number;
    charts: ChartConfig[];
}
export interface ChartConfig {
    type: 'line' | 'bar' | 'pie' | 'radar';
    metrics: string[];
    title: string;
}
export interface BenchmarkError {
    phase: AEFrameworkPhase;
    type: 'timeout' | 'runtime' | 'validation' | 'resource' | 'network';
    message: string;
    stack?: string;
    timestamp: Date;
}
export interface ExecutionEnvironment {
    nodeVersion: string;
    platform: string;
    arch: string;
    memory: number;
    cpuCount: number;
    dockerVersion?: string;
    kubernetesVersion?: string;
}
export interface ExecutionLog {
    timestamp: Date;
    level: 'debug' | 'info' | 'warn' | 'error';
    phase: AEFrameworkPhase;
    message: string;
    data?: any;
}
export interface DocumentationArtifact {
    filename: string;
    content: string;
    type: 'readme' | 'api' | 'architecture' | 'deployment' | 'user-guide';
    format: 'markdown' | 'html' | 'pdf';
}
export interface TestArtifact {
    filename: string;
    content: string;
    type: TestType;
    coverage: number;
    passed: number;
    failed: number;
    skipped: number;
}
export interface ConfigurationArtifact {
    filename: string;
    content: string;
    type: 'package' | 'docker' | 'ci' | 'deployment' | 'environment';
}
export interface DeploymentArtifact {
    filename: string;
    content: string;
    type: 'docker' | 'kubernetes' | 'terraform' | 'helm' | 'compose';
}
export interface BenchmarkReport {
    summary: BenchmarkSummary;
    results: BenchmarkResult[];
    trends: BenchmarkTrend[];
    recommendations: string[];
    generatedAt: Date;
}
export interface BenchmarkSummary {
    totalProblems: number;
    completedProblems: number;
    successRate: number;
    averageScore: number;
    totalExecutionTime: number;
    bestCategory: BenchmarkCategory;
    worstCategory: BenchmarkCategory;
    improvements: ImprovementSuggestion[];
}
export interface BenchmarkTrend {
    date: Date;
    metrics: BenchmarkMetrics;
    version: string;
    changes: string[];
}
export interface ImprovementSuggestion {
    category: string;
    priority: 'high' | 'medium' | 'low';
    description: string;
    estimatedImpact: number;
    implementationEffort: 'easy' | 'medium' | 'hard';
}

// ---- src/cegis/auto-fix-engine.d.ts ----
/**
 * Auto-Fix Engine
 * Phase 2.1: Core engine for analyzing failures and applying automated fixes
 */
import { FailureArtifact, FixStrategy, FixResult, AutoFixConfig, AutoFixOptions, FailurePattern, FailureCategory } from './types.js';
export type { AutoFixOptions };
import { RiskAssessmentService } from './risk-assessment-service.js';
export declare class AutoFixEngine {
    private strategies;
    private riskAssessment;
    private config;
    constructor(config?: Partial<AutoFixConfig>, riskAssessment?: RiskAssessmentService);
    /**
     * Execute automatic fixes for the given failure artifacts
     */
    executeFixes(failures: FailureArtifact[], options?: AutoFixOptions): Promise<FixResult>;
    /**
     * Add a custom fix strategy
     */
    addStrategy(strategy: FixStrategy): void;
    /**
     * Get available strategies for a category
     */
    getStrategies(category: FailureCategory): FixStrategy[];
    /**
     * Analyze failure patterns to identify common issues
     */
    analyzeFailurePatterns(failures: FailureArtifact[]): Promise<FailurePattern[]>;
    private initializeDefaultStrategies;
    private filterValidFailures;
    private selectStrategies;
    private applyFixes;
    private applySingleStrategy;
    private applyAction;
    private backupFile;
    private groupByCategory;
    private findCommonPatterns;
    private getSuggestedStrategies;
    private calculatePatternConfidence;
    private generateSummary;
    private generateRecommendations;
    private generateReport;
}

// ---- src/cegis/failure-artifact-factory.d.ts ----
/**
 * Failure Artifact Factory
 * Phase 2.1: Factory for creating standardized failure artifacts
 */
import { FailureArtifact, CodeLocation } from './types.js';
export declare class FailureArtifactFactory {
    /**
     * Create failure artifact from a runtime error
     */
    static fromError(error: Error, location?: CodeLocation, context?: Record<string, any>): FailureArtifact;
    /**
     * Create failure artifact from test failure
     */
    static fromTestFailure(testName: string, expected: any, actual: any, location?: CodeLocation, testOutput?: string): FailureArtifact;
    /**
     * Create failure artifact from TypeScript compilation error
     */
    static fromTypeError(message: string, filePath: string, line: number, column: number, sourceCode?: string): FailureArtifact;
    /**
     * Create failure artifact from contract violation
     */
    static fromContractViolation(contractName: string, violationType: 'input' | 'output' | 'schema', actualData: any, location?: CodeLocation, expectedSchema?: string): FailureArtifact;
    /**
     * Create failure artifact from build error
     */
    static fromBuildError(message: string, command: string, exitCode: number, buildOutput: string, workingDirectory?: string): FailureArtifact;
    /**
     * Create failure artifact from lint error
     */
    static fromLintError(rule: string, message: string, filePath: string, line: number, column: number, severity?: 'error' | 'warning', sourceCode?: string): FailureArtifact;
    /**
     * Create failure artifact from dependency issue
     */
    static fromDependencyIssue(packageName: string, issueType: 'missing' | 'version_mismatch' | 'security_vulnerability' | 'deprecated', message: string, currentVersion?: string, requiredVersion?: string): FailureArtifact;
    /**
     * Create failure artifact from performance issue
     */
    static fromPerformanceIssue(metric: string, threshold: number, actual: number, location?: CodeLocation, context?: Record<string, any>): FailureArtifact;
    /**
     * Validate and enrich an existing failure artifact
     */
    static validate(artifact: any): FailureArtifact;
    /**
     * Create a collection of related failure artifacts
     */
    static createRelatedGroup(artifacts: Partial<FailureArtifact>[], groupId?: string): FailureArtifact[];
}

// ---- src/cegis/failure-artifact-schema.d.ts ----
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

// ---- src/cegis/index.d.ts ----
/**
 * CEGIS Module Exports
 * Phase 2.1: Main exports for Counter-Example Guided Inductive Synthesis
 */
export * from './types.js';
export { FailureArtifactFactory } from './failure-artifact-factory.js';
export { AutoFixEngine } from './auto-fix-engine.js';
export { RiskAssessmentService } from './risk-assessment-service.js';
export { BaseFixStrategy } from './strategies/base-strategy.js';
export { TypeErrorFixStrategy } from './strategies/type-error-strategy.js';
export { TestFailureFixStrategy } from './strategies/test-failure-strategy.js';
export { ContractViolationFixStrategy } from './strategies/contract-violation-strategy.js';
export { CEGISCli, executeCEGISCli } from '../cli/cegis-cli.js';

// ---- src/cegis/risk-assessment-service.d.ts ----
/**
 * Risk Assessment Service
 * Phase 2.1: Evaluates risks associated with automated fixes
 */
import { FixStrategy, RepairAction, RiskAssessment, FailureArtifact } from './types.js';
export declare class RiskAssessmentService {
    /**
     * Assess the risk level of applying a fix strategy
     */
    assess(strategy: FixStrategy): Promise<number>;
    /**
     * Assess risk of a specific repair action
     */
    assessAction(action: RepairAction): Promise<RiskAssessment>;
    /**
     * Assess cumulative risk of multiple actions
     */
    assessBatch(actions: RepairAction[]): Promise<RiskAssessment>;
    /**
     * Generate risk report for a set of failures and proposed fixes
     */
    generateRiskReport(failures: FailureArtifact[], proposedActions: RepairAction[]): Promise<string>;
    /**
     * Check if a combination of actions creates additional risks
     */
    private checkInteractionRisks;
    private groupActionsByType;
}

// ---- src/cegis/strategies/base-strategy.d.ts ----
/**
 * Base Fix Strategy Interface
 * Phase 2.1: Abstract base class for all fix strategies
 */
import { FailureArtifact, FixStrategy, RepairAction, FailureCategory } from '../types.js';
export declare abstract class BaseFixStrategy implements FixStrategy {
    abstract readonly name: string;
    abstract readonly category: FailureCategory;
    abstract readonly confidence: number;
    abstract readonly riskLevel: number;
    abstract readonly description: string;
    /**
     * Check if this strategy can be applied to the given failure
     */
    abstract canApply(failure: FailureArtifact): Promise<boolean>;
    /**
     * Generate repair actions for the given failure
     */
    abstract generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    /**
     * Common validation for repair actions
     */
    protected validateRepairAction(action: RepairAction): boolean;
    /**
     * Helper method to create a code change repair action
     */
    protected createCodeChangeAction(description: string, filePath: string, oldCode: string, newCode: string, startLine: number, endLine: number, confidence?: number, riskLevel?: number): RepairAction;
    /**
     * Helper method to create a dependency update action
     */
    protected createDependencyUpdateAction(description: string, packageName: string, fromVersion: string, toVersion: string, confidence?: number, riskLevel?: number): RepairAction;
    /**
     * Helper method to create a type annotation action
     */
    protected createTypeAnnotationAction(description: string, filePath: string, oldCode: string, newCode: string, startLine: number, endLine: number, confidence?: number): RepairAction;
    /**
     * Helper method to create a test update action
     */
    protected createTestUpdateAction(description: string, filePath: string, oldCode: string, newCode: string, startLine: number, endLine: number, confidence?: number): RepairAction;
    /**
     * Helper method to create a validation update action
     */
    protected createValidationUpdateAction(description: string, filePath: string, oldSchema: string, newSchema: string, confidence?: number): RepairAction;
    /**
     * Helper method to extract code context around a location
     */
    protected extractCodeContext(filePath: string, startLine: number, endLine: number, contextLines?: number): Promise<string>;
    /**
     * Helper method to check if a file exists
     */
    protected fileExists(filePath: string): Promise<boolean>;
    /**
     * Helper method to parse TypeScript error message
     */
    protected parseTypeScriptError(message: string): {
        code: string;
        type: string;
        description: string;
    } | null;
    /**
     * Get TypeScript error type based on error code
     */
    private getTypeScriptErrorType;
    /**
     * Helper method to determine confidence based on error patterns
     */
    protected calculateConfidence(failure: FailureArtifact): number;
    /**
     * Helper method to assess risk level
     */
    protected assessRiskLevel(failure: FailureArtifact, changeType: 'code' | 'dependency' | 'config'): number;
}

// ---- src/cegis/strategies/contract-violation-strategy.d.ts ----
/**
 * Contract Violation Fix Strategy
 * Phase 2.1: Automatic fixes for runtime conformance violations
 */
import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';
export declare class ContractViolationFixStrategy extends BaseFixStrategy {
    readonly name = "Contract Violation Fix";
    readonly category: FailureCategory;
    readonly confidence = 0.8;
    readonly riskLevel = 2;
    readonly description = "Automatically fixes runtime contract violations by updating validation schemas and adding proper data transformations";
    canApply(failure: FailureArtifact): Promise<boolean>;
    generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    private fixInputViolation;
    private fixOutputViolation;
    private fixSchemaViolation;
    private extractActualData;
    private generateZodSchema;
    private inferZodType;
    private generateDataTransformation;
    private generateOutputTransformation;
    private identifyOptionalFields;
    private generateOptionalFieldsSchema;
    private generateSchemaUpdate;
    private generateVersionedSchema;
}

// ---- src/cegis/strategies/test-failure-strategy.d.ts ----
/**
 * Test Failure Fix Strategy
 * Phase 2.1: Automatic fixes for common test failures and assertion errors
 */
import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';
export declare class TestFailureFixStrategy extends BaseFixStrategy {
    readonly name = "Test Failure Fix";
    readonly category: FailureCategory;
    readonly confidence = 0.7;
    readonly riskLevel = 1;
    readonly description = "Automatically fixes common test failures including assertion mismatches, mock issues, and async test problems";
    canApply(failure: FailureArtifact): Promise<boolean>;
    generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    private isAssertionError;
    private isAsyncTestError;
    private isMockError;
    private isTimeoutError;
    private isMatcherError;
    private fixAssertionError;
    private fixAsyncTestError;
    private fixMockError;
    private fixTimeoutError;
    private fixMatcherError;
    private isNumberComparisonError;
    private isStringComparisonError;
    private isArrayComparisonError;
    private isObjectComparisonError;
    private fixNumberComparison;
    private fixStringComparison;
    private fixArrayComparison;
    private fixObjectComparison;
    private updateAssertion;
}

// ---- src/cegis/strategies/type-error-strategy.d.ts ----
/**
 * TypeScript Type Error Fix Strategy
 * Phase 2.1: Automatic fixes for common TypeScript compilation errors
 */
import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';
export declare class TypeErrorFixStrategy extends BaseFixStrategy {
    readonly name = "TypeScript Type Error Fix";
    readonly category: FailureCategory;
    readonly confidence = 0.8;
    readonly riskLevel = 1;
    readonly description = "Automatically fixes common TypeScript type errors including missing imports, type annotations, and interface mismatches";
    canApply(failure: FailureArtifact): Promise<boolean>;
    generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    private fixNameNotFound;
    private fixPropertyNotFound;
    private fixModuleNotFound;
    private fixTypeAssignmentError;
    private fixArgumentTypeMismatch;
    private fixMissingProperties;
    private fixGenericTypeError;
    private getCommonImports;
    private inferTypeAnnotation;
}

// ---- src/cegis/types.d.ts ----
/**
 * CEGIS (Counter-Example Guided Inductive Synthesis) Types
 * Phase 2.1: Core types for failure artifacts and auto-fix system
 */
import { z } from 'zod';
export declare const FailureCategorySchema: z.ZodEnum<["contract_violation", "test_failure", "type_error", "runtime_error", "build_error", "lint_error", "security_violation", "performance_issue", "accessibility_violation", "dependency_issue"]>;
export type FailureCategory = z.infer<typeof FailureCategorySchema>;
export declare const CodeLocationSchema: z.ZodObject<{
    filePath: z.ZodString;
    startLine: z.ZodNumber;
    endLine: z.ZodNumber;
    startColumn: z.ZodOptional<z.ZodNumber>;
    endColumn: z.ZodOptional<z.ZodNumber>;
    functionName: z.ZodOptional<z.ZodString>;
    className: z.ZodOptional<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    filePath?: string;
    startLine?: number;
    endLine?: number;
    startColumn?: number;
    endColumn?: number;
    functionName?: string;
    className?: string;
}, {
    filePath?: string;
    startLine?: number;
    endLine?: number;
    startColumn?: number;
    endColumn?: number;
    functionName?: string;
    className?: string;
}>;
export type CodeLocation = z.infer<typeof CodeLocationSchema>;
export declare const FailureContextSchema: z.ZodObject<{
    environment: z.ZodDefault<z.ZodString>;
    nodeVersion: z.ZodOptional<z.ZodString>;
    timestamp: z.ZodString;
    phase: z.ZodOptional<z.ZodEnum<["intent", "formal", "test", "code", "verify", "operate"]>>;
    command: z.ZodOptional<z.ZodString>;
    workingDirectory: z.ZodOptional<z.ZodString>;
    gitCommit: z.ZodOptional<z.ZodString>;
    gitBranch: z.ZodOptional<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    environment?: string;
    timestamp?: string;
    command?: string;
    phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
    nodeVersion?: string;
    workingDirectory?: string;
    gitCommit?: string;
    gitBranch?: string;
}, {
    environment?: string;
    timestamp?: string;
    command?: string;
    phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
    nodeVersion?: string;
    workingDirectory?: string;
    gitCommit?: string;
    gitBranch?: string;
}>;
export type FailureContext = z.infer<typeof FailureContextSchema>;
export declare const FailureEvidenceSchema: z.ZodObject<{
    stackTrace: z.ZodOptional<z.ZodString>;
    errorMessage: z.ZodOptional<z.ZodString>;
    errorType: z.ZodOptional<z.ZodString>;
    logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
    sourceCode: z.ZodOptional<z.ZodString>;
    testOutput: z.ZodOptional<z.ZodString>;
    buildOutput: z.ZodOptional<z.ZodString>;
    lintOutput: z.ZodOptional<z.ZodString>;
    dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    relatedFiles: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    dependencies?: string[];
    metrics?: Record<string, number>;
    logs?: string[];
    sourceCode?: string;
    stackTrace?: string;
    errorMessage?: string;
    errorType?: string;
    testOutput?: string;
    buildOutput?: string;
    lintOutput?: string;
    relatedFiles?: string[];
}, {
    dependencies?: string[];
    metrics?: Record<string, number>;
    logs?: string[];
    sourceCode?: string;
    stackTrace?: string;
    errorMessage?: string;
    errorType?: string;
    testOutput?: string;
    buildOutput?: string;
    lintOutput?: string;
    relatedFiles?: string[];
}>;
export type FailureEvidence = z.infer<typeof FailureEvidenceSchema>;
export declare const RootCauseSchema: z.ZodObject<{
    primaryCause: z.ZodString;
    contributingFactors: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    confidence: z.ZodNumber;
    reasoning: z.ZodString;
    suggestedActions: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    confidence?: number;
    primaryCause?: string;
    contributingFactors?: string[];
    reasoning?: string;
    suggestedActions?: string[];
}, {
    confidence?: number;
    primaryCause?: string;
    contributingFactors?: string[];
    reasoning?: string;
    suggestedActions?: string[];
}>;
export type RootCause = z.infer<typeof RootCauseSchema>;
export declare const RepairActionSchema: z.ZodObject<{
    type: z.ZodEnum<["code_change", "dependency_update", "config_change", "test_update", "documentation_update", "refactor", "type_annotation", "validation_update"]>;
    description: z.ZodString;
    confidence: z.ZodNumber;
    riskLevel: z.ZodNumber;
    estimatedEffort: z.ZodEnum<["low", "medium", "high"]>;
    filePath: z.ZodOptional<z.ZodString>;
    codeChange: z.ZodOptional<z.ZodObject<{
        oldCode: z.ZodString;
        newCode: z.ZodString;
        startLine: z.ZodNumber;
        endLine: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    }, {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    }>>;
    dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    prerequisites: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
    dependencies?: string[];
    description?: string;
    estimatedEffort?: "low" | "medium" | "high";
    riskLevel?: number;
    confidence?: number;
    filePath?: string;
    codeChange?: {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    };
    prerequisites?: string[];
}, {
    type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
    dependencies?: string[];
    description?: string;
    estimatedEffort?: "low" | "medium" | "high";
    riskLevel?: number;
    confidence?: number;
    filePath?: string;
    codeChange?: {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    };
    prerequisites?: string[];
}>;
export type RepairAction = z.infer<typeof RepairActionSchema>;
export declare const FailureArtifactSchema: z.ZodObject<{
    id: z.ZodString;
    title: z.ZodString;
    description: z.ZodString;
    severity: z.ZodEnum<["critical", "major", "minor", "info"]>;
    category: z.ZodEnum<["contract_violation", "test_failure", "type_error", "runtime_error", "build_error", "lint_error", "security_violation", "performance_issue", "accessibility_violation", "dependency_issue"]>;
    location: z.ZodOptional<z.ZodObject<{
        filePath: z.ZodString;
        startLine: z.ZodNumber;
        endLine: z.ZodNumber;
        startColumn: z.ZodOptional<z.ZodNumber>;
        endColumn: z.ZodOptional<z.ZodNumber>;
        functionName: z.ZodOptional<z.ZodString>;
        className: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    }, {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    }>>;
    context: z.ZodObject<{
        environment: z.ZodDefault<z.ZodString>;
        nodeVersion: z.ZodOptional<z.ZodString>;
        timestamp: z.ZodString;
        phase: z.ZodOptional<z.ZodEnum<["intent", "formal", "test", "code", "verify", "operate"]>>;
        command: z.ZodOptional<z.ZodString>;
        workingDirectory: z.ZodOptional<z.ZodString>;
        gitCommit: z.ZodOptional<z.ZodString>;
        gitBranch: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    }, {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    }>;
    evidence: z.ZodObject<{
        stackTrace: z.ZodOptional<z.ZodString>;
        errorMessage: z.ZodOptional<z.ZodString>;
        errorType: z.ZodOptional<z.ZodString>;
        logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
        sourceCode: z.ZodOptional<z.ZodString>;
        testOutput: z.ZodOptional<z.ZodString>;
        buildOutput: z.ZodOptional<z.ZodString>;
        lintOutput: z.ZodOptional<z.ZodString>;
        dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        relatedFiles: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    }, {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    }>;
    rootCause: z.ZodOptional<z.ZodObject<{
        primaryCause: z.ZodString;
        contributingFactors: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        confidence: z.ZodNumber;
        reasoning: z.ZodString;
        suggestedActions: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    }, {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    }>>;
    suggestedActions: z.ZodDefault<z.ZodArray<z.ZodObject<{
        type: z.ZodEnum<["code_change", "dependency_update", "config_change", "test_update", "documentation_update", "refactor", "type_annotation", "validation_update"]>;
        description: z.ZodString;
        confidence: z.ZodNumber;
        riskLevel: z.ZodNumber;
        estimatedEffort: z.ZodEnum<["low", "medium", "high"]>;
        filePath: z.ZodOptional<z.ZodString>;
        codeChange: z.ZodOptional<z.ZodObject<{
            oldCode: z.ZodString;
            newCode: z.ZodString;
            startLine: z.ZodNumber;
            endLine: z.ZodNumber;
        }, "strip", z.ZodTypeAny, {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        }, {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        }>>;
        dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        prerequisites: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }, {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }>, "many">>;
    relatedArtifacts: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metadata: z.ZodObject<{
        createdAt: z.ZodString;
        updatedAt: z.ZodString;
        version: z.ZodDefault<z.ZodString>;
        tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        environment: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodString>>;
        source: z.ZodDefault<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    }, {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    }>;
}, "strip", z.ZodTypeAny, {
    id?: string;
    location?: {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    };
    severity?: "critical" | "major" | "minor" | "info";
    description?: string;
    category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "build_error" | "lint_error" | "security_violation" | "performance_issue" | "accessibility_violation" | "dependency_issue";
    metadata?: {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    };
    context?: {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    };
    title?: string;
    suggestedActions?: {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }[];
    evidence?: {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    };
    rootCause?: {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    };
    relatedArtifacts?: string[];
}, {
    id?: string;
    location?: {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    };
    severity?: "critical" | "major" | "minor" | "info";
    description?: string;
    category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "build_error" | "lint_error" | "security_violation" | "performance_issue" | "accessibility_violation" | "dependency_issue";
    metadata?: {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    };
    context?: {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    };
    title?: string;
    suggestedActions?: {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }[];
    evidence?: {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    };
    rootCause?: {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    };
    relatedArtifacts?: string[];
}>;
export type FailureArtifact = z.infer<typeof FailureArtifactSchema>;
export interface FixStrategy {
    name: string;
    category: FailureCategory;
    confidence: number;
    riskLevel: number;
    description: string;
    canApply: (failure: FailureArtifact) => Promise<boolean>;
    generateFix: (failure: FailureArtifact) => Promise<RepairAction[]>;
}
export interface AppliedFix {
    strategy: string;
    actions: RepairAction[];
    success: boolean;
    filesModified: string[];
    errors: string[];
    warnings: string[];
    type?: string;
    description?: string;
    targetFile?: string;
    confidence?: number;
    metadata: {
        timestamp: string;
        duration: number;
        confidence: number;
        riskLevel: number;
    };
}
export interface SkippedFix {
    strategy: string;
    reason: string;
    confidence?: number;
    riskLevel?: number;
    error?: string;
}
export interface AutoFixConfig {
    dryRun: boolean;
    confidenceThreshold: number;
    maxRiskLevel: number;
    enabledCategories: FailureCategory[];
    maxFixesPerRun: number;
    timeoutMs: number;
    backupFiles: boolean;
    generateReport: boolean;
}
export interface FixResult {
    appliedFixes: AppliedFix[];
    skippedFixes: SkippedFix[];
    summary: {
        totalFailures: number;
        fixesApplied: number;
        fixesSkipped: number;
        filesModified: number;
        success: boolean;
        errors: string[];
        warnings: string[];
    };
    recommendations: string[];
    reportPath?: string;
    success: boolean;
    appliedActions: AppliedFix[];
    generatedFiles: string[];
    backupFiles: string[];
    errors: string[];
    analysis?: string;
    proposedFixes?: RepairAction[];
    riskAssessment?: RiskAssessment;
}
export interface RiskAssessment {
    level: number;
    factors: string[];
    mitigation: string[];
    recommendation: 'proceed' | 'caution' | 'abort';
}
export interface AutoFixOptions {
    dryRun?: boolean;
    confidenceThreshold?: number;
    maxRiskLevel?: number;
    timeoutMs?: number;
    maxIterations?: number;
    outputDir?: string;
}
export interface FailurePattern {
    pattern: string;
    frequency: number;
    categories: FailureCategory[];
    commonLocations: CodeLocation[];
    suggestedStrategies: string[];
    confidence: number;
}

// ---- src/cli.d.ts ----
#!/usr/bin/env node
export {};

// ---- src/cli/ae-fix-cli.d.ts ----
#!/usr/bin/env node
/**
 * AE-Framework Auto-Fix CLI
 *
 * Command-line interface for CEGIS-based automated repair
 * Implements `ae fix` command for specification/code repair
 */
export {};

// ---- src/cli/ae-ui-alias.d.ts ----
#!/usr/bin/env node
export {};

// ---- src/cli/approval-cli.d.ts ----
#!/usr/bin/env node
/**
 * CLI for managing approval workflows in ae-framework
 */
export {};

// ---- src/cli/benchmark-cli.d.ts ----
#!/usr/bin/env node
/**
 * Req2Run Benchmark CLI
 * Command-line interface for running AE Framework benchmarks
 */
export {};

// ---- src/cli/cegis-cli.d.ts ----
/**
 * CEGIS CLI Interface
 * Phase 2.1: Command-line interface for automatic code fixing
 */
import { Command } from 'commander';
export declare class CEGISCli {
    private engine;
    constructor();
    /**
     * Create and configure the CLI command
     */
    createCommand(): Command;
    /**
     * Handle the apply command
     */
    private handleApplyCommand;
    /**
     * Handle the analyze command
     */
    private handleAnalyzeCommand;
    /**
     * Handle the create-artifact command
     */
    private handleCreateArtifactCommand;
    /**
     * Handle the status command
     */
    private handleStatusCommand;
    /**
     * Handle the strategies command
     */
    private handleStrategiesCommand;
    /**
     * Load failure artifacts from file
     */
    private loadFailures;
    /**
     * Display fix results
     */
    private displayResults;
    /**
     * Group failures by category
     */
    private groupByCategory;
}
/**
 * Execute the CEGIS CLI
 */
export declare function executeCEGISCli(args: string[]): Promise<void>;

// ---- src/cli/circuit-breaker-cli.d.ts ----
#!/usr/bin/env node
import { Command } from 'commander';
/**
 * Circuit Breaker CLI
 * Provides command-line interface for circuit breaker management and monitoring
 */
export declare class CircuitBreakerCLI {
    private breakers;
    constructor();
    /**
     * Create a circuit breaker with configuration
     */
    createCircuitBreaker(options: {
        name: string;
        failureThreshold?: number;
        successThreshold?: number;
        timeout?: number;
        monitoringWindow?: number;
    }): Promise<void>;
    /**
     * List all circuit breakers and their states
     */
    listCircuitBreakers(): Promise<void>;
    /**
     * Show detailed statistics for a specific circuit breaker
     */
    showStats(breakerName: string): Promise<void>;
    /**
     * Generate comprehensive health report
     */
    generateHealthReport(): Promise<void>;
    /**
     * Test a circuit breaker with simulated operations
     */
    testCircuitBreaker(options: {
        name: string;
        operations: number;
        failureRate: number;
        delay: number;
    }): Promise<void>;
    /**
     * Reset a circuit breaker
     */
    resetCircuitBreaker(breakerName: string): Promise<void>;
    /**
     * Force open a circuit breaker
     */
    forceOpen(breakerName: string): Promise<void>;
    /**
     * Force close a circuit breaker
     */
    forceClose(breakerName: string): Promise<void>;
    /**
     * Watch circuit breaker state changes in real-time
     */
    watchCircuitBreakers(): Promise<void>;
    private setupEventListeners;
    private getStateIcon;
    private getHealthIcon;
    private formatDuration;
    private createHealthReport;
}
export declare function createCircuitBreakerCommand(): Command;

// ---- src/cli/codegen-cli.d.ts ----
#!/usr/bin/env node
/**
 * Code Generation CLI
 * Command-line interface for deterministic code generation and drift detection
 */
import { Command } from 'commander';
export declare function createCodegenCommand(): Command;
export default createCodegenCommand;

// ---- src/cli/config/ConfigLoader.d.ts ----
import { AEFrameworkConfig } from '../types.js';
export declare class ConfigLoader {
    static load(configPath?: string): AEFrameworkConfig;
    private static validateAndSetDefaults;
    private static getDefaultConfig;
}

// ---- src/cli/conformance-cli.d.ts ----
/**
 * Conformance CLI Interface
 * Phase 2.2: Command-line interface for runtime conformance verification
 */
import { Command } from 'commander';
export declare class ConformanceCli {
    private engine;
    private config;
    constructor();
    /**
     * Create and configure the CLI command
     */
    createCommand(): Command;
    /**
     * Handle the verify command
     */
    private handleVerifyCommand;
    /**
     * Handle the rules command
     */
    private handleRulesCommand;
    /**
     * Handle the config command
     */
    private handleConfigCommand;
    /**
     * Handle the metrics command
     */
    private handleMetricsCommand;
    /**
     * Handle the status command
     */
    private handleStatusCommand;
    /**
     * Handle the sample command
     */
    private handleSampleCommand;
    /**
     * Display verification results
     */
    private displayVerificationResults;
    /**
     * Create default runtime context
     */
    private createDefaultContext;
    /**
     * Load default configuration
     */
    private loadDefaultConfig;
    /**
     * Parse configuration value
     */
    private parseConfigValue;
    /**
     * Create sample rules for demonstration
     */
    private createSampleRules;
    /**
     * Create sample data for testing
     */
    private createSampleData;
    /**
     * Simple UUID generator
     */
    private generateUUID;
}
/**
 * Execute the Conformance CLI
 */
export declare function executeConformanceCli(args: string[]): Promise<void>;

// ---- src/cli/enhanced-state-cli.d.ts ----
#!/usr/bin/env node
import { Command } from 'commander';
/**
 * Enhanced State Manager CLI
 * Provides command-line interface for advanced state management operations
 */
export declare class EnhancedStateCLI {
    private stateManager;
    constructor(projectRoot?: string);
    /**
     * Initialize the state manager and CLI
     */
    initialize(): Promise<void>;
    /**
     * Save SSOT (Single Source of Truth) from file
     */
    saveSSOT(options: {
        logicalKey: string;
        inputPath: string;
        phase?: string;
        tags?: string;
        ttl?: number;
        source?: string;
    }): Promise<void>;
    /**
     * Load SSOT data
     */
    loadSSOT(options: {
        logicalKey: string;
        version?: number;
        outputPath?: string;
    }): Promise<void>;
    /**
     * List all versions of a logical key
     */
    listVersions(logicalKey: string): Promise<void>;
    /**
     * Create compressed snapshot
     */
    createSnapshot(options: {
        phase: string;
        entities?: string;
    }): Promise<void>;
    /**
     * Load and display snapshot
     */
    loadSnapshot(snapshotId: string): Promise<void>;
    /**
     * Simulate failure artifact for testing
     */
    simulateFailure(options: {
        phase: string;
        type: 'validation' | 'compilation' | 'test' | 'verification' | 'generation';
        severity: 'low' | 'medium' | 'high' | 'critical';
        message: string;
        retryable?: boolean;
    }): Promise<void>;
    /**
     * Run manual garbage collection
     */
    runGarbageCollection(): Promise<void>;
    /**
     * Display storage statistics
     */
    showStatistics(): Promise<void>;
    /**
     * Test transaction functionality
     */
    testTransaction(): Promise<void>;
    /**
     * Export state to file
     */
    exportState(outputPath: string): Promise<void>;
    /**
     * Import state from file
     */
    importState(inputPath: string): Promise<void>;
    private setupEventListeners;
    private formatBytes;
    /**
     * Cleanup and shutdown
     */
    shutdown(): Promise<void>;
}
export declare function createEnhancedStateCommand(): Command;

// ---- src/cli/guards/GuardRunner.d.ts ----
import { AEFrameworkConfig, Guard, GuardResult } from '../types.js';
export declare class GuardRunner {
    private config;
    constructor(config: AEFrameworkConfig);
    run(guard: Guard): Promise<GuardResult>;
    private runTDDGuard;
    private runTestExecutionGuard;
    private runRedGreenCycleGuard;
    private runCoverageGuard;
    checkGitForTDDViolations(): Promise<string[]>;
}

// ---- src/cli/index.d.ts ----
#!/usr/bin/env node
import { Phase } from './types.js';
import { TaskRequest, TaskResponse, TaskHandler } from '../agents/task-types.js';
import '../telemetry/telemetry-setup.js';
type TaskResult = TaskResponse;
declare class AEFrameworkCLI {
    private config;
    private phaseValidator;
    private guardRunner;
    private intentSystem;
    naturalLanguageHandler: TaskHandler;
    userStoriesHandler: TaskHandler;
    validationHandler: TaskHandler;
    domainModelingHandler: TaskHandler;
    uiHandler: TaskHandler;
    constructor();
    checkPhase(phaseName: string): Promise<void>;
    runGuards(guardName?: string): Promise<void>;
    runIntent(options: {
        analyze?: boolean;
        validate?: boolean;
        sources?: string;
    }): Promise<void>;
    handleProgressBlocking(result: TaskResult): void;
    nextPhase(): Promise<void>;
    detectCurrentPhase(): Promise<string>;
    getNextPhase(currentPhase: string): string | null;
    displayResults(details: Array<{
        check: string;
        passed: boolean;
        message?: string;
    }>): void;
    displayPhaseRequirements(phase: Phase): void;
    handleUIScaffoldTask(request: TaskRequest): Promise<TaskResponse>;
}
export { AEFrameworkCLI };

// ---- src/cli/integration-cli.d.ts ----
/**
 * Integration Testing CLI Interface
 * Phase 2.3: Command-line interface for comprehensive integration testing
 */
import { Command } from 'commander';
export declare class IntegrationTestingCli {
    private orchestrator;
    private discovery;
    constructor();
    /**
     * Create and configure the CLI command
     */
    createCommand(): Command;
    /**
     * Handle the run command
     */
    private handleRunCommand;
    /**
     * Handle the discover command
     */
    private handleDiscoverCommand;
    /**
     * Handle the list command
     */
    private handleListCommand;
    /**
     * Handle the generate command
     */
    private handleGenerateCommand;
    /**
     * Handle the status command
     */
    private handleStatusCommand;
    /**
     * Handle the reports command
     */
    private handleReportsCommand;
    /**
     * Create default environment
     */
    private createDefaultEnvironment;
    /**
     * Display discovery results in table format
     */
    private displayDiscoveryTable;
    /**
     * Generate sample test case
     */
    private generateSampleTest;
    /**
     * Generate sample test suite
     */
    private generateSampleSuite;
    /**
     * Generate sample fixture
     */
    private generateSampleFixture;
    /**
     * Generate sample environment
     */
    private generateSampleEnvironment;
    /**
     * Format file size
     */
    private formatFileSize;
}
/**
 * Execute the Integration Testing CLI
 */
export declare function executeIntegrationCli(args: string[]): Promise<void>;

// ---- src/cli/metrics/MetricsCollector.d.ts ----
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

// ---- src/cli/phase-cli.d.ts ----
#!/usr/bin/env node
/**
 * CLI for managing ae-framework phase state
 */
export {};

// ---- src/cli/quality-cli.d.ts ----
/**
 * Quality CLI commands for the AE-Framework
 * Provides commands to execute and manage quality gates
 */
import { Command } from 'commander';
export declare function createQualityCommand(): Command;
export default createQualityCommand;

// ---- src/cli/resilience-cli.d.ts ----
#!/usr/bin/env node
import { Command } from 'commander';
/**
 * Resilience System CLI
 * Provides command-line interface for resilience pattern management and monitoring
 */
export declare class ResilienceCLI {
    private systems;
    constructor();
    /**
     * Create a resilience system with configuration
     */
    createSystem(options: {
        name: string;
        preset?: 'default' | 'aggressive' | 'conservative' | 'minimal';
        config?: string;
    }): Promise<void>;
    /**
     * List all resilience systems
     */
    listSystems(): Promise<void>;
    /**
     * Get detailed health statistics
     */
    getHealth(systemName?: string): Promise<void>;
    /**
     * Reset resilience system statistics
     */
    resetSystem(systemName?: string): Promise<void>;
    /**
     * Test resilience system with simulated operations
     */
    testSystem(options: {
        systemName?: string;
        operations?: number;
        failureRate?: number;
        bulkheadName?: string;
    }): Promise<void>;
    /**
     * Export system configuration
     */
    exportConfig(systemName?: string, outputPath?: string): Promise<void>;
}
/**
 * Create resilience command for CLI
 */
export declare function createResilienceCommand(): Command;

// ---- src/cli/sbom-cli.d.ts ----
#!/usr/bin/env node
import { Command } from 'commander';
/**
 * SBOM (Software Bill of Materials) CLI
 * Provides command-line interface for SBOM generation and management
 */
export declare class SBOMCLI {
    /**
     * Generate SBOM for project
     */
    generateSBOM(options: {
        projectRoot?: string;
        output?: string;
        format?: 'json' | 'xml';
        includeDevDeps?: boolean;
        includeVulns?: boolean;
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Validate existing SBOM
     */
    validateSBOM(sbomPath: string, options: {
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Compare two SBOMs
     */
    compareSBOMs(sbom1Path: string, sbom2Path: string, options: {
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Generate CI/CD integration scripts
     */
    generateCIIntegration(options: {
        ciProvider?: 'github' | 'gitlab' | 'azure' | 'jenkins';
        output?: string;
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Generate GitHub Actions workflow
     */
    private generateGitHubWorkflow;
    /**
     * Generate GitLab CI pipeline
     */
    private generateGitLabPipeline;
    /**
     * Generate Azure DevOps pipeline
     */
    private generateAzurePipeline;
    /**
     * Generate Jenkinsfile
     */
    private generateJenkinsfile;
}
/**
 * Create SBOM command for CLI
 */
export declare function createSBOMCommand(): Command;

// ---- src/cli/security-cli.d.ts ----
/**
 * Security CLI commands for the AE-Framework
 * Provides commands to test and manage security headers
 */
import { Command } from 'commander';
export declare function createSecurityCommand(): Command;
export default createSecurityCommand;

// ---- src/cli/slash-cli.d.ts ----
#!/usr/bin/env node
/**
 * Interactive slash command CLI for ae-framework
 */
export {};

// ---- src/cli/spec-cli.d.ts ----
#!/usr/bin/env node
/**
 * AE-Framework Spec CLI Integration
 * Integrates spec-compiler into main ae-framework CLI
 */
import { Command } from 'commander';
export declare function createSpecCommand(): Command;
export default createSpecCommand;

// ---- src/cli/types.d.ts ----
export interface AEFrameworkConfig {
    version: string;
    name: string;
    description: string;
    phases: Record<string, Phase>;
    guards: Guard[];
    cli: CLIConfig;
    templates: TemplateConfig;
    integrations: IntegrationConfig;
    metrics: MetricsConfig;
}
export interface Phase {
    name: string;
    description: string;
    required_artifacts: string[];
    validation: string[];
    enforce_red_first?: boolean;
    block_code_without_test?: boolean;
    mandatory_test_run?: boolean;
    coverage_threshold?: number;
    prerequisites?: Prerequisite[];
}
export interface Prerequisite {
    phase: string;
    status: string;
    validation: string;
}
export interface Guard {
    name: string;
    description: string;
    rule: string;
    enforcement: 'strict' | 'warning';
}
export interface CLIConfig {
    checkpoint_validation: boolean;
    interactive_mode: boolean;
    auto_validation: boolean;
    commands: Record<string, CommandConfig>;
}
export interface CommandConfig {
    description: string;
    usage: string;
}
export interface TemplateConfig {
    test_first: {
        enabled: boolean;
        path: string;
    };
    phase_transitions: {
        enabled: boolean;
        require_validation: boolean;
    };
    standard_prompts: {
        enabled: boolean;
        path: string;
    };
}
export interface IntegrationConfig {
    git: {
        pre_commit_hooks: boolean;
        prevent_commit_on_red: boolean;
    };
    ide: {
        vscode_extension: boolean;
        guard_notifications: boolean;
    };
    ci_cd: {
        validate_on_push: boolean;
        block_merge_on_violations: boolean;
    };
}
export interface MetricsConfig {
    track_tdd_violations: boolean;
    phase_timing: boolean;
    coverage_trends: boolean;
    export: {
        format: string;
        path: string;
    };
}
export interface ValidationResult {
    success: boolean;
    message?: string;
    details: ValidationDetail[];
}
export interface ValidationDetail {
    check: string;
    passed: boolean;
    message?: string;
}
export interface GuardResult {
    success: boolean;
    message?: string;
}
export interface PhaseCheckpoint {
    beforeCode: {
        required: string[];
        validate: () => Promise<boolean>;
    };
    afterCode: {
        required: string[];
        validate: () => Promise<boolean>;
    };
}

// ---- src/cli/ui-scaffold-cli.d.ts ----
#!/usr/bin/env node
export {};

// ---- src/cli/validators/PhaseValidator.d.ts ----
import { AEFrameworkConfig, Phase, ValidationResult, Prerequisite } from '../types.js';
export declare class PhaseValidator {
    private config;
    constructor(config: AEFrameworkConfig);
    validate(phase: Phase): Promise<ValidationResult>;
    validatePrerequisite(prereq: Prerequisite): Promise<ValidationResult>;
    hasRequiredArtifacts(phase: Phase): Promise<boolean>;
    private checkArtifactExists;
    private runValidation;
    private validateTestsExist;
    private validateTestsAreRed;
    private validateTestsPass;
    private validateCodeHasTests;
    private validateCoverage;
    private runFullTestSuite;
    private validateTraceability;
}

// ---- src/codegen/deterministic-generator.d.ts ----
/**
 * Deterministic Code Generator
 * Ensures consistent code generation from AE-IR specifications
 */
export interface CodegenOptions {
    /** Input AE-IR file path */
    inputPath: string;
    /** Output directory for generated code */
    outputDir: string;
    /** Template directory */
    templateDir?: string;
    /** Target language/framework */
    target: 'typescript' | 'react' | 'api' | 'database';
    /** Enable drift detection */
    enableDriftDetection?: boolean;
    /** Custom hash algorithm */
    hashAlgorithm?: 'sha256' | 'md5';
    /** Preserve existing manual modifications */
    preserveManualChanges?: boolean;
}
export interface GeneratedFile {
    /** Relative file path */
    filePath: string;
    /** Generated content */
    content: string;
    /** Content hash for drift detection */
    hash: string;
    /** Generation timestamp */
    timestamp: string;
    /** Source specification hash */
    specHash: string;
}
export interface DriftDetectionResult {
    /** Whether drift was detected */
    hasDrift: boolean;
    /** Files with detected drift */
    driftedFiles: Array<{
        filePath: string;
        reason: 'spec_changed' | 'manual_modification' | 'template_changed';
        expectedHash: string;
        actualHash: string;
        lastGenerated: string;
    }>;
    /** Summary of drift analysis */
    summary: {
        totalFiles: number;
        driftedFiles: number;
        upToDateFiles: number;
    };
}
export interface CodegenManifest {
    /** Generation metadata */
    metadata: {
        generatedAt: string;
        specHash: string;
        templateHash: string;
        options: CodegenOptions;
    };
    /** Generated files registry */
    files: GeneratedFile[];
}
export declare class DeterministicCodeGenerator {
    private options;
    private manifestPath;
    constructor(options: CodegenOptions);
    /**
     * Generate code from AE-IR specification
     */
    generate(): Promise<CodegenManifest>;
    /**
     * Detect drift between current state and expected state
     */
    detectDrift(currentSpecHash: string): Promise<DriftDetectionResult>;
    /**
     * Generate files based on target and AE-IR
     */
    private generateFiles;
    /**
     * Generate TypeScript types and interfaces
     */
    private generateTypeScriptFiles;
    /**
     * Generate React components
     */
    private generateReactFiles;
    /**
     * Generate API handlers
     */
    private generateAPIFiles;
    /**
     * Generate database schemas
     */
    private generateDatabaseFiles;
    /**
     * Helper methods for code generation
     */
    private generateTypeScriptTypes;
    private generateAPIInterfaces;
    private generateValidationSchemas;
    private generateEntityForm;
    private generateEntityList;
    private generateAPIHandler;
    private generateSQLMigration;
    private generateORMModel;
    /**
     * Helper methods for type mapping
     */
    private mapTypeToTS;
    private mapTypeToZod;
    private mapTypeToInputType;
    private mapTypeToSQL;
    private getColumnOptions;
    /**
     * Utility methods
     */
    private loadAEIR;
    private loadManifest;
    private writeManifest;
    private calculateHash;
    private calculateTemplateHash;
}

// ---- src/codegen/drift-detector.d.ts ----
/**
 * Drift Detection System
 * Monitors changes in generated code and specifications
 */
export interface DriftConfig {
    /** Directory containing generated code */
    codeDir: string;
    /** Path to AE-IR specification file */
    specPath: string;
    /** Path to codegen manifest */
    manifestPath?: string;
    /** Files to ignore during drift detection */
    ignorePatterns?: string[];
    /** Enable detailed reporting */
    verbose?: boolean;
    /** Auto-fix simple drift issues */
    autoFix?: boolean;
}
export interface FileChangeInfo {
    /** File path relative to codeDir */
    filePath: string;
    /** Change type */
    changeType: 'modified' | 'added' | 'deleted' | 'renamed';
    /** Previous hash (for modified files) */
    previousHash?: string;
    /** Current hash */
    currentHash?: string;
    /** Change timestamp */
    detectedAt: string;
    /** Lines changed (approximate) */
    linesChanged?: number;
    /** Confidence level of detection */
    confidence: 'high' | 'medium' | 'low';
}
export interface DriftReport {
    /** Overall drift status */
    status: 'no_drift' | 'minor_drift' | 'major_drift' | 'critical_drift';
    /** Summary statistics */
    summary: {
        totalFiles: number;
        changedFiles: number;
        addedFiles: number;
        deletedFiles: number;
        unchangedFiles: number;
    };
    /** Detailed change information */
    changes: FileChangeInfo[];
    /** Specification change detection */
    specificationChange: {
        hasChanged: boolean;
        previousHash?: string;
        currentHash?: string;
        changesSince?: string;
    };
    /** Recommendations */
    recommendations: string[];
    /** Generated at timestamp */
    generatedAt: string;
}
export declare class DriftDetector {
    private config;
    constructor(config: DriftConfig);
    /**
     * Perform comprehensive drift detection
     */
    detectDrift(): Promise<DriftReport>;
    /**
     * Detect changes in the specification file
     */
    private detectSpecificationChanges;
    /**
     * Scan for changes in existing files
     */
    private scanFileChanges;
    /**
     * Detect new files and structural changes
     */
    private detectStructuralChanges;
    /**
     * Calculate drift severity status
     */
    private calculateDriftStatus;
    /**
     * Generate actionable recommendations
     */
    private generateRecommendations;
    /**
     * Auto-fix minor drift issues
     */
    private autoFixMinorIssues;
    /**
     * Helper methods
     */
    private loadManifest;
    private calculateHash;
    private estimateLinesChanged;
    private calculateChangeConfidence;
    /**
     * Attempts to determine the original line count from the manifest or original file content.
     */
    private getOriginalLineCount;
    private isLikelyGeneratedFile;
    private generateSummary;
    private printReport;
}

// ---- src/commands/adapt/jest.d.ts ----
export declare function adaptJest(thresholds?: {
    statements: number;
    branches: number;
    functions: number;
    lines: number;
}): Promise<void>;

// ---- src/commands/adapt/vitest.d.ts ----
export declare function adaptVitest(thresholds?: {
    statements: number;
    branches: number;
    functions: number;
    lines: number;
}): Promise<void>;

// ---- src/commands/agent/complete.d.ts ----
export declare function agentComplete(prompt: string, system?: string, flags?: {
    record?: boolean;
    replay?: boolean;
    dir?: string;
}): Promise<void>;

// ---- src/commands/bench/run.d.ts ----
export declare function benchRun(): Promise<void>;

// ---- src/commands/ci/scaffold.d.ts ----
export declare function ciScaffold(force?: boolean): Promise<void>;

// ---- src/commands/doctor/env.d.ts ----
export declare function doctorEnv(): Promise<void>;

// ---- src/commands/extended/analyze-command-unified.d.ts ----
/**
 * Unified Analyze Command for ae-framework
 * Provides deep code analysis with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { CodeAnalysis, AnalysisOptions } from './types.js';
export declare class UnifiedAnalyzeCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): AnalysisOptions;
    protected execute(args: string[], options: AnalysisOptions, context: CommandContext): Promise<ExtendedCommandResult<CodeAnalysis>>;
    private performAnalysis;
    private analyzeFile;
    private performBasicAnalysis;
    private performSecurityAnalysis;
    private performPerformanceAnalysis;
    private performTypeScriptAnalysis;
    private calculateCodeMetrics;
    private extractDependencies;
    private calculateCyclomaticComplexity;
    private calculateCognitiveComplexity;
    private calculateFileCognitiveComplexity;
    private findSourceFiles;
    private calculateOverallConfidence;
    private createSummary;
    protected generateValidationClaim(data: CodeAnalysis): string;
    protected generateSummary(data: CodeAnalysis): string;
}

// ---- src/commands/extended/base-command.d.ts ----
/**
 * Base Command for Extended Commands
 * Provides common functionality and unified interface
 */
import type { CommandResult, CommandContext } from '../slash-command-manager.js';
import { EvidenceValidator } from '../../utils/evidence-validator.js';
export interface ExtendedCommandConfig {
    name: string;
    description: string;
    usage: string;
    aliases?: string[];
    category: 'utility' | 'analysis' | 'documentation';
}
export interface ExtendedCommandResult<T = any> {
    success: boolean;
    message: string;
    data?: T;
    evidence?: any[];
    metrics?: CommandMetrics;
}
export interface CommandMetrics {
    executionTime: number;
    filesProcessed: number;
    confidence?: number;
}
export declare abstract class BaseExtendedCommand {
    readonly name: string;
    readonly description: string;
    readonly category: "utility";
    readonly usage: string;
    readonly aliases?: string[];
    protected validator: EvidenceValidator;
    private metrics;
    constructor(config?: ExtendedCommandConfig);
    /**
     * Record metric for performance tracking
     */
    protected recordMetric(key: string, value?: number): void;
    /**
     * Get recorded metrics
     */
    protected getMetrics(): Map<string, number>;
    /**
     * Main handler method - implements common flow
     */
    handler(args: string[], context: CommandContext): Promise<CommandResult>;
    /**
     * Validate command arguments
     */
    protected abstract validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    /**
     * Parse command options
     */
    protected parseOptions(args: string[]): Record<string, any>;
    /**
     * Execute the specific command logic
     */
    protected abstract execute(args: string[], options: Record<string, any>, context: CommandContext): Promise<ExtendedCommandResult>;
    /**
     * Validate results with evidence
     */
    protected validateWithEvidence(data: any, options: Record<string, any>): Promise<any[]>;
    /**
     * Generate validation claim from data
     */
    protected abstract generateValidationClaim(data: any): string;
    /**
     * Generate summary for results
     */
    protected abstract generateSummary(data: any): string;
}

// ---- src/commands/extended/document-command-unified.d.ts ----
/**
 * Unified Document Command for ae-framework
 * Generates comprehensive documentation with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { DocumentationResult, DocumentationOptions } from './types.js';
export declare class UnifiedDocumentCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): DocumentationOptions;
    protected execute(args: string[], options: DocumentationOptions, context: CommandContext): Promise<ExtendedCommandResult<DocumentationResult>>;
    private generateDocumentation;
    private findSourceFiles;
    private documentFile;
    private parseTypeScriptFile;
    private parseJavaScriptFile;
    private hasPrivateModifier;
    private createFunctionItem;
    private createClassItem;
    private createInterfaceItem;
    private createTypeItem;
    private createConstantItem;
    private createEnumItem;
    private getFunctionSignature;
    private extractParameters;
    private extractReturnType;
    private getTypeString;
    private extractJSDocComment;
    private extractParameterComment;
    private extractReturnComment;
    private extractJSDocFromLines;
    private extractExamples;
    private extractDependencies;
    private calculateDocumentationCoverage;
    private generateDocumentationSuggestions;
    private formatDocumentation;
    private formatAsMarkdown;
    private formatAsJSDoc;
    private getOutputPath;
    private calculateDocumentationCompleteness;
    private createDocumentationSummary;
    protected generateValidationClaim(data: DocumentationResult): string;
    protected generateSummary(data: DocumentationResult): string;
}

// ---- src/commands/extended/improve-command-unified.d.ts ----
/**
 * Unified Improve Command for ae-framework
 * Provides code improvements and refactoring suggestions with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { ImprovementResult, ImprovementOptions } from './types.js';
export declare class UnifiedImproveCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): ImprovementOptions;
    protected execute(args: string[], options: ImprovementOptions, context: CommandContext): Promise<ExtendedCommandResult<ImprovementResult>>;
    private analyzeForImprovements;
    private findSourceFiles;
    private analyzeFile;
    private analyzePatterns;
    private analyzeSecurityPatterns;
    private analyzePerformancePatterns;
    private analyzeModernizationPatterns;
    private analyzeTypeScriptPatterns;
    private applyImprovements;
    private calculateEstimatedImpact;
    private calculateComplexityMetric;
    private calculateOverallConfidence;
    private createImprovementSummary;
    protected generateValidationClaim(data: ImprovementResult): string;
    protected generateSummary(data: ImprovementResult): string;
}

// ---- src/commands/extended/index.d.ts ----
/**
 * Extended Commands for ae-framework
 * Unified architecture with consistent interfaces and shared functionality
 */
export { UnifiedAnalyzeCommand } from './analyze-command-unified.js';
export { UnifiedDocumentCommand } from './document-command-unified.js';
export { UnifiedImproveCommand } from './improve-command-unified.js';
export { UnifiedTroubleshootCommand } from './troubleshoot-command-unified.js';
export { PersonaCommand } from './persona-command.js';
export { InstallerCommand } from './installer-command.js';
export { MCPCommand } from './mcp-command.js';
export { BaseExtendedCommand } from './base-command.js';
export type { ExtendedCommandResult, ExtendedCommandConfig, CommandMetrics } from './base-command.js';
export * from './types.js';

// ---- src/commands/extended/installer-command.d.ts ----
/**
 * Installer Command for ae-framework
 * Provides project template installation and setup functionality
 */
import { BaseExtendedCommand, ExtendedCommandResult, ExtendedCommandConfig } from './base-command.js';
import { InstallationTemplate } from '../../utils/installer-manager.js';
export interface InstallerCommandResult extends ExtendedCommandResult {
    installedTemplate?: string;
    installedDependencies?: string[];
    createdFiles?: string[];
    suggestions?: string[];
    recommendations?: string[];
    availableTemplates?: InstallationTemplate[];
}
export declare class InstallerCommand extends BaseExtendedCommand {
    readonly name = "/ae:installer";
    readonly description = "Install project templates and manage dependencies";
    readonly category: "utility";
    readonly usage = "/ae:installer <template-id> | list | suggest | templates";
    readonly aliases: string[];
    private installerManager?;
    private contextManager?;
    private tokenOptimizer?;
    constructor(config?: ExtendedCommandConfig);
    private getInstallerManager;
    private getContextManager;
    private getTokenOptimizer;
    handler(args: string[], context: any): Promise<InstallerCommandResult>;
    private handleListTemplates;
    private handleSuggestTemplates;
    private handleInstallTemplate;
    private parseInstallationOptions;
    private generatePostInstallationRecommendations;
    private handleHelp;
    private createErrorResult;
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected execute(args: string[], options: Record<string, any>, context: any): Promise<ExtendedCommandResult>;
    protected generateValidationClaim(data: any): string;
    protected generateSummary(data: any): string;
}

// ---- src/commands/extended/mcp-command.d.ts ----
/**
 * MCP Command for ae-framework
 * Manages MCP server instances, plugins, and extensions
 */
import { BaseExtendedCommand, ExtendedCommandResult, ExtendedCommandConfig } from './base-command.js';
export interface MCPCommandResult extends ExtendedCommandResult {
    serverStatus?: any;
    pluginList?: string[];
    capabilities?: any[];
    metrics?: any;
    pluginDetails?: any;
    recommendations?: string[];
}
export declare class MCPCommand extends BaseExtendedCommand {
    readonly name = "/ae:mcp";
    readonly description = "Manage MCP server, plugins, and extensions";
    readonly category: "utility";
    readonly usage = "/ae:mcp <action> [options]";
    readonly aliases: string[];
    private mcpServer?;
    private pluginManager?;
    private contextManager?;
    private tokenOptimizer?;
    constructor(config?: ExtendedCommandConfig);
    private getMCPServer;
    private getPluginManager;
    private getContextManager;
    private getTokenOptimizer;
    handler(args: string[], context: any): Promise<MCPCommandResult>;
    private handleStartServer;
    private handleStopServer;
    private handleRestartServer;
    private handleServerStatus;
    private handlePluginManagement;
    private handleListPlugins;
    private handleCapabilities;
    private handleMetrics;
    private handleConfigManagement;
    private handleShowConfig;
    private handleHelp;
    private loadServerConfig;
    private handleDiscoverPlugins;
    private handleLoadPlugin;
    private handleEnablePlugin;
    private handleDisablePlugin;
    private handleUnloadPlugin;
    private handleCreatePlugin;
    private handleCreateConfig;
    private createErrorResult;
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected execute(args: string[], options: Record<string, any>, context: any): Promise<ExtendedCommandResult>;
    protected generateValidationClaim(data: any): string;
    protected generateSummary(data: any): string;
}

// ---- src/commands/extended/persona-command.d.ts ----
/**
 * Persona Command for ae-framework
 * Manages Smart Persona System for adaptive AI behavior
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { UserPreferences, PersonaProfile } from '../../utils/persona-manager.js';
interface PersonaCommandResult {
    action: 'view' | 'update' | 'export' | 'import' | 'reset';
    profile?: PersonaProfile;
    preferences?: UserPreferences;
    message: string;
    data?: any;
}
export declare class PersonaCommand extends BaseExtendedCommand {
    private personaManager;
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): Record<string, any>;
    protected execute(args: string[], options: any, context: CommandContext): Promise<ExtendedCommandResult<PersonaCommandResult>>;
    private handleView;
    private handleUpdate;
    private handleExport;
    private handleImport;
    private handleReset;
    private parseUpdateOptions;
    private convertUpdateTypes;
    private getAvailablePreferenceKeys;
    protected generateValidationClaim(data: PersonaCommandResult): string;
    protected generateSummary(data: PersonaCommandResult): string;
}
export {};

// ---- src/commands/extended/troubleshoot-command-unified.d.ts ----
/**
 * Unified Troubleshoot Command for ae-framework
 * Provides intelligent debugging and problem diagnosis with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { TroubleshootResult, TroubleshootOptions } from './types.js';
export declare class UnifiedTroubleshootCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): TroubleshootOptions;
    protected execute(args: string[], options: TroubleshootOptions, context: CommandContext): Promise<ExtendedCommandResult<TroubleshootResult>>;
    private extractDescription;
    private performTroubleshooting;
    private autoDetectIssues;
    private checkPackageJson;
    private checkBuildStatus;
    private checkCommonFileIssues;
    private checkTypeScriptConfig;
    private analyzeErrorMessage;
    private analyzeLogs;
    private analyzeDescription;
    private getCategorySolutions;
    private calculateComplexityScore;
    private calculateOverallConfidence;
    private createTroubleshootSummary;
    protected generateValidationClaim(data: TroubleshootResult): string;
    protected generateSummary(data: TroubleshootResult): string;
}

// ---- src/commands/extended/types.d.ts ----
/**
 * Unified types for Extended Commands
 * Provides consistent data structures across all commands
 */
export interface AnalysisTarget {
    path: string;
    type: 'file' | 'directory';
}
export interface Issue {
    type: string;
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info';
    message: string;
    location?: {
        file?: string;
        line?: number;
        column?: number;
    };
}
export interface Suggestion {
    type: string;
    message: string;
    priority: 'high' | 'medium' | 'low';
    category: string;
    confidence?: number;
}
export interface Metrics {
    lines: number;
    files: number;
    complexity?: number;
    coverage?: number;
}
export interface UnifiedResult {
    target: AnalysisTarget;
    summary: string;
    issues: Issue[];
    suggestions: Suggestion[];
    metrics: Metrics;
    metadata: {
        timestamp: string;
        commandType: string;
        processingTime: number;
    };
}
export interface CodeAnalysis extends UnifiedResult {
    codeMetrics: {
        functions: number;
        classes: number;
        dependencies: string[];
        cyclomaticComplexity: number;
        cognitiveComplexity: number;
    };
    securityIssues: Issue[];
    performanceIssues: Issue[];
}
export interface DocumentationResult extends UnifiedResult {
    documentation: {
        exports: ExportedItem[];
        examples: Example[];
        dependencies: string[];
        coverage: number;
    };
    format: 'markdown' | 'jsdoc' | 'api-json';
    outputPath?: string;
}
export interface ExportedItem {
    name: string;
    type: 'function' | 'class' | 'interface' | 'type' | 'constant' | 'enum';
    signature?: string;
    description?: string;
    parameters?: Parameter[];
    returns?: ReturnValue;
}
export interface Parameter {
    name: string;
    type: string;
    description?: string;
    optional?: boolean;
    defaultValue?: string;
}
export interface ReturnValue {
    type: string;
    description?: string;
}
export interface Example {
    title: string;
    code: string;
    description?: string;
}
export interface ImprovementResult extends UnifiedResult {
    improvements: Improvement[];
    appliedCount: number;
    estimatedImpact: string;
}
export interface Improvement {
    type: 'refactor' | 'optimize' | 'simplify' | 'modernize' | 'security' | 'pattern';
    description: string;
    location: {
        line: number;
        column?: number;
    };
    original: string;
    suggested: string;
    impact: 'high' | 'medium' | 'low';
    category: 'performance' | 'readability' | 'maintainability' | 'security' | 'best-practice';
    confidence: number;
}
export interface TroubleshootResult extends UnifiedResult {
    detectedIssues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
}
export interface DetectedIssue extends Issue {
    stackTrace?: string;
    reproducible?: boolean;
    frequency?: number;
}
export interface Diagnosis {
    rootCause: string;
    affectedComponents: string[];
    impact: string;
    confidence: number;
}
export interface Solution {
    description: string;
    steps: string[];
    confidence: number;
    estimatedTime: string;
    riskLevel: 'low' | 'medium' | 'high';
    prerequisites?: string[];
}
export interface BaseCommandOptions {
    validate?: boolean;
    output?: string;
    format?: string;
    verbose?: boolean;
    dryRun?: boolean;
}
export interface AnalysisOptions extends BaseCommandOptions {
    depth?: 'shallow' | 'normal' | 'deep';
    includeTests?: boolean;
    includeSecurity?: boolean;
    includePerformance?: boolean;
    minConfidence?: number;
}
export interface DocumentationOptions extends BaseCommandOptions {
    format?: 'markdown' | 'jsdoc' | 'api-json';
    includePrivate?: boolean;
    includeExamples?: boolean;
    template?: string;
}
export interface ImprovementOptions extends BaseCommandOptions {
    category?: string;
    impact?: 'high' | 'medium' | 'low';
    apply?: boolean;
    interactive?: boolean;
}
export interface TroubleshootOptions extends BaseCommandOptions {
    auto?: boolean;
    logs?: string;
    error?: string;
    interactive?: boolean;
}

// ---- src/commands/qa/flake.d.ts ----
import { type Result } from '../../core/result.js';
import type { AppError } from '../../core/errors.js';
interface QAFlakeOptions {
    times?: number;
    pattern?: string;
    timeoutMs?: number;
    workers?: string | number;
}
export declare function qaFlake(options?: QAFlakeOptions): Promise<Result<{
    failures: number;
    total: number;
    seeds: number[];
}, AppError>>;
export {};

// ---- src/commands/qa/run.d.ts ----
export declare function qaRun(): Promise<void>;

// ---- src/commands/slash-command-manager.d.ts ----
/**
 * Slash Command Manager for ae-framework
 * Provides a unified interface for executing commands across all agents
 */
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { SteeringLoader } from '../utils/steering-loader.js';
import { ApprovalService } from '../services/approval-service.js';
export interface SlashCommand {
    name: string;
    description: string;
    category: 'phase' | 'utility' | 'info' | 'workflow';
    usage: string;
    aliases?: string[];
    handler: CommandHandler;
    requiresPhase?: PhaseType;
    stopOnFailure?: boolean;
}
export type CommandHandler = (args: string[], context: CommandContext) => Promise<CommandResult>;
export interface CommandContext {
    phaseStateManager: PhaseStateManager;
    steeringLoader: SteeringLoader;
    approvalService: ApprovalService;
    currentPhase?: PhaseType;
    projectRoot: string;
}
export interface CommandResult {
    success: boolean;
    message?: string;
    data?: any;
    nextCommand?: string;
}
export declare class SlashCommandManager {
    private commands;
    private aliases;
    private context;
    private intentAgent?;
    private formalAgent?;
    private testAgent?;
    private codeAgent?;
    private verifyAgent?;
    private operateAgent?;
    constructor(projectRoot?: string);
    /**
     * Get or create intent agent
     */
    private getIntentAgent;
    /**
     * Get or create formal agent
     */
    private getFormalAgent;
    /**
     * Get or create test agent
     */
    private getTestAgent;
    /**
     * Get or create code agent
     */
    private getCodeAgent;
    /**
     * Get or create verify agent
     */
    private getVerifyAgent;
    /**
     * Get or create operate agent
     */
    private getOperateAgent;
    /**
     * Register extended commands from Issue #17 (Unified Architecture)
     */
    private registerExtendedCommands;
    /**
     * Register all available commands
     */
    private registerCommands;
    /**
     * Register a command
     */
    private registerCommand;
    /**
     * Execute a command
     */
    execute(input: string): Promise<CommandResult>;
    private handleIntentCommand;
    private handleFormalCommand;
    private handleTestCommand;
    private handleCodeCommand;
    private handleVerifyCommand;
    private handleOperateCommand;
    private handleInitCommand;
    private handleStatusCommand;
    private handleNextCommand;
    private handleApproveCommand;
    private handleCompleteCommand;
    private handleHelpCommand;
    private handleSteeringCommand;
    private handleContextCommand;
    private handleTimelineCommand;
    private handleRunCommand;
    /**
     * Get list of available commands
     */
    getCommands(): SlashCommand[];
    /**
     * Parse command from text (extract commands from natural text)
     */
    parseCommandFromText(text: string): string[];
    /**
     * Execute multiple commands in sequence
     */
    executeSequence(commands: string[]): Promise<CommandResult[]>;
}

// ---- src/commands/tdd/guard.d.ts ----
export declare function tddGuard(): Promise<void>;

// ---- src/commands/verify/run.d.ts ----
import { type Result } from '../../core/result.js';
import type { AppError } from '../../core/errors.js';
export declare function verifyRun(): Promise<Result<{
    logs: string[];
    duration: string;
}, AppError>>;

// ---- src/conformance/monitors/api-contract-monitor.d.ts ----
/**
 * API Contract Monitor
 * Phase 2.2: Runtime monitor for API contract conformance verification
 */
import { ConformanceMonitor, ConformanceRule, RuntimeContext, VerificationResult } from '../types.js';
interface APIContractSpec {
    method: string;
    path: string;
    requestSchema?: any;
    responseSchema?: any;
    headers?: Record<string, string>;
    statusCodes?: number[];
    timeout?: number;
    rateLimit?: {
        requests: number;
        window: number;
    };
}
export declare class APIContractMonitor implements ConformanceMonitor {
    readonly id = "api-contract-monitor";
    readonly name = "API Contract Monitor";
    private rules;
    private contractSpecs;
    private rateLimitTracker;
    /**
     * Verify API call against contract rules
     */
    verify(data: any, context: RuntimeContext): Promise<VerificationResult>;
    /**
     * Check if this monitor can verify a specific rule
     */
    canVerify(ruleId: string): boolean;
    /**
     * Get all rules managed by this monitor
     */
    getRules(): ConformanceRule[];
    /**
     * Update a rule
     */
    updateRule(rule: ConformanceRule): Promise<void>;
    /**
     * Remove a rule
     */
    removeRule(ruleId: string): Promise<void>;
    /**
     * Add API contract specification
     */
    addContractSpec(path: string, spec: APIContractSpec): void;
    /**
     * Remove API contract specification
     */
    removeContractSpec(path: string): void;
    /**
     * Validate API call against contract
     */
    private validateAPIContract;
    /**
     * Check if data is valid API call data
     */
    private isAPICallData;
    /**
     * Find matching contract specification
     */
    private findMatchingContract;
    /**
     * Check if path matches pattern (supports basic wildcards)
     */
    private matchesPathPattern;
    /**
     * Normalize path pattern for consistent storage
     */
    private normalizePathPattern;
    /**
     * Find missing required headers
     */
    private findMissingHeaders;
    /**
     * Check rate limiting
     */
    private checkRateLimit;
    /**
     * Validate data against schema
     */
    private validateSchema;
    /**
     * Validate path parameters
     */
    private validatePathParameters;
    /**
     * Create violation details
     */
    private createViolation;
    /**
     * Generate API-specific suggestions
     */
    private generateAPISuggestions;
    /**
     * Map severity to priority
     */
    private mapSeverityToPriority;
    /**
     * Get memory usage (if available)
     */
    private getMemoryUsage;
    /**
     * Create common API contract rules
     */
    static createCommonRules(): ConformanceRule[];
}
export {};

// ---- src/conformance/monitors/data-validation-monitor.d.ts ----
/**
 * Data Validation Monitor
 * Phase 2.2: Runtime monitor for data validation conformance rules
 */
import { ConformanceMonitor, ConformanceRule, RuntimeContext, VerificationResult } from '../types.js';
export declare class DataValidationMonitor implements ConformanceMonitor {
    readonly id = "data-validation-monitor";
    readonly name = "Data Validation Monitor";
    private rules;
    private schemaCache;
    /**
     * Verify data against validation rules
     */
    verify(data: any, context: RuntimeContext): Promise<VerificationResult>;
    /**
     * Check if this monitor can verify a specific rule
     */
    canVerify(ruleId: string): boolean;
    /**
     * Get all rules managed by this monitor
     */
    getRules(): ConformanceRule[];
    /**
     * Update a rule
     */
    updateRule(rule: ConformanceRule): Promise<void>;
    /**
     * Remove a rule
     */
    removeRule(ruleId: string): Promise<void>;
    /**
     * Validate data against a specific rule
     */
    private validateAgainstRule;
    /**
     * Parse validation schema from rule condition
     */
    private parseValidationSchema;
    /**
     * Apply constraints to Zod schema
     */
    private applyConstraints;
    /**
     * Perform custom validation logic when schema parsing fails
     */
    private performCustomValidation;
    /**
     * Generate validation suggestions based on Zod errors
     */
    private generateValidationSuggestions;
    /**
     * Map severity to priority
     */
    private mapSeverityToPriority;
    /**
     * Get memory usage (if available)
     */
    private getMemoryUsage;
    /**
     * Create common validation rules
     */
    static createCommonRules(): ConformanceRule[];
}

// ---- src/conformance/rule-engine.d.ts ----
/**
 * Conformance Rule Engine
 * Phase 2.2: Core engine for executing conformance rules and detecting violations
 */
import { ConformanceRule, ConformanceConfig, RuntimeContext, VerificationResult, ConformanceVerificationResult, ConformanceRuleCategory } from './types.js';
export declare class ConformanceRuleEngine {
    private rules;
    private config;
    private executionCache;
    private metrics;
    constructor(config: ConformanceConfig);
    /**
     * Add a conformance rule to the engine
     */
    addRule(rule: ConformanceRule): Promise<void>;
    /**
     * Remove a rule from the engine
     */
    removeRule(ruleId: string): Promise<void>;
    /**
     * Update an existing rule
     */
    updateRule(rule: ConformanceRule): Promise<void>;
    /**
     * Get all loaded rules
     */
    getRules(): ConformanceRule[];
    /**
     * Get rules by category
     */
    getRulesByCategory(category: ConformanceRuleCategory): ConformanceRule[];
    /**
     * Verify data against all applicable rules
     */
    verifyConformance(data: any, context: RuntimeContext, ruleIds?: string[]): Promise<ConformanceVerificationResult>;
    /**
     * Verify a single rule
     */
    verifyRule(ruleId: string, data: any, context: RuntimeContext): Promise<VerificationResult>;
    /**
     * Execute a single conformance rule
     */
    private executeRule;
    /**
     * Evaluate rule condition against data
     */
    private evaluateRule;
    /**
     * Evaluate a condition expression
     */
    private evaluateCondition;
    /**
     * Safe expression evaluation (simplified)
     */
    private safeEvaluate;
    /**
     * Get nested property from object
     */
    private getNestedProperty;
    /**
     * Execute rules in parallel with concurrency limits
     */
    private executeRulesParallel;
    /**
     * Select rules to execute based on configuration
     */
    private selectRules;
    /**
     * Apply sampling configuration
     */
    private applySampling;
    /**
     * Helper methods
     */
    private executeWithTimeout;
    private createSkippedResult;
    private generateCacheKey;
    private isCacheValid;
    private clearRuleCache;
    private getMemoryUsage;
    private getValidatorHelpers;
    private getUtilityHelpers;
    private generateRemediationSuggestions;
    private mapSeverityToPriority;
    private determineOverallStatus;
    private generateSummary;
    private updateMetrics;
    private getRuleFailureRate;
    private shuffleArray;
    /**
     * Get engine metrics
     */
    getMetrics(): Record<string, number>;
    /**
     * Reset engine metrics
     */
    resetMetrics(): void;
}

// ---- src/conformance/types.d.ts ----
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

// ---- src/conformance/verification-engine.d.ts ----
/**
 * Conformance Verification Engine
 * Phase 2.2: Central orchestrator for runtime conformance verification
 */
import { EventEmitter } from 'events';
import { ConformanceRule, ConformanceConfig, RuntimeContext, ConformanceVerificationResult, ConformanceMonitor, ViolationHandler, ConformanceMetrics, ConformanceRuleCategory } from './types.js';
export declare class ConformanceVerificationEngine extends EventEmitter {
    private config;
    private ruleEngine;
    private monitors;
    private violationHandlers;
    private metrics;
    private isRunning;
    private verificationCount;
    private violationCount;
    constructor(config: ConformanceConfig);
    /**
     * Start the verification engine
     */
    start(): Promise<void>;
    /**
     * Stop the verification engine
     */
    stop(): Promise<void>;
    /**
     * Verify data against all applicable rules
     */
    verify(data: any, context: RuntimeContext, options?: {
        ruleIds?: string[];
        skipCategories?: ConformanceRuleCategory[];
        async?: boolean;
    }): Promise<ConformanceVerificationResult>;
    /**
     * Add a conformance rule
     */
    addRule(rule: ConformanceRule): Promise<void>;
    /**
     * Update a conformance rule
     */
    updateRule(rule: ConformanceRule): Promise<void>;
    /**
     * Remove a conformance rule
     */
    removeRule(ruleId: string): Promise<void>;
    /**
     * Get all rules
     */
    getRules(): ConformanceRule[];
    /**
     * Get rules by category
     */
    getRulesByCategory(category: ConformanceRuleCategory): ConformanceRule[];
    /**
     * Add a specialized monitor
     */
    addMonitor(monitor: ConformanceMonitor): void;
    /**
     * Remove a specialized monitor
     */
    removeMonitor(monitorId: string): void;
    /**
     * Add a violation handler
     */
    addViolationHandler(category: ConformanceRuleCategory, handler: ViolationHandler): void;
    /**
     * Remove a violation handler
     */
    removeViolationHandler(category: ConformanceRuleCategory, handler: ViolationHandler): void;
    /**
     * Get current metrics
     */
    getMetrics(): ConformanceMetrics;
    /**
     * Reset metrics
     */
    resetMetrics(): void;
    /**
     * Get engine configuration
     */
    getConfig(): ConformanceConfig;
    /**
     * Update engine configuration
     */
    updateConfig(newConfig: Partial<ConformanceConfig>): void;
    /**
     * Setup default monitors
     */
    private setupDefaultMonitors;
    /**
     * Run specialized monitors
     */
    private runSpecializedMonitors;
    /**
     * Merge results from different sources
     */
    private mergeResults;
    /**
     * Handle violations asynchronously
     */
    private handleViolationsAsync;
    /**
     * Handle violations synchronously
     */
    private handleViolationsSync;
    /**
     * Handle a single violation
     */
    private handleSingleViolation;
    /**
     * Calculate result summary
     */
    private calculateSummary;
    /**
     * Determine overall status from results
     */
    private determineOverallStatus;
    /**
     * Update metrics with verification result
     */
    private updateMetrics;
    /**
     * Initialize metrics structure
     */
    private initializeMetrics;
    /**
     * Start periodic metrics collection
     */
    private startMetricsCollection;
}

// ---- src/core/assertNever.d.ts ----
export declare function assertNever(x: never, msg?: string): never;

// ---- src/core/config.d.ts ----
import { z } from 'zod';
export declare const AeConfigSchema: z.ZodObject<{
    tddGuard: z.ZodDefault<z.ZodObject<{
        enabled: z.ZodDefault<z.ZodBoolean>;
        onlyChanged: z.ZodDefault<z.ZodBoolean>;
        changedSince: z.ZodDefault<z.ZodString>;
        include: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        exclude: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        allowSkipWithEnv: z.ZodDefault<z.ZodString>;
        ciOnly: z.ZodDefault<z.ZodBoolean>;
    }, "strip", z.ZodTypeAny, {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    }, {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    }>>;
    qa: z.ZodDefault<z.ZodObject<{
        coverageThreshold: z.ZodDefault<z.ZodObject<{
            branches: z.ZodDefault<z.ZodNumber>;
            lines: z.ZodDefault<z.ZodNumber>;
            functions: z.ZodDefault<z.ZodNumber>;
            statements: z.ZodDefault<z.ZodNumber>;
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
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    }, {
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    }>>;
    bench: z.ZodDefault<z.ZodObject<{
        warmupMs: z.ZodDefault<z.ZodNumber>;
        iterations: z.ZodDefault<z.ZodNumber>;
        seed: z.ZodDefault<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    }, {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    }>>;
}, "strict", z.ZodTypeAny, {
    tddGuard?: {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    };
    qa?: {
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    };
    bench?: {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    };
}, {
    tddGuard?: {
        enabled?: boolean;
        onlyChanged?: boolean;
        changedSince?: string;
        include?: string[];
        exclude?: string[];
        allowSkipWithEnv?: string;
        ciOnly?: boolean;
    };
    qa?: {
        coverageThreshold?: {
            branches?: number;
            lines?: number;
            functions?: number;
            statements?: number;
        };
    };
    bench?: {
        warmupMs?: number;
        iterations?: number;
        seed?: number;
    };
}>;
export type AeConfig = z.infer<typeof AeConfigSchema>;
export declare function loadConfig(): Promise<AeConfig>;

// ---- src/core/errors.d.ts ----
export type AppError = {
    code: 'E_EXEC';
    step: string;
    detail?: string;
} | {
    code: 'E_PARSE';
    step: string;
    detail?: string;
} | {
    code: 'E_TIMEOUT';
    step: string;
    ms: number;
} | {
    code: 'E_CONFIG';
    key: string;
    detail?: string;
};

// ---- src/core/exec.d.ts ----
import { type Result } from './result.js';
import type { AppError } from './errors.js';
export declare function run(step: string, cmd: string, args: string[], opts?: any): Promise<Result<{
    stdout: string;
}, AppError>>;

// ---- src/core/result.d.ts ----
export type Ok<T> = {
    ok: true;
    value: T;
};
export type Err<E extends {
    code: string;
}> = {
    ok: false;
    error: E;
};
export type Result<T, E extends {
    code: string;
} = {
    code: string;
    message?: string;
}> = Ok<T> | Err<E>;
export declare const ok: <T>(value: T) => Ok<T>;
export declare const err: <E extends {
    code: string;
}>(e: E) => Err<E>;
export declare function isOk<T, E extends {
    code: string;
}>(r: Result<T, E>): r is Ok<T>;
export declare function isErr<T, E extends {
    code: string;
}>(r: Result<T, E>): r is Err<E>;
export declare function unwrap<T, E extends {
    code: string;
}>(r: Result<T, E>): T;

// ---- src/core/seed.d.ts ----
export declare function getSeed(): number | undefined;

// ---- src/domain/contracts.d.ts ----
import { z } from "zod";
export declare const Reservation: z.ZodObject<{
    orderId: z.ZodString;
    itemId: z.ZodString;
    quantity: z.ZodNumber;
}, "strip", z.ZodTypeAny, {
    orderId?: string;
    itemId?: string;
    quantity?: number;
}, {
    orderId?: string;
    itemId?: string;
    quantity?: number;
}>;
export type Reservation = z.infer<typeof Reservation>;

// ---- src/domain/entities.d.ts ----
export interface Item {
    id: string;
    name: string;
    stock: number;
    reserved: number;
}
export interface ReservationEntity {
    id: string;
    orderId: string;
    itemId: string;
    quantity: number;
    createdAt: Date;
    status: 'pending' | 'confirmed' | 'cancelled';
}
export declare class InsufficientStockError extends Error {
    constructor(itemId: string, requested: number, available: number);
}

// ---- src/domain/services.d.ts ----
import { Item, ReservationEntity } from './entities.js';
import { Reservation } from './contracts.js';
export interface InventoryService {
    checkAvailability(itemId: string, quantity: number): Promise<boolean>;
    createReservation(reservation: Reservation): Promise<ReservationEntity>;
    getItem(itemId: string): Promise<Item | null>;
}
export declare class InventoryServiceImpl implements InventoryService {
    private _db;
    constructor(_db: any);
    checkAvailability(itemId: string, quantity: number): Promise<boolean>;
    createReservation(reservation: Reservation): Promise<ReservationEntity>;
    getItem(_itemId: string): Promise<Item | null>;
}

// ---- src/engines/sequential-inference-engine.d.ts ----
/**
 * Sequential Inference Engine for ae-framework
 * Provides multi-step reasoning with validation and rollback capabilities
 */
import { EventEmitter } from 'events';
export interface ComplexQuery {
    id: string;
    description: string;
    context: Record<string, any>;
    constraints: Constraint[];
    expectedOutcome?: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
}
export interface Constraint {
    type: 'logical' | 'temporal' | 'resource' | 'dependency';
    condition: string;
    severity: 'warning' | 'error' | 'critical';
}
export interface InferenceStep {
    id: string;
    description: string;
    input: Record<string, any>;
    output?: Record<string, any>;
    confidence: number;
    duration: number;
    dependencies: string[];
    status: 'pending' | 'running' | 'completed' | 'failed' | 'skipped';
    error?: Error;
}
export interface InferenceResult {
    queryId: string;
    success: boolean;
    confidence: number;
    totalSteps: number;
    completedSteps: number;
    steps: InferenceStep[];
    finalResult?: any;
    error?: Error;
    metadata: {
        startTime: Date;
        endTime?: Date;
        duration: number;
        memoryUsed: number;
        cacheHits: number;
    };
}
export interface ProjectContext {
    projectRoot: string;
    packageJson?: any;
    tsConfig?: any;
    sourceFiles: string[];
    dependencies: Record<string, string>;
    devDependencies: Record<string, string>;
    buildConfig?: any;
}
export interface DependencyNode {
    id: string;
    type: 'file' | 'module' | 'function' | 'class';
    path: string;
    dependencies: string[];
    dependents: string[];
    weight: number;
    metadata: Record<string, any>;
}
export interface DependencyGraph {
    nodes: DependencyNode[];
    edges: Array<{
        from: string;
        to: string;
        type: string;
        weight: number;
    }>;
    cycles: string[][];
    criticalPaths: string[][];
    metrics: {
        totalNodes: number;
        totalEdges: number;
        cycleCount: number;
        maxDepth: number;
        fanOut: Record<string, number>;
    };
}
export interface ChangeSet {
    id: string;
    description: string;
    files: FileChange[];
    timestamp: Date;
    author: string;
}
export interface FileChange {
    path: string;
    type: 'create' | 'modify' | 'delete' | 'rename';
    oldPath?: string;
    content?: string;
    lines?: {
        added: number;
        removed: number;
        modified: number;
    };
}
export interface ImpactAnalysis {
    changeSetId: string;
    affectedComponents: AffectedComponent[];
    riskLevel: 'low' | 'medium' | 'high' | 'critical';
    estimatedEffort: number;
    recommendations: string[];
    testingRequirements: TestRequirement[];
    rollbackPlan?: string[];
}
export interface AffectedComponent {
    id: string;
    path: string;
    type: 'direct' | 'indirect' | 'cascade';
    impactLevel: 'minimal' | 'moderate' | 'significant' | 'critical';
    description: string;
    dependencies: string[];
}
export interface TestRequirement {
    type: 'unit' | 'integration' | 'e2e' | 'performance';
    priority: 'low' | 'medium' | 'high' | 'critical';
    description: string;
    estimatedTime: number;
}
export declare class SequentialInferenceEngine extends EventEmitter {
    private options;
    private cache;
    private activeQueries;
    private stepHandlers;
    constructor(options?: {
        maxConcurrentQueries?: number;
        cacheSize?: number;
        timeoutMs?: number;
        enableProfiling?: boolean;
    });
    /**
     * Process a complex query using sequential reasoning
     */
    processComplexQuery(query: ComplexQuery): Promise<InferenceResult>;
    /**
     * Analyze deep dependencies in a project context
     */
    analyzeDeepDependencies(context: ProjectContext): Promise<DependencyGraph>;
    /**
     * Evaluate the impact scope of changes
     */
    evaluateImpactScope(changes: ChangeSet): Promise<ImpactAnalysis>;
    private registerDefaultHandlers;
    private decomposeQuery;
    private checkStepDependencies;
    private executeStep;
    private validateStepResult;
    private shouldAbortOnStepFailure;
    private synthesizeResult;
    private handleAnalyzeStep;
    private handleValidateStep;
    private handleSynthesizeStep;
    private analyzeFileDependencies;
    private detectCycles;
    private findCriticalPaths;
    private calculateMaxDepth;
    private calculateFanOut;
    private analyzeDirectImpacts;
    private analyzeIndirectImpacts;
    private calculateRiskLevel;
    private estimateEffort;
    private generateRecommendations;
    private defineTestingRequirements;
    private createRollbackPlan;
    private getMemoryUsage;
}

// ---- src/generators/ui-scaffold-generator.d.ts ----
interface PhaseState {
    entities: Record<string, EntityDefinition>;
    ui_preferences?: UIPreferences;
    relationships?: Record<string, any>;
}
interface EntityDefinition {
    description: string;
    attributes: Record<string, AttributeDefinition>;
    constraints?: any;
    acceptance_criteria?: string[];
}
interface AttributeDefinition {
    type: string;
    required: boolean;
    validation?: string;
    description: string;
    default?: any;
}
interface UIPreferences {
    theme?: string;
    layout?: string;
    components?: string;
    styling?: string;
    forms?: string;
    validation?: string;
    data_fetching?: string;
    testing?: string;
}
interface GeneratorOptions {
    outputDir: string;
    dryRun?: boolean;
    overwrite?: boolean;
    targetEntity?: string;
}
interface GenerationResult {
    success: boolean;
    files: string[];
    error?: string;
}
export declare class UIScaffoldGenerator {
    private phaseState;
    private options;
    private templatesDir;
    constructor(phaseState: PhaseState, options: GeneratorOptions);
    private findFrameworkRoot;
    generateAll(): Promise<Record<string, GenerationResult>>;
    private generateEntityUI;
    private buildTemplateContext;
    private findDisplayNameField;
    private findDescriptionField;
    private findStatusField;
    private getEditableAttributes;
    private getDisplayAttributes;
    private getCardDisplayFields;
    private getTimestampFields;
    private getRequiredFormFields;
    private getOptionalFormFields;
    private getEnumOptions;
    private renderTemplate;
    private writeFile;
    validatePhaseState(): {
        valid: boolean;
        errors: string[];
        entityCount: number;
        uiFramework: string;
    };
    private registerHandlebarsHelpers;
}
export {};

// ---- src/health/health-endpoint.d.ts ----
/**
 * Health Check Endpoint for ae-framework
 * Phase 1.4: Docker production optimization health checks
 */
import { FastifyInstance } from 'fastify';
export interface HealthStatus {
    status: 'healthy' | 'unhealthy' | 'degraded';
    timestamp: string;
    uptime: number;
    version: string;
    environment: string;
    checks: {
        memory: {
            status: 'ok' | 'warning' | 'critical';
            used: number;
            total: number;
            percentage: number;
        };
        system: {
            status: 'ok' | 'error';
            nodeVersion: string;
            platform: string;
        };
        telemetry: {
            status: 'ok' | 'error';
            message: string;
        };
    };
}
export declare function registerHealthEndpoint(fastify: FastifyInstance): Promise<void>;

// ---- src/index.d.ts ----
export {};

// ---- src/inference/core/problem-decomposer.d.ts ----
/**
 * Problem Decomposer for Complex Problem Solving Framework
 * Breaks down complex problems into manageable sub-problems
 */
export interface Problem {
    id: string;
    title: string;
    description: string;
    domain: string;
    complexity: 'low' | 'medium' | 'high' | 'critical';
    priority: 'low' | 'medium' | 'high' | 'critical';
    constraints: Constraint[];
    context: Record<string, any>;
    expectedOutcome?: string;
    deadline?: Date;
}
export interface Constraint {
    id: string;
    type: 'resource' | 'time' | 'quality' | 'dependency' | 'business' | 'technical';
    description: string;
    importance: 'low' | 'medium' | 'high' | 'critical';
    value?: any;
    operator?: '>' | '<' | '>=' | '<=' | '=' | '!=' | 'in' | 'not_in';
}
export interface SubProblem {
    id: string;
    parentId: string;
    title: string;
    description: string;
    type: 'sequential' | 'parallel' | 'conditional' | 'loop';
    dependencies: string[];
    estimatedComplexity: number;
    estimatedTime: number;
    requiredResources: string[];
    constraints: Constraint[];
    successCriteria: string[];
    fallbackStrategies: string[];
}
export interface DecompositionResult {
    originalProblem: Problem;
    subProblems: SubProblem[];
    executionPlan: ExecutionNode[];
    estimatedTotalTime: number;
    criticalPath: string[];
    riskAssessment: RiskAssessment;
    recommendations: string[];
}
export interface ExecutionNode {
    id: string;
    subProblemId: string;
    phase: number;
    canRunInParallel: boolean;
    dependencies: string[];
    estimatedStartTime: number;
    estimatedEndTime: number;
}
export interface RiskAssessment {
    overallRisk: 'low' | 'medium' | 'high' | 'critical';
    riskFactors: RiskFactor[];
    mitigationStrategies: MitigationStrategy[];
    contingencyPlan: string[];
}
export interface RiskFactor {
    id: string;
    description: string;
    probability: number;
    impact: number;
    category: 'technical' | 'resource' | 'time' | 'quality' | 'external';
    mitigation?: string;
}
export interface MitigationStrategy {
    riskId: string;
    strategy: string;
    cost: number;
    effectiveness: number;
    timeRequired: number;
}
export declare class ProblemDecomposer {
    private decompositionStrategies;
    private complexityAnalyzers;
    constructor();
    /**
     * Decompose a complex problem into manageable sub-problems
     */
    decompose(problem: Problem): Promise<DecompositionResult>;
    /**
     * Register a custom decomposition strategy
     */
    registerDecompositionStrategy(domain: string, strategy: (problem: Problem) => SubProblem[]): void;
    /**
     * Register a custom complexity analyzer
     */
    registerComplexityAnalyzer(domain: string, analyzer: (problem: Problem) => number): void;
    private registerDefaultStrategies;
    private registerDefaultAnalyzers;
    private validateProblem;
    private analyzeComplexity;
    private selectDecompositionStrategy;
    private generateSubProblems;
    private decomposeSoftwareProblem;
    private decomposeDataProblem;
    private decomposeSystemProblem;
    private decomposeDebuggingProblem;
    private decomposeOptimizationProblem;
    private decomposeGenericProblem;
    private analyzeSoftwareComplexity;
    private analyzeDataComplexity;
    private analyzeGenericComplexity;
    private applyDecompositionStrategy;
    private applyHierarchicalStrategy;
    private applyModularStrategy;
    private applySequentialStrategy;
    private optimizeSubProblems;
    private removeRedundantDependencies;
    private balanceWorkload;
    private createExecutionPlan;
    private calculateTotalTime;
    private findCriticalPath;
    private performRiskAssessment;
    private findLongDependencyChains;
    private calculateOverallRisk;
    private generateMitigationStrategies;
    private createContingencyPlan;
    private generateRecommendations;
}

// ---- src/inference/core/reasoning-engine.d.ts ----
/**
 * Core Reasoning Engine for ae-framework
 * Orchestrates different reasoning strategies and manages inference processes
 */
import { EventEmitter } from 'events';
import { SequentialStrategy } from '../strategies/sequential-strategy.js';
import { ParallelStrategy } from '../strategies/parallel-strategy.js';
import type { ReasoningContext, StrategyResult } from '../strategies/sequential-strategy.js';
export type ReasoningMode = 'sequential' | 'parallel' | 'adaptive' | 'hybrid';
export interface ReasoningRequest {
    id: string;
    mode: ReasoningMode;
    context: ReasoningContext;
    timeout?: number;
    priority?: 'low' | 'medium' | 'high' | 'critical';
    options?: {
        maxRetries?: number;
        fallbackMode?: ReasoningMode;
        validateResults?: boolean;
        cacheResults?: boolean;
    };
}
export interface ReasoningSession {
    id: string;
    startTime: Date;
    endTime?: Date;
    status: 'pending' | 'running' | 'completed' | 'failed' | 'timeout';
    request: ReasoningRequest;
    result?: StrategyResult;
    error?: Error;
    metrics: {
        duration: number;
        memoryUsed: number;
        strategySwitches: number;
        cacheHits: number;
    };
}
export interface EngineMetrics {
    totalRequests: number;
    successfulRequests: number;
    failedRequests: number;
    averageProcessingTime: number;
    averageConfidence: number;
    strategyUsage: Record<ReasoningMode, number>;
    memoryUsage: {
        current: number;
        peak: number;
        average: number;
    };
    cacheStatistics: {
        size: number;
        hitRate: number;
        evictions: number;
    };
}
export declare class ReasoningEngine extends EventEmitter {
    private options;
    private sequentialStrategy;
    private parallelStrategy;
    private activeSessions;
    private resultCache;
    private metrics;
    constructor(options?: {
        maxConcurrentSessions?: number;
        defaultTimeout?: number;
        cacheSize?: number;
        cacheTTL?: number;
        enableMetrics?: boolean;
    });
    /**
     * Process a reasoning request
     */
    processRequest(request: ReasoningRequest): Promise<StrategyResult>;
    /**
     * Get current engine metrics
     */
    getMetrics(): EngineMetrics;
    /**
     * Clear all caches and reset metrics
     */
    reset(): void;
    /**
     * Register custom reasoning strategies
     */
    registerStrategy(mode: string, strategy: SequentialStrategy | ParallelStrategy): void;
    private validateRequest;
    private createSession;
    private executeStrategy;
    private selectAndExecuteStrategy;
    private executeAdaptiveStrategy;
    private executeHybridStrategy;
    private combineResults;
    private validateResult;
    private getCachedResult;
    private cacheResult;
    private generateCacheKey;
    private analyzeComplexity;
    private estimateDataSize;
    private hasParallelizableWork;
    private getCurrentMemoryUsage;
    private initializeMetrics;
    private updateMetrics;
    private performMaintenance;
}

// ---- src/inference/core/solution-composer.d.ts ----
/**
 * Solution Composer for Complex Problem Solving Framework
 * Integrates and validates solutions from sub-problems
 */
import type { DecompositionResult } from './problem-decomposer.js';
export interface SubSolution {
    subProblemId: string;
    success: boolean;
    confidence: number;
    result: any;
    metrics: {
        executionTime: number;
        resourcesUsed: string[];
        qualityScore: number;
    };
    validationResults: ValidationResult[];
    dependencies: Record<string, any>;
    error?: Error;
}
export interface ValidationResult {
    criterion: string;
    passed: boolean;
    score: number;
    details: string;
    importance: 'low' | 'medium' | 'high' | 'critical';
}
export interface CompositeSolution {
    problemId: string;
    success: boolean;
    overallConfidence: number;
    compositeResult: any;
    subSolutions: SubSolution[];
    integrationMetrics: {
        consistencyScore: number;
        completenessScore: number;
        qualityScore: number;
        performanceScore: number;
    };
    validationResults: GlobalValidationResult[];
    recommendations: string[];
    alternatives?: AlternativeSolution[];
}
export interface GlobalValidationResult {
    aspect: 'consistency' | 'completeness' | 'quality' | 'performance' | 'security';
    passed: boolean;
    score: number;
    details: string;
    requiredActions: string[];
}
export interface AlternativeSolution {
    id: string;
    description: string;
    confidence: number;
    tradeoffs: string[];
    estimatedImpact: {
        time: number;
        resources: number;
        quality: number;
    };
}
export interface CompositionStrategy {
    name: string;
    description: string;
    canHandle: (decomposition: DecompositionResult) => boolean;
    compose: (subSolutions: SubSolution[], context: CompositionContext) => Promise<any>;
    validate: (result: any, context: CompositionContext) => Promise<ValidationResult[]>;
}
export interface CompositionContext {
    originalProblem: any;
    decompositionResult: DecompositionResult;
    constraints: any[];
    qualityThresholds: Record<string, number>;
    integrationRules: IntegrationRule[];
}
export interface IntegrationRule {
    id: string;
    type: 'dependency' | 'consistency' | 'transformation' | 'validation';
    description: string;
    condition: (subSolutions: SubSolution[]) => boolean;
    action: (subSolutions: SubSolution[]) => SubSolution[] | void;
    priority: 'low' | 'medium' | 'high' | 'critical';
}
export declare class SolutionComposer {
    private strategies;
    private validators;
    private transformers;
    constructor();
    /**
     * Compose solutions from sub-problems into a complete solution
     */
    compose(subSolutions: SubSolution[], decompositionResult: DecompositionResult, context?: Partial<CompositionContext>): Promise<CompositeSolution>;
    /**
     * Register a custom composition strategy
     */
    registerCompositionStrategy(strategy: CompositionStrategy): void;
    /**
     * Register a custom validator
     */
    registerValidator(name: string, validator: (result: any, context: CompositionContext) => Promise<ValidationResult[]>): void;
    private registerDefaultStrategies;
    private registerDefaultValidators;
    private registerDefaultTransformers;
    private validateInputSolutions;
    private preprocessSolutions;
    private selectCompositionStrategy;
    private composeSequential;
    private composeParallel;
    private composeHierarchical;
    private composeHybrid;
    private performGlobalValidation;
    private calculateIntegrationMetrics;
    private determineOverallSuccess;
    private calculateOverallConfidence;
    private createDefaultIntegrationRules;
    private resolveDependencies;
    private resolveSubSolutionDependencies;
    private enforceConsistency;
    private normalizeQuality;
    private validateSequential;
    private validateParallel;
    private validateHierarchical;
    private validateHybrid;
    private validateConsistency;
    private validateCompleteness;
    private validateQuality;
    private validatePerformance;
    private validateSecurity;
    private sortByExecutionOrder;
    private groupByExecutionPhase;
    private buildHierarchy;
    private composeHierarchyRecursive;
    private calculateHierarchyLevels;
    private isSequentialSolution;
    private isParallelSolution;
    private integrateHybridResults;
    private hasHierarchicalStructure;
    private applyIntegrationRules;
    private getPriorityValue;
    private generateRecommendations;
    private generateAlternatives;
}

// ---- src/inference/core/validation-orchestrator.d.ts ----
/**
 * Validation Orchestrator for Complex Problem Solving Framework
 * Coordinates validation processes across different solution components
 */
import { EventEmitter } from 'events';
import type { SubSolution, CompositeSolution, ValidationResult } from './solution-composer.js';
export interface ValidationPlan {
    id: string;
    description: string;
    phases: ValidationPhase[];
    totalValidators: number;
    estimatedDuration: number;
    requiredResources: string[];
    criticalityLevel: 'low' | 'medium' | 'high' | 'critical';
}
export interface ValidationPhase {
    id: string;
    name: string;
    description: string;
    validators: ValidatorConfig[];
    dependencies: string[];
    parallel: boolean;
    timeout: number;
    retryPolicy: RetryPolicy;
}
export interface ValidatorConfig {
    id: string;
    type: ValidationCategory;
    name: string;
    description: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    timeout: number;
    retries: number;
    parameters: Record<string, any>;
    successCriteria: SuccessCriteria;
}
export type ValidationCategory = 'structural' | 'functional' | 'performance' | 'security' | 'consistency' | 'completeness' | 'integration' | 'business_rules' | 'data_quality';
export interface SuccessCriteria {
    minScore: number;
    mustPass: boolean;
    allowableFailures?: number;
    customCondition?: (result: ValidationResult) => boolean;
}
export interface RetryPolicy {
    maxRetries: number;
    backoffStrategy: 'linear' | 'exponential' | 'fixed';
    baseDelayMs: number;
    maxDelayMs: number;
}
export interface ValidationExecution {
    planId: string;
    executionId: string;
    startTime: Date;
    endTime?: Date;
    status: 'pending' | 'running' | 'completed' | 'failed' | 'cancelled';
    currentPhase?: string;
    results: ValidationPhaseResult[];
    overallResult: OverallValidationResult;
    metrics: ValidationMetrics;
}
export interface ValidationPhaseResult {
    phaseId: string;
    success: boolean;
    startTime: Date;
    endTime: Date;
    duration: number;
    validatorResults: ValidatorExecutionResult[];
    phaseScore: number;
    criticalFailures: string[];
}
export interface ValidatorExecutionResult {
    validatorId: string;
    success: boolean;
    score: number;
    result: ValidationResult;
    executionTime: number;
    attempts: number;
    error?: Error;
}
export interface OverallValidationResult {
    success: boolean;
    overallScore: number;
    criticalityLevel: 'low' | 'medium' | 'high' | 'critical';
    summary: string;
    passedValidations: number;
    failedValidations: number;
    totalValidations: number;
    recommendations: string[];
    blockers: string[];
}
export interface ValidationMetrics {
    totalDuration: number;
    avgValidatorTime: number;
    successRate: number;
    retryCount: number;
    resourceUtilization: Record<string, number>;
    performanceScore: number;
}
export interface Validator {
    id: string;
    category: ValidationCategory;
    validate: (target: any, context: ValidationContext, config: ValidatorConfig) => Promise<ValidationResult>;
    canHandle: (target: any, context: ValidationContext) => boolean;
}
export interface ValidationContext {
    originalProblem?: any;
    subSolutions?: SubSolution[];
    compositeSolution?: CompositeSolution;
    constraints: any[];
    metadata: Record<string, any>;
}
export declare class ValidationOrchestrator extends EventEmitter {
    private options;
    private validators;
    private activeExecutions;
    private validationPlans;
    constructor(options?: {
        maxConcurrentValidations?: number;
        defaultTimeout?: number;
        enableMetrics?: boolean;
    });
    /**
     * Create a validation plan for a given context
     */
    createValidationPlan(target: any, context: ValidationContext, requirements?: {
        categories?: ValidationCategory[];
        criticalityLevel?: 'low' | 'medium' | 'high' | 'critical';
        maxDuration?: number;
    }): Promise<ValidationPlan>;
    /**
     * Execute a validation plan
     */
    executeValidationPlan(planId: string, target: any, context: ValidationContext): Promise<ValidationExecution>;
    /**
     * Register a custom validator
     */
    registerValidator(validator: Validator): void;
    /**
     * Get validation execution by ID
     */
    getExecution(executionId: string): ValidationExecution | undefined;
    /**
     * Cancel a running validation execution
     */
    cancelExecution(executionId: string): Promise<boolean>;
    private registerDefaultValidators;
    private selectValidators;
    private organizeValidatorsIntoPhases;
    private executeValidationPhase;
    private executeValidator;
    private executeWithTimeout;
    private evaluateValidationResult;
    private calculateRetryDelay;
    private validateStructureCompleteness;
    private validateStructureConsistency;
    private validateFunctionalCorrectness;
    private validatePerformanceMetrics;
    private validateSecurityCompliance;
    private validateDataQuality;
    private validateIntegrationCompatibility;
    private assessDataQuality;
    private hasDataContent;
    private getTargetDescription;
    private getValidatorName;
    private getValidatorDescription;
    private getValidatorPriority;
    private getPriorityValue;
    private estimateValidationDuration;
    private identifyRequiredResources;
    private createEmptyOverallResult;
    private createEmptyMetrics;
    private calculateOverallResult;
    private calculateMetrics;
    private generateValidationRecommendations;
}

// ---- src/inference/strategies/parallel-strategy.d.ts ----
/**
 * Parallel Strategy for Inference Engine
 * Implements concurrent reasoning with result aggregation
 */
import { ReasoningContext, StrategyResult } from './sequential-strategy.js';
export interface ParallelTask {
    id: string;
    description: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    dependencies: string[];
    input: any;
    estimatedDuration: number;
    maxRetries: number;
}
export interface TaskResult {
    taskId: string;
    success: boolean;
    result: any;
    duration: number;
    confidence: number;
    error?: Error;
}
export interface ParallelExecutionPlan {
    phases: TaskPhase[];
    totalTasks: number;
    estimatedDuration: number;
    resourceRequirements: string[];
}
export interface TaskPhase {
    id: string;
    tasks: ParallelTask[];
    canRunConcurrently: boolean;
    dependencies: string[];
}
export declare class ParallelStrategy {
    private maxConcurrency;
    private activeTaskCount;
    private taskProcessors;
    constructor(options?: {
        maxConcurrency?: number;
    });
    /**
     * Execute parallel reasoning strategy
     */
    execute(context: ReasoningContext): Promise<StrategyResult>;
    /**
     * Register a custom task processor
     */
    registerTaskProcessor(taskType: string, processor: (task: ParallelTask) => Promise<any>): void;
    private registerDefaultProcessors;
    private createExecutionPlan;
    private createTasksFromContext;
    private organizeTasks;
    private executePhase;
    private executeTask;
    private getTaskProcessor;
    private enrichTaskInput;
    private processAnalysisTask;
    private processValidationTask;
    private processComputationTask;
    private processFetchTask;
    private aggregateResults;
    private extractPatterns;
    private calculateStatistics;
    private estimatePhaseTime;
    private identifyResourceRequirements;
    private getPriorityValue;
    private getStepTypeFromTask;
    private calculateTaskConfidence;
    private calculateOverallConfidence;
}

// ---- src/inference/strategies/sequential-strategy.d.ts ----
/**
 * Sequential Strategy for Inference Engine
 * Implements step-by-step reasoning with validation
 */
export interface ReasoningStep {
    id: string;
    type: 'analyze' | 'deduce' | 'validate' | 'synthesize';
    description: string;
    input: any;
    output?: any;
    confidence: number;
    metadata: {
        startTime: Date;
        endTime?: Date;
        duration: number;
        resources: string[];
    };
}
export interface ReasoningContext {
    domain: string;
    constraints: any[];
    objectives: string[];
    availableData: Record<string, any>;
    previousSteps: ReasoningStep[];
}
export interface StrategyResult {
    success: boolean;
    steps: ReasoningStep[];
    finalConclusion: any;
    confidence: number;
    reasoning: string[];
}
export declare class SequentialStrategy {
    private stepProcessors;
    constructor();
    /**
     * Execute sequential reasoning strategy
     */
    execute(context: ReasoningContext): Promise<StrategyResult>;
    /**
     * Register a custom step processor
     */
    registerStepProcessor(type: string, processor: (step: ReasoningStep, context: ReasoningContext) => Promise<any>): void;
    private registerDefaultProcessors;
    private createAnalysisStep;
    private createDeductionStep;
    private createValidationStep;
    private createSynthesisStep;
    private processStep;
    private processAnalysisStep;
    private processDeductionStep;
    private processValidationStep;
    private processSynthesisStep;
    private identifyPatterns;
    private isRelevantConstraint;
    private assessDataQuality;
    private generateHypotheses;
    private filterByConstraints;
    private checkConstraint;
    private validateConclusions;
    private extractKeyFindings;
    private generateRecommendations;
    private calculateStepConfidence;
    private calculateOverallConfidence;
}

// ---- src/infra/db.d.ts ----
import pg from 'pg';
export declare class Database {
    private pool;
    constructor(connectionString: string);
    query(text: string, params?: any[]): Promise<import("pg").QueryResult<any>>;
    transaction<T>(callback: (client: pg.PoolClient) => Promise<T>): Promise<T>;
    close(): Promise<void>;
}
export declare function initDatabase(db: Database): Promise<void>;

// ---- src/infra/telemetry.d.ts ----
import { NodeSDK } from '@opentelemetry/sdk-node';
export declare function initTelemetry(serviceName?: string): NodeSDK;

// ---- src/integration/circuit-breaker-integration.d.ts ----
import { CircuitBreaker } from '../utils/circuit-breaker.js';
import { EventEmitter } from 'events';
/**
 * AE-Framework specific error types for circuit breaker filtering
 */
export declare class AgentCommunicationError extends Error {
    constructor(message: string);
}
export declare class StateManagementError extends Error {
    constructor(message: string);
}
export declare class PhaseTransitionError extends Error {
    constructor(message: string);
}
export declare class ExternalServiceError extends Error {
    constructor(message: string);
}
export declare class ResourceExhaustionError extends Error {
    constructor(message: string);
}
/**
 * Circuit Breaker Integration for AE-Framework Components
 */
export declare class AEFrameworkCircuitBreakerIntegration extends EventEmitter {
    private static instance;
    private constructor();
    /**
     * Get singleton instance
     */
    static getInstance(): AEFrameworkCircuitBreakerIntegration;
    /**
     * Get circuit breaker for agent communication
     */
    getAgentCircuitBreaker(agentName: string): CircuitBreaker;
    /**
     * Get circuit breaker for state management operations
     */
    getStateManagementCircuitBreaker(): CircuitBreaker;
    /**
     * Get circuit breaker for phase transitions
     */
    getPhaseTransitionCircuitBreaker(): CircuitBreaker;
    /**
     * Get circuit breaker for external service calls
     */
    getExternalServiceCircuitBreaker(serviceName: string): CircuitBreaker;
    /**
     * Get circuit breaker for resource-intensive operations
     */
    getResourceCircuitBreaker(resourceType: string): CircuitBreaker;
    /**
     * Execute agent operation with circuit breaker protection
     */
    executeAgentOperation<T>(agentName: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute state management operation with circuit breaker protection
     */
    executeStateOperation<T>(operationType: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute phase transition with circuit breaker protection
     */
    executePhaseTransition<T>(fromPhase: string, toPhase: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute external service call with circuit breaker protection
     */
    executeExternalServiceCall<T>(serviceName: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Execute resource-intensive operation with circuit breaker protection
     */
    executeResourceOperation<T>(resourceType: string, operation: () => Promise<T>, context?: any): Promise<T>;
    /**
     * Get comprehensive health status for all AE-Framework circuit breakers
     */
    getFrameworkHealthStatus(): {
        overall: 'healthy' | 'degraded' | 'critical';
        components: {
            agents: {
                [agentName: string]: 'healthy' | 'degraded' | 'critical';
            };
            stateManagement: 'healthy' | 'degraded' | 'critical';
            phaseTransitions: 'healthy' | 'degraded' | 'critical';
            externalServices: {
                [serviceName: string]: 'healthy' | 'degraded' | 'critical';
            };
            resources: {
                [resourceType: string]: 'healthy' | 'degraded' | 'critical';
            };
        };
        recommendations: string[];
    };
    /**
     * Reset all framework circuit breakers
     */
    resetAllCircuitBreakers(): void;
    private agentFallback;
    private stateManagementFallback;
    private phaseTransitionFallback;
    private externalServiceFallback;
    private resourceFallback;
    private setupGlobalEventHandlers;
}
export declare const aeFrameworkCircuitBreakers: AEFrameworkCircuitBreakerIntegration;
/**
 * Decorator for adding circuit breaker protection to methods
 */
export declare function WithCircuitBreaker(breakerName: string, options?: {
    failureThreshold?: number;
    successThreshold?: number;
    timeout?: number;
    expectedErrors?: Array<new (...args: any[]) => Error>;
    fallback?: (...args: any[]) => any;
}): (target: any, propertyKey: string, descriptor: PropertyDescriptor) => PropertyDescriptor;
/**
 * Utility functions for common circuit breaker patterns
 */
export declare class CircuitBreakerUtils {
    /**
     * Create a retry-with-circuit-breaker pattern
     */
    static executeWithRetryAndCircuitBreaker<T>(operation: () => Promise<T>, circuitBreaker: CircuitBreaker, retryOptions: {
        maxRetries: number;
        delayMs: number;
        backoffMultiplier?: number;
    }): Promise<T>;
    /**
     * Create a timeout-with-circuit-breaker pattern
     */
    static executeWithTimeoutAndCircuitBreaker<T>(operation: () => Promise<T>, circuitBreaker: CircuitBreaker, timeoutMs: number): Promise<T>;
    /**
     * Create a bulk operation with circuit breaker protection
     */
    static executeBulkWithCircuitBreaker<T, R>(items: T[], operation: (item: T) => Promise<R>, circuitBreaker: CircuitBreaker, options?: {
        concurrency?: number;
        failFast?: boolean;
    }): Promise<Array<{
        item: T;
        result?: R;
        error?: Error;
    }>>;
}

// ---- src/integration/hybrid-intent-system.d.ts ----
/**
 * Hybrid Intent System
 *
 * Integrates CLI tools, MCP server, and Claude Code agents
 * for comprehensive Intent analysis and Phase 1 guidance
 */
export interface HybridIntentConfig {
    enableCLI: boolean;
    enableMCPServer: boolean;
    enableClaudeCodeIntegration: boolean;
    enforceRealTime: boolean;
    strictMode: boolean;
}
export declare class HybridIntentSystem {
    private agent?;
    private taskAdapter?;
    private metricsCollector;
    private config;
    private periodicCheckIntervalId?;
    constructor(config: HybridIntentConfig);
    /**
     * Main entry point for Intent operations
     * Routes requests to appropriate handler based on context
     */
    handleIntentRequest(request: {
        type: 'cli' | 'task' | 'mcp' | 'auto';
        data: any;
        context?: {
            isClaudeCode: boolean;
            hasTaskTool: boolean;
            userPreference: string;
        };
    }): Promise<{
        response: any;
        source: 'cli' | 'agent' | 'hybrid';
        followUp?: string[];
    }>;
    /**
     * Proactive Intent monitoring and intervention
     * Runs in background to provide real-time guidance
     */
    startProactiveMonitoring(): Promise<void>;
    /**
     * Integration with existing development workflow
     */
    integrateWithWorkflow(workflow: {
        ide: string;
        vcs: string;
        ci: string;
        requirementsTool: string;
    }): Promise<{
        integrations: Array<{
            type: string;
            status: 'active' | 'available' | 'unavailable';
            setup: string[];
        }>;
    }>;
    private detectBestHandler;
    private handleCLIRequest;
    private handleTaskRequest;
    private handleMCPRequest;
    private handleHybridRequest;
    private executeIntentCommand;
    private executeMCPCommand;
    private combineResults;
    private generateCLIFollowUp;
    private generateAgentFollowUp;
    private setupRequirementWatchers;
    private setupGitIntegration;
    private startPeriodicChecks;
    /**
     * Clean up resources and stop periodic checks
     */
    cleanup(): void;
    private isRequirementFile;
    private handleRequirementChange;
    private checkIntentCompliance;
}
export declare const createHybridIntentSystem: (config?: Partial<HybridIntentConfig>) => HybridIntentSystem;

// ---- src/integration/hybrid-tdd-system.d.ts ----
/**
 * Hybrid TDD System
 *
 * Integrates CLI tools, MCP server, and Claude Code agents
 * for comprehensive TDD enforcement and guidance
 */
export interface HybridTDDConfig {
    enableCLI: boolean;
    enableMCPServer: boolean;
    enableClaudeCodeIntegration: boolean;
    enforceRealTime: boolean;
    strictMode: boolean;
    enableSpecSSot: boolean;
    specPath: string;
    aeIrOutputPath: string;
}
export declare class HybridTDDSystem {
    private cli?;
    private taskAdapter?;
    private metricsCollector;
    private config;
    private specCompiler;
    private stateManager;
    constructor(config: HybridTDDConfig);
    /**
     * Main entry point for TDD operations
     * Routes requests to appropriate handler based on context
     */
    handleTDDRequest(request: {
        type: 'cli' | 'task' | 'mcp' | 'auto';
        data: any;
        phase?: number;
        context?: {
            isClaudeCode: boolean;
            hasTaskTool: boolean;
            userPreference: string;
        };
    }): Promise<{
        response: any;
        source: 'cli' | 'agent' | 'hybrid';
        followUp?: string[];
    }>;
    /**
     * AE-Spec/IR SSOT Pipeline Processing
     * Converts NL specs to structured IR for downstream phases
     */
    private processSpecPipeline;
    /**
     * Check if current phase requires spec pipeline processing
     */
    private requiresSpecPipeline;
    /**
     * Proactive TDD monitoring and intervention
     * Runs in background to provide real-time guidance
     */
    startProactiveMonitoring(): Promise<void>;
    /**
     * Integration with existing development workflow
     */
    integrateWithWorkflow(workflow: {
        ide: string;
        vcs: string;
        ci: string;
        testRunner: string;
    }): Promise<{
        integrations: Array<{
            type: string;
            status: 'active' | 'available' | 'unavailable';
            setup: string[];
        }>;
    }>;
    private detectBestHandler;
    private handleCLIRequest;
    private handleTaskRequest;
    private handleMCPRequest;
    private handleHybridRequest;
    private executeCLICommand;
    private executeMCPCommand;
    private combineResults;
    private generateCLIFollowUp;
    private generateAgentFollowUp;
    private setupFileWatchers;
    private setupGitIntegration;
    private startPeriodicChecks;
    private handleFileChange;
    private checkCompliance;
    private checkFileForViolations;
}
export declare const createHybridTDDSystem: (config?: Partial<HybridTDDConfig>) => HybridTDDSystem;

// ---- src/integration/reporters/html-reporter.d.ts ----
/**
 * HTML Test Reporter
 * Phase 2.3: Generate comprehensive HTML reports for test execution results
 */
import { TestReporter, TestExecutionSummary } from '../types.js';
export declare class HTMLTestReporter implements TestReporter {
    readonly name = "HTML Reporter";
    readonly format = "html";
    /**
     * Generate HTML test report
     */
    generateReport(summary: TestExecutionSummary): Promise<string>;
    /**
     * Save report to file
     */
    saveReport(content: string, filePath: string): Promise<void>;
    /**
     * Generate CSS styles
     */
    private generateStyles;
    /**
     * Generate JavaScript
     */
    private generateScripts;
    /**
     * Generate report header
     */
    private generateHeader;
    /**
     * Generate summary cards
     */
    private generateSummaryCards;
    /**
     * Generate charts section
     */
    private generateChartsSection;
    /**
     * Generate simple pie chart representation
     */
    private generatePieChart;
    /**
     * Generate test results table
     */
    private generateTestResults;
    /**
     * Generate failures section
     */
    private generateFailures;
    /**
     * Generate artifacts section
     */
    private generateArtifacts;
    /**
     * Generate report footer
     */
    private generateFooter;
    /**
     * Get icon for artifact type
     */
    private getArtifactIcon;
    /**
     * Format duration in milliseconds
     */
    private formatDuration;
    /**
     * Format file size in bytes
     */
    private formatFileSize;
    /**
     * Escape HTML entities
     */
    private escapeHtml;
    /**
     * Copy static assets
     */
    private copyAssets;
}

// ---- src/integration/runners/api-runner.d.ts ----
/**
 * API Test Runner
 * Phase 2.3: HTTP API testing with contract validation and performance monitoring
 */
import { TestRunner, TestCase, TestSuite, TestEnvironment, TestResult, TestExecutionSummary, TestCategory } from '../types.js';
export type HttpMethod = 'GET' | 'POST' | 'PUT' | 'PATCH' | 'DELETE' | 'HEAD' | 'OPTIONS';
export interface APITestConfig {
    timeout: number;
    retries: number;
    validateSchema: boolean;
    followRedirects: boolean;
    validateSSL: boolean;
    maxResponseSize: number;
    defaultHeaders: Record<string, string>;
}
export interface HttpRequest {
    method: HttpMethod;
    url: string;
    headers?: Record<string, string>;
    body?: any;
    query?: Record<string, string>;
    auth?: {
        type: 'basic' | 'bearer' | 'apikey' | 'oauth2';
        credentials: Record<string, string>;
    };
    timeout?: number;
    validateStatus?: (status: number) => boolean;
}
export interface HttpResponse {
    status: number;
    statusText: string;
    headers: Record<string, string>;
    body: any;
    size: number;
    time: number;
    redirects: number;
}
export interface APIAssertion {
    type: 'status' | 'header' | 'body' | 'schema' | 'performance' | 'custom';
    field?: string;
    operator: 'equals' | 'contains' | 'matches' | 'gt' | 'lt' | 'gte' | 'lte' | 'exists' | 'not_exists';
    expected: any;
    message?: string;
}
export interface ResponseSchema {
    type: 'json' | 'xml' | 'text' | 'binary';
    schema?: any;
    properties?: Record<string, any>;
    required?: string[];
}
export declare class APITestRunner implements TestRunner {
    readonly id = "api-runner";
    readonly name = "API Test Runner";
    readonly category: TestCategory;
    private config;
    constructor(config: APITestConfig);
    /**
     * Check if runner can execute test
     */
    canRun(test: TestCase): boolean;
    /**
     * Setup API testing environment
     */
    setup(environment: TestEnvironment): Promise<void>;
    /**
     * Teardown API testing environment
     */
    teardown(environment: TestEnvironment): Promise<void>;
    /**
     * Execute single API test
     */
    runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult>;
    /**
     * Execute test suite (delegates to orchestrator)
     */
    runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary>;
    /**
     * Execute API test step
     */
    private executeAPIStep;
    /**
     * Execute HTTP request
     */
    private executeRequest;
    /**
     * Execute response validation
     */
    private executeValidation;
    /**
     * Execute data extraction
     */
    private executeExtraction;
    /**
     * Make HTTP request
     */
    private makeRequest;
    /**
     * Generate mock status code
     */
    private getMockStatus;
    /**
     * Generate mock response body
     */
    private getMockResponseBody;
    /**
     * Add authentication to headers
     */
    private addAuthentication;
    /**
     * Validate response against assertion
     */
    private validateAssertion;
    /**
     * Apply comparison operator
     */
    private applyOperator;
    /**
     * Validate response schema
     */
    private validateSchema;
    /**
     * Extract value from object using path
     */
    private extractFromObject;
    /**
     * Parse API action string
     */
    private parseAPIAction;
    /**
     * Check if action is API step
     */
    private isAPIStep;
    /**
     * Before test hook
     */
    beforeTest?(test: TestCase): Promise<void>;
    /**
     * After test hook
     */
    afterTest?(test: TestCase, result: TestResult): Promise<void>;
}

// ---- src/integration/runners/e2e-runner.d.ts ----
/**
 * End-to-End Test Runner
 * Phase 2.3: Browser-based E2E test execution with Playwright integration
 */
/**
 * Test step result interface
 */
export interface TestStepResult {
    stepIndex: number;
    action: string;
    status: 'success' | 'error';
    message: string;
    duration: number;
    screenshot?: string;
}
import { TestRunner, TestCase, TestSuite, TestEnvironment, TestResult, TestExecutionSummary, TestCategory } from '../types.js';
export type BrowserType = 'chromium' | 'firefox' | 'webkit';
export interface E2EConfig {
    browser: BrowserType;
    headless: boolean;
    viewport: {
        width: number;
        height: number;
    };
    timeout: number;
    retries: number;
    screenshots: boolean;
    video: boolean;
    trace: boolean;
    slowMo: number;
}
export interface BrowserPage {
    goto(url: string): Promise<void>;
    click(selector: string): Promise<void>;
    fill(selector: string, value: string): Promise<void>;
    selectOption(selector: string, value: string): Promise<void>;
    waitForSelector(selector: string, timeout?: number): Promise<void>;
    waitForTimeout(timeout: number): Promise<void>;
    screenshot(options?: {
        path?: string;
        fullPage?: boolean;
    }): Promise<Buffer>;
    textContent(selector: string): Promise<string | null>;
    getAttribute(selector: string, name: string): Promise<string | null>;
    isVisible(selector: string): Promise<boolean>;
    locator(selector: string): any;
    evaluate(fn: () => any): Promise<any>;
    reload(): Promise<void>;
    close(): Promise<void>;
}
export interface BrowserContext {
    newPage(): Promise<BrowserPage>;
    close(): Promise<void>;
}
export interface Browser {
    newContext(options?: any): Promise<BrowserContext>;
    close(): Promise<void>;
}
export declare class E2ETestRunner implements TestRunner {
    readonly id = "e2e-runner";
    readonly name = "End-to-End Test Runner";
    readonly category: TestCategory;
    private config;
    private browser;
    private context;
    private currentPage;
    constructor(config: E2EConfig);
    /**
     * Check if runner can execute test
     */
    canRun(test: TestCase): boolean;
    /**
     * Setup browser environment
     */
    setup(environment: TestEnvironment): Promise<void>;
    /**
     * Teardown browser environment
     */
    teardown(environment: TestEnvironment): Promise<void>;
    /**
     * Execute single test
     */
    runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult>;
    /**
     * Execute test suite (delegates to orchestrator)
     */
    runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary>;
    /**
     * Execute individual test step
     */
    private executeStep;
    /**
     * Execute verification step
     */
    private executeVerification;
    /**
     * Execute custom step
     */
    private executeCustomStep;
    /**
     * Parse step action string
     */
    private parseStepAction;
    /**
     * Check if action is E2E step
     */
    private isE2EStep;
    /**
     * Capture screenshot
     */
    private captureScreenshot;
    /**
     * Launch browser (placeholder implementation)
     */
    private launchBrowser;
    /**
     * Create mock page for testing
     */
    private createMockPage;
    /**
     * Before test hook
     */
    beforeTest?(test: TestCase): Promise<void>;
    /**
     * After test hook
     */
    afterTest?(test: TestCase, result: TestResult): Promise<void>;
}

// ---- src/integration/test-orchestrator.d.ts ----
/**
 * Integration Test Orchestrator
 * Phase 2.3: Central orchestrator for managing and executing integration tests
 */
import { EventEmitter } from 'events';
import { TestCase, TestSuite, TestFixture, TestEnvironment, TestExecutionConfig, TestExecutionSummary, TestResult, TestRunner, IntegrationTestConfig, TestDiscovery } from './types.js';
export declare class IntegrationTestOrchestrator extends EventEmitter {
    private config;
    private environments;
    private runners;
    private reporters;
    private testCases;
    private testSuites;
    private testFixtures;
    private activeExecutions;
    constructor(config: IntegrationTestConfig);
    /**
     * Initialize the orchestrator
     */
    initialize(): Promise<void>;
    /**
     * Discover tests from patterns
     */
    discoverTests(discovery: TestDiscovery, patterns: string[]): Promise<{
        tests: TestCase[];
        suites: TestSuite[];
        fixtures: TestFixture[];
    }>;
    /**
     * Execute a single test case
     */
    executeTest(testId: string, environmentName: string, config: TestExecutionConfig): Promise<TestResult>;
    /**
     * Execute a test suite
     */
    executeSuite(suiteId: string, environmentName: string, config: TestExecutionConfig): Promise<TestExecutionSummary>;
    /**
     * Internal suite execution logic
     */
    private executeSuiteInternal;
    /**
     * Execute tests in parallel
     */
    private executeTestsParallel;
    /**
     * Apply filters to test list
     */
    private applyFilters;
    /**
     * Find appropriate runner for test
     */
    private findRunner;
    /**
     * Setup test fixtures
     */
    private setupFixtures;
    /**
     * Teardown test fixtures
     */
    private teardownFixtures;
    /**
     * Execute setup scripts
     */
    private executeSetupScripts;
    /**
     * Execute teardown scripts
     */
    private executeTeardownScripts;
    /**
     * Execute a script
     */
    private executeScript;
    /**
     * Execute SQL script
     */
    private executeSQLScript;
    /**
     * Execute API script
     */
    private executeAPIScript;
    /**
     * Execute shell script
     */
    private executeShellScript;
    /**
     * Calculate test statistics
     */
    private calculateStatistics;
    /**
     * Collect test artifacts
     */
    private collectArtifacts;
    /**
     * Collect metadata
     */
    private collectMetadata;
    /**
     * Generate test reports
     */
    private generateReports;
    /**
     * Setup environments
     */
    private setupEnvironments;
    /**
     * Setup runners
     */
    private setupRunners;
    /**
     * Setup reporters
     */
    private setupReporters;
    /**
     * Get execution status
     */
    getExecutionStatus(suiteId: string): 'idle' | 'running' | 'unknown';
    /**
     * Cancel execution
     */
    cancelExecution(suiteId: string): Promise<boolean>;
    /**
     * Get available environments
     */
    getEnvironments(): TestEnvironment[];
    /**
     * Get available runners
     */
    getRunners(): TestRunner[];
    /**
     * Get test cases
     */
    getTestCases(): TestCase[];
    /**
     * Get test suites
     */
    getTestSuites(): TestSuite[];
    /**
     * Add test case
     */
    addTestCase(test: TestCase): void;
    /**
     * Add test suite
     */
    addTestSuite(suite: TestSuite): void;
    /**
     * Add test fixture
     */
    addTestFixture(fixture: TestFixture): void;
}

// ---- src/integration/types.d.ts ----
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

// ---- src/lib/brand.d.ts ----
import { z } from 'zod';
export type Brand<T, B extends string> = T & {
    readonly __brand: B;
};
export declare function branded<T, B extends string>(schema: z.ZodType<T>, brand: B, normalize?: (t: T) => T): {
    schema: z.ZodType<T, z.ZodTypeDef, T>;
    make(input: unknown): Brand<T, B>;
    is(u: unknown): u is Brand<T, B>;
};

// ---- src/lib/email.d.ts ----
import { z } from 'zod';
import { Brand } from './brand.js';
export type Email = Brand<string, 'Email'>;
export declare const Email: {
    schema: z.ZodType<string, z.ZodTypeDef, string>;
    make(input: unknown): Brand<string, "Email">;
    is(u: unknown): u is Brand<string, "Email">;
};
export declare function makeEmail(input: string): Email;

// ---- src/mcp-server/code-generation-server.d.ts ----
/**
 * MCP Server for Code Generation Agent
 * Provides tools for Phase 4: Code generation from tests
 */
export declare class CodeGenerationServer {
    private server;
    private agent;
    constructor();
    private setupErrorHandling;
    private registerTools;
    private validateCodeAgainstTests;
    start(): Promise<void>;
    stop(): Promise<void>;
}

// ---- src/mcp-server/container-server.d.ts ----
/**
 * Container MCP Server - Phase 3 of Issue #37
 * MCP server providing container-based verification tools
 */
import { ContainerAgentConfig } from '../agents/container-agent.js';
export declare class ContainerServer {
    private server;
    private agent;
    constructor(config?: ContainerAgentConfig);
    private setupTools;
    private setupErrorHandling;
    start(): Promise<void>;
}

// ---- src/mcp-server/formal-server.d.ts ----
#!/usr/bin/env node
/**
 * MCP Server for Formal Agent
 * Provides tools for formal specification generation, validation, and model checking
 */
declare class FormalMCPServer {
    private server;
    private formalAgent;
    constructor();
    private setupToolHandlers;
    private handleGenerateFormalSpec;
    private handleCreateAPISpec;
    private handleGenerateStateMachine;
    private handleCreateContracts;
    private handleValidateSpec;
    private handleModelCheck;
    private handleGenerateDiagrams;
    private handleListSpecifications;
    private handleGetSpecification;
    private handleUpdateConfig;
    private setupErrorHandling;
    run(): Promise<void>;
}
export declare function createFormalServer(): Promise<FormalMCPServer>;
export { FormalMCPServer };

// ---- src/mcp-server/intent-server.d.ts ----
#!/usr/bin/env node
/**
 * MCP Server for Intent Agent
 * Exposes Intent Agent capabilities as MCP tools for Phase 1 of ae-framework
 */
export {};

// ---- src/mcp-server/operate-server.d.ts ----
#!/usr/bin/env node
export {};

// ---- src/mcp-server/tdd-server.d.ts ----
#!/usr/bin/env node
export {};

// ---- src/mcp-server/test-generation-server.d.ts ----
#!/usr/bin/env node
export {};

// ---- src/mcp-server/verify-server.d.ts ----
/**
 * MCP Server for Verify Agent
 * Exposes verification tools for Phase 5 of ae-framework
 */
interface VerifyServerOptions {
    name: string;
    version: string;
}
export declare class VerifyMCPServer {
    private server;
    private verifyAgent;
    constructor(options: VerifyServerOptions);
    private setupHandlers;
    private handleFullVerification;
    private handleRunTests;
    private handleCheckCoverage;
    private handleRunLinting;
    private handleRunTypeChecking;
    private handleRunSecurityScan;
    private handleRunPerformanceTests;
    private handleCheckAccessibility;
    private handleVerifyContracts;
    private handleVerifySpecifications;
    private handleRunMutationTests;
    private handleGenerateTraceabilityMatrix;
    private handleGetQualityMetrics;
    private buildVerificationRequest;
    private loadCodeFiles;
    private loadTestFiles;
    private loadSpecifications;
    private findFiles;
    private formatTraceabilityAsHTML;
    private formatTraceabilityAsCSV;
    run(): Promise<void>;
}
export {};

// ---- src/optimization/index.d.ts ----
/**
 * Phase 3.3: Complete Optimization System Integration
 * Combines monitoring, parallel processing, and resource management
 */
import { EventEmitter } from 'events';
import { MonitoringSystem, type MonitoringSystemConfig, type MonitoringDashboard } from './monitoring/index.js';
import { ParallelOptimizationSystem, type OptimizationMetrics } from './parallel/index.js';
export interface OptimizationSystemConfig {
    monitoring?: MonitoringSystemConfig;
    parallelOptimization?: {
        optimizer?: any;
        scheduler?: any;
        resourcePool?: any;
    };
    integration?: {
        autoStart?: boolean;
        crossSystemMetrics?: boolean;
        adaptiveOptimization?: boolean;
        performanceBasedScaling?: boolean;
    };
}
export interface SystemMetrics {
    timestamp: Date;
    monitoring: {
        healthStatus: string;
        activeAlerts: number;
        metricsCount: number;
        uptime: number;
    };
    optimization: OptimizationMetrics;
    integration: {
        crossSystemEfficiency: number;
        adaptiveOptimizations: number;
        resourceUtilization: number;
        systemStability: number;
    };
    performance: {
        overallThroughput: number;
        systemLatency: number;
        errorRate: number;
        scalabilityIndex: number;
    };
}
export interface OptimizationDashboard {
    timestamp: Date;
    systemStatus: 'optimal' | 'good' | 'degraded' | 'critical';
    monitoringDashboard: MonitoringDashboard;
    optimizationMetrics: OptimizationMetrics;
    systemMetrics: SystemMetrics;
    recommendations: SystemRecommendation[];
    alerts: SystemAlert[];
}
export interface SystemRecommendation {
    id: string;
    type: 'performance' | 'resource' | 'scaling' | 'configuration';
    priority: 'high' | 'medium' | 'low';
    title: string;
    description: string;
    impact: string;
    action: string;
    estimatedBenefit: number;
}
export interface SystemAlert {
    id: string;
    level: 'info' | 'warning' | 'error' | 'critical';
    source: 'monitoring' | 'optimization' | 'integration';
    message: string;
    timestamp: Date;
    data?: any;
}
export declare class OptimizationSystem extends EventEmitter {
    private monitoringSystem;
    private parallelOptimization;
    private config;
    private isRunning;
    private startTime;
    private integrationTimer?;
    private adaptiveTimer?;
    private systemAlerts;
    private recommendations;
    constructor(config?: OptimizationSystemConfig);
    /**
     * Start the complete optimization system
     */
    start(): Promise<void>;
    /**
     * Stop the complete optimization system
     */
    stop(): Promise<void>;
    /**
     * Get comprehensive system metrics
     */
    getSystemMetrics(): SystemMetrics;
    /**
     * Get comprehensive system dashboard
     */
    getDashboard(): OptimizationDashboard;
    /**
     * Get monitoring system
     */
    getMonitoringSystem(): MonitoringSystem;
    /**
     * Get parallel optimization system
     */
    getParallelOptimizationSystem(): ParallelOptimizationSystem;
    /**
     * Track operation across both systems
     */
    trackOperation(operationName: string, startTime: number): void;
    /**
     * Track error across both systems
     */
    trackError(errorType: string): void;
    /**
     * Apply system optimization recommendations
     */
    applyOptimizationRecommendations(): Promise<void>;
    /**
     * Export comprehensive system report
     */
    exportSystemReport(): string;
    private setupIntegration;
    private startIntegrationServices;
    private stopIntegrationServices;
    private handleMonitoringAlert;
    private performAdaptiveOptimization;
    private optimizeForCpuPressure;
    private optimizeForMemoryPressure;
    private generateSystemRecommendations;
    private applyRecommendation;
    private addSystemAlert;
    private updateIntegrationMetrics;
    private cleanupOldAlerts;
    private calculateCrossSystemEfficiency;
    private calculateOverallResourceUtilization;
    private calculateSystemStability;
    private calculateScalabilityIndex;
    private mergeDefaultConfig;
}
export type { MonitoringSystemConfig, SystemHealthStatus, PerformanceMetrics as MonitoringPerformanceMetrics, PerformanceAlert, MetricPoint, MetricsSnapshot, AlertInstance, AlertSummary } from './monitoring/index.js';
export { MonitoringSystem, PerformanceMonitor, MetricsCollector, AlertManager } from './monitoring/index.js';
export type { ParallelTask, TaskResult, ResourceRequirements, ResourceUsage, OptimizationStrategy, ParallelizationPlan, OptimizationMetrics, ScheduledTask, SchedulingPolicy, TaskQueue, SchedulingMetrics, PooledResource, ResourceType, ResourceCapacity, PerformanceMetrics as ParallelPerformanceMetrics, MonitoringConfig as ParallelMonitoringConfig } from './parallel/index.js';
export { ParallelOptimizer, TaskScheduler, ResourcePool, ParallelOptimizationSystem } from './parallel/index.js';
export declare function createOptimizationSystem(config?: OptimizationSystemConfig): OptimizationSystem;
export declare function startDefaultOptimizationSystem(): Promise<OptimizationSystem>;

// ---- src/optimization/monitoring/alert-manager.d.ts ----
/**
 * Alert Manager for Phase 3.3 Optimization
 * Manages alerts, notifications, and escalation workflows
 */
import { EventEmitter } from 'events';
import type { PerformanceAlert } from './performance-monitor.js';
import type { MetricPoint } from './metrics-collector.js';
export interface AlertRule {
    id: string;
    name: string;
    description: string;
    metric: string;
    condition: AlertCondition;
    severity: 'info' | 'warning' | 'critical';
    enabled: boolean;
    silenced: boolean;
    silenceUntil?: Date;
    evaluationInterval: number;
    notifications: NotificationConfig[];
    escalation?: EscalationConfig;
    tags: Record<string, string>;
}
export interface AlertCondition {
    operator: 'gt' | 'gte' | 'lt' | 'lte' | 'eq' | 'ne';
    threshold: number;
    duration?: number;
    aggregation?: 'avg' | 'min' | 'max' | 'sum' | 'count';
    timeWindow?: number;
}
export interface NotificationConfig {
    type: 'email' | 'slack' | 'webhook' | 'console' | 'file';
    target: string;
    template?: string;
    enabled: boolean;
    throttle?: number;
}
export interface EscalationConfig {
    levels: EscalationLevel[];
    autoResolve: boolean;
    maxEscalationTime: number;
}
export interface EscalationLevel {
    level: number;
    delay: number;
    notifications: NotificationConfig[];
    autoAction?: AutoAction;
}
export interface AutoAction {
    type: 'restart' | 'scale' | 'cleanup' | 'custom';
    command?: string;
    parameters?: Record<string, any>;
}
export interface AlertInstance {
    id: string;
    ruleId: string;
    ruleName: string;
    status: 'firing' | 'resolved' | 'silenced';
    severity: AlertRule['severity'];
    message: string;
    metric: string;
    currentValue: number;
    threshold: number;
    startTime: Date;
    endTime?: Date;
    duration: number;
    escalationLevel: number;
    notificationsSent: number;
    labels: Record<string, string>;
    annotations: Record<string, string>;
}
export interface AlertHistory {
    instanceId: string;
    action: 'fired' | 'resolved' | 'escalated' | 'silenced' | 'notification_sent';
    timestamp: Date;
    details: Record<string, any>;
}
export interface AlertSummary {
    total: number;
    firing: number;
    resolved: number;
    silenced: number;
    bySeverity: {
        info: number;
        warning: number;
        critical: number;
    };
    byMetric: Record<string, number>;
    recentActivity: AlertHistory[];
}
export declare class AlertManager extends EventEmitter {
    private rules;
    private activeAlerts;
    private alertHistory;
    private evaluationTimer?;
    private metricBuffer;
    private notificationThrottles;
    private isRunning;
    private readonly maxHistorySize;
    private readonly maxMetricBufferSize;
    private readonly defaultEvaluationInterval;
    constructor();
    /**
     * Start alert manager
     */
    start(): void;
    /**
     * Stop alert manager
     */
    stop(): void;
    /**
     * Add alert rule
     */
    addRule(rule: AlertRule): void;
    /**
     * Update alert rule
     */
    updateRule(ruleId: string, updates: Partial<AlertRule>): void;
    /**
     * Remove alert rule
     */
    removeRule(ruleId: string): void;
    /**
     * Process metric point for alert evaluation
     */
    processMetric(metric: MetricPoint): void;
    /**
     * Process performance alert from monitor
     */
    processPerformanceAlert(perfAlert: PerformanceAlert): void;
    /**
     * Silence alert
     */
    silenceAlert(alertId: string, duration: number): void;
    /**
     * Unsilence alert
     */
    unsilenceAlert(alertId: string): void;
    /**
     * Get alert summary
     */
    getAlertSummary(): AlertSummary;
    /**
     * Get active alerts
     */
    getActiveAlerts(): AlertInstance[];
    /**
     * Get alert history
     */
    getAlertHistory(limit?: number): AlertHistory[];
    /**
     * Clear resolved alerts
     */
    clearResolvedAlerts(): void;
    private setupDefaultRules;
    private startEvaluation;
    private evaluateAllRules;
    private evaluateRulesForMetric;
    private evaluateRule;
    private evaluateCondition;
    private isConditionDurationMet;
    private createAlert;
    private fireAlert;
    private resolveAlert;
    private findAlertByRule;
    private updateAlertDurations;
    private checkEscalations;
    private escalateAlert;
    private sendNotifications;
    private sendNotification;
    private sendConsoleNotification;
    private sendFileNotification;
    private executeAutoAction;
    private addHistory;
    private calculateAggregation;
}

// ---- src/optimization/monitoring/demo.d.ts ----
#!/usr/bin/env tsx
/**
 * Phase 3.3 Monitoring System Demo
 * Demonstrates the performance monitoring, metrics collection, and alerting capabilities
 */
declare function runMonitoringDemo(): Promise<void>;
export { runMonitoringDemo };

// ---- src/optimization/monitoring/index.d.ts ----
/**
 * Phase 3.3 Monitoring System Integration
 * Combines performance monitoring, metrics collection, and alert management
 */
import { EventEmitter } from 'events';
import { type PerformanceMetrics } from './performance-monitor.js';
import { type MetricsSnapshot } from './metrics-collector.js';
import { type AlertInstance, type AlertSummary } from './alert-manager.js';
export interface MonitoringSystemConfig {
    performanceMonitor?: {
        interval?: number;
        thresholds?: {
            cpu: {
                warning: number;
                critical: number;
            };
            memory: {
                warning: number;
                critical: number;
            };
            responseTime: {
                warning: number;
                critical: number;
            };
            errorRate: {
                warning: number;
                critical: number;
            };
        };
    };
    metricsCollector?: {
        aggregationInterval?: number;
        retention?: number;
    };
    alertManager?: {
        enabled?: boolean;
        defaultNotifications?: boolean;
    };
    integration?: {
        autoStart?: boolean;
        exportMetrics?: boolean;
        exportInterval?: number;
    };
}
export interface SystemHealthStatus {
    overall: 'healthy' | 'degraded' | 'critical';
    components: {
        performanceMonitor: 'running' | 'stopped' | 'error';
        metricsCollector: 'running' | 'stopped' | 'error';
        alertManager: 'running' | 'stopped' | 'error';
    };
    metrics: {
        uptime: number;
        lastUpdate: Date;
        metricsCount: number;
        activeAlerts: number;
    };
    issues: string[];
}
export interface MonitoringDashboard {
    timestamp: Date;
    healthStatus: SystemHealthStatus;
    currentMetrics: PerformanceMetrics | null;
    activeAlerts: AlertInstance[];
    alertSummary: AlertSummary;
    metricsSnapshot: MetricsSnapshot;
    systemStats: {
        totalOperations: number;
        avgResponseTime: number;
        errorRate: number;
        uptime: number;
    };
}
export declare class MonitoringSystem extends EventEmitter {
    private performanceMonitor;
    private metricsCollector;
    private alertManager;
    private config;
    private startTime;
    private isRunning;
    private healthCheckTimer?;
    private exportTimer?;
    constructor(config?: MonitoringSystemConfig);
    /**
     * Start the complete monitoring system
     */
    start(): Promise<void>;
    /**
     * Stop the monitoring system
     */
    stop(): Promise<void>;
    /**
     * Get current system health status
     */
    getHealthStatus(): SystemHealthStatus;
    /**
     * Get monitoring dashboard data
     */
    getDashboard(): MonitoringDashboard;
    /**
     * Track custom operation for monitoring
     */
    trackOperation(operationName: string, startTime: number): void;
    /**
     * Track error for monitoring
     */
    trackError(errorType: string): void;
    /**
     * Record custom metric
     */
    recordMetric(name: string, value: number, tags?: Record<string, string>): void;
    /**
     * Export current metrics
     */
    exportMetrics(format?: 'json' | 'prometheus' | 'csv'): string;
    /**
     * Get performance metrics history
     */
    getPerformanceHistory(limit?: number): PerformanceMetrics[];
    /**
     * Get alert history
     */
    getAlertHistory(limit?: number): import("./alert-manager.js").AlertHistory[];
    /**
     * Get active alerts
     */
    getActiveAlerts(): AlertInstance[];
    /**
     * Get alert summary
     */
    getAlertSummary(): AlertSummary;
    /**
     * Force metrics collection (for testing)
     */
    forceMetricsCollection(): void;
    /**
     * Silence all alerts for a duration
     */
    silenceAllAlerts(duration: number): void;
    /**
     * Clear old data
     */
    cleanup(): void;
    private setupIntegration;
    private startHealthChecks;
    private startMetricsExport;
    private mergeDefaultConfig;
}
export * from './performance-monitor.js';
export * from './metrics-collector.js';
export * from './alert-manager.js';
export declare function createMonitoringSystem(config?: MonitoringSystemConfig): MonitoringSystem;
export declare function startDefaultMonitoring(): Promise<MonitoringSystem>;

// ---- src/optimization/monitoring/metrics-collector.d.ts ----
/**
 * Metrics Collector for Phase 3.3 Optimization
 * Collects, aggregates, and exports performance metrics
 */
import { EventEmitter } from 'events';
import type { PerformanceMetrics } from './performance-monitor.js';
export interface MetricPoint {
    name: string;
    value: number;
    timestamp: Date;
    tags: Record<string, string>;
    unit: string;
    type: 'counter' | 'gauge' | 'histogram' | 'timer';
}
export interface MetricSeries {
    name: string;
    points: MetricPoint[];
    metadata: {
        description: string;
        unit: string;
        type: string;
        retention: number;
    };
}
export interface AggregationConfig {
    interval: number;
    functions: AggregationFunction[];
    retention: number;
}
export type AggregationFunction = 'sum' | 'avg' | 'min' | 'max' | 'count' | 'p50' | 'p95' | 'p99';
export interface AggregatedMetric {
    name: string;
    function: AggregationFunction;
    value: number;
    timestamp: Date;
    windowStart: Date;
    windowEnd: Date;
    count: number;
}
export interface MetricsExportConfig {
    format: 'prometheus' | 'json' | 'csv' | 'influxdb';
    endpoint?: string;
    interval?: number;
    includeLabels: boolean;
    filters?: MetricFilter[];
}
export interface MetricFilter {
    name?: string;
    tags?: Record<string, string>;
    timeRange?: {
        start: Date;
        end: Date;
    };
}
export interface MetricsSnapshot {
    timestamp: Date;
    metrics: MetricPoint[];
    aggregations: AggregatedMetric[];
    summary: {
        totalMetrics: number;
        uniqueNames: number;
        timeRange: {
            start: Date;
            end: Date;
        };
    };
}
export declare class MetricsCollector extends EventEmitter {
    private metrics;
    private aggregations;
    private config;
    private aggregationTimer?;
    private exportConfigs;
    private isCollecting;
    constructor(config?: Partial<AggregationConfig>);
    /**
     * Start metrics collection
     */
    start(): void;
    /**
     * Stop metrics collection
     */
    stop(): void;
    /**
     * Record a single metric point
     */
    recordMetric(name: string, value: number, tags?: Record<string, string>, unit?: string, type?: MetricPoint['type']): void;
    /**
     * Record multiple metrics from performance data
     */
    recordPerformanceMetrics(perfMetrics: PerformanceMetrics): void;
    /**
     * Increment a counter metric
     */
    incrementCounter(name: string, value?: number, tags?: Record<string, string>): void;
    /**
     * Set a gauge metric
     */
    setGauge(name: string, value: number, tags?: Record<string, string>): void;
    /**
     * Record a timer metric
     */
    recordTimer(name: string, duration: number, tags?: Record<string, string>): void;
    /**
     * Record a histogram metric
     */
    recordHistogram(name: string, value: number, tags?: Record<string, string>): void;
    /**
     * Get metrics series by name
     */
    getMetricSeries(name: string): MetricSeries | undefined;
    /**
     * Get all metric series
     */
    getAllMetrics(): Map<string, MetricSeries>;
    /**
     * Get aggregated metrics for a time range
     */
    getAggregatedMetrics(name: string, startTime: Date, endTime: Date): AggregatedMetric[];
    /**
     * Query metrics with filters
     */
    queryMetrics(filter: MetricFilter): MetricPoint[];
    /**
     * Create a metrics snapshot
     */
    createSnapshot(): MetricsSnapshot;
    /**
     * Export metrics in specified format
     */
    exportMetrics(config: MetricsExportConfig): string;
    /**
     * Add export configuration
     */
    addExportConfig(config: MetricsExportConfig): void;
    /**
     * Clear all metrics
     */
    clearMetrics(): void;
    private recordMetricWithTimestamp;
    private addMetricPoint;
    private startAggregation;
    private performAggregation;
    private calculateAggregation;
    private exportPrometheus;
    private exportJSON;
    private exportCSV;
    private exportInfluxDB;
    private formatLabels;
    private formatInfluxTags;
}

// ---- src/optimization/monitoring/performance-monitor.d.ts ----
/**
 * Performance Monitor for Phase 3.3 Optimization
 * Provides real-time performance monitoring and analysis
 */
import { EventEmitter } from 'events';
export interface PerformanceMetrics {
    timestamp: Date;
    cpuUsage: CPUMetrics;
    memoryUsage: MemoryMetrics;
    responseTime: ResponseTimeMetrics;
    throughput: ThroughputMetrics;
    errorRate: ErrorRateMetrics;
    customMetrics: Record<string, number>;
}
export interface CPUMetrics {
    userCPU: number;
    systemCPU: number;
    totalUsage: number;
    loadAverage: number[];
}
export interface MemoryMetrics {
    heapUsed: number;
    heapTotal: number;
    external: number;
    rss: number;
    buffers: number;
    cached: number;
    available: number;
    usagePercentage: number;
}
export interface ResponseTimeMetrics {
    average: number;
    median: number;
    p95: number;
    p99: number;
    min: number;
    max: number;
    samples: number[];
}
export interface ThroughputMetrics {
    requestsPerSecond: number;
    operationsPerSecond: number;
    tasksCompleted: number;
    concurrentTasks: number;
}
export interface ErrorRateMetrics {
    totalErrors: number;
    errorRate: number;
    errorsByType: Record<string, number>;
    criticalErrors: number;
}
export interface PerformanceAlert {
    id: string;
    type: 'warning' | 'critical' | 'info';
    category: 'cpu' | 'memory' | 'response_time' | 'error_rate' | 'custom';
    message: string;
    threshold: number;
    currentValue: number;
    timestamp: Date;
    recommendations: string[];
}
export interface MonitoringConfig {
    interval: number;
    thresholds: {
        cpu: {
            warning: number;
            critical: number;
        };
        memory: {
            warning: number;
            critical: number;
        };
        responseTime: {
            warning: number;
            critical: number;
        };
        errorRate: {
            warning: number;
            critical: number;
        };
    };
    enabledMetrics: {
        cpu: boolean;
        memory: boolean;
        responseTime: boolean;
        throughput: boolean;
        errorRate: boolean;
        custom: boolean;
    };
    retentionPeriod: number;
    alertCooldown: number;
}
export interface PerformanceBaseline {
    cpu: {
        normal: number;
        peak: number;
    };
    memory: {
        normal: number;
        peak: number;
    };
    responseTime: {
        normal: number;
        acceptable: number;
    };
    throughput: {
        minimum: number;
        optimal: number;
    };
    errorRate: {
        acceptable: number;
        critical: number;
    };
}
export declare class PerformanceMonitor extends EventEmitter {
    private config;
    private isMonitoring;
    private metrics;
    private alerts;
    private baseline;
    private monitoringTimer?;
    private performanceObserver?;
    private responseTimes;
    private operationCounts;
    private errorCounts;
    private lastAlerts;
    constructor(config?: Partial<MonitoringConfig>);
    /**
     * Start performance monitoring
     */
    start(): void;
    /**
     * Stop performance monitoring
     */
    stop(): void;
    /**
     * Collect current performance metrics
     */
    private collectMetrics;
    /**
     * Get CPU usage metrics
     */
    private getCPUMetrics;
    /**
     * Get memory usage metrics
     */
    private getMemoryMetrics;
    /**
     * Get response time metrics
     */
    private getResponseTimeMetrics;
    /**
     * Get throughput metrics
     */
    private getThroughputMetrics;
    /**
     * Get error rate metrics
     */
    private getErrorRateMetrics;
    /**
     * Get custom metrics
     */
    private getCustomMetrics;
    /**
     * Check thresholds and generate alerts
     */
    private checkThresholds;
    /**
     * Check CPU thresholds
     */
    private checkCPUThresholds;
    /**
     * Check memory thresholds
     */
    private checkMemoryThresholds;
    /**
     * Check response time thresholds
     */
    private checkResponseTimeThresholds;
    /**
     * Check error rate thresholds
     */
    private checkErrorRateThresholds;
    /**
     * Create a performance alert
     */
    private createAlert;
    /**
     * Process and emit alert
     */
    private processAlert;
    /**
     * Track operation for performance monitoring
     */
    trackOperation(operationName: string, startTime: number): void;
    /**
     * Track error for monitoring
     */
    trackError(errorType: string): void;
    /**
     * Set performance baseline
     */
    setBaseline(baseline: PerformanceBaseline): void;
    /**
     * Get current metrics
     */
    getCurrentMetrics(): PerformanceMetrics | null;
    /**
     * Get metrics history
     */
    getMetricsHistory(limit?: number): PerformanceMetrics[];
    /**
     * Get recent alerts
     */
    getRecentAlerts(limit?: number): PerformanceAlert[];
    /**
     * Clear metrics and alerts
     */
    clearHistory(): void;
    private createDefaultConfig;
    private setupPerformanceObserver;
    private cleanupOldMetrics;
    private getLoadAverage;
    private getTotalSystemMemory;
    private getCurrentConcurrentTasks;
    private getActiveConnections;
    private getQueueSize;
    private getCacheHitRate;
}

// ---- src/optimization/parallel/demo.d.ts ----
/**
 * Phase 3.3.2: Parallel Processing Optimization Engine Demo
 * Interactive demonstration of parallel optimization capabilities
 */
declare class ParallelOptimizationDemo {
    private system;
    private demoTasks;
    private isRunning;
    constructor();
    /**
     * Start the demo
     */
    start(): Promise<void>;
    /**
     * Stop the demo
     */
    stop(): Promise<void>;
    /**
     * Run demonstration scenarios
     */
    private runDemoScenarios;
    /**
     * Scenario 1: Basic Parallel Processing
     */
    private scenario1_BasicParallelProcessing;
    /**
     * Scenario 2: Priority-based Scheduling
     */
    private scenario2_PriorityScheduling;
    /**
     * Scenario 3: Resource-aware Optimization
     */
    private scenario3_ResourceOptimization;
    /**
     * Scenario 4: Dependency Management
     */
    private scenario4_DependencyManagement;
    /**
     * Scenario 5: Load Balancing and Auto-scaling
     */
    private scenario5_LoadBalancing;
    /**
     * Display final comprehensive metrics
     */
    private displayFinalMetrics;
    /**
     * Setup demo tasks
     */
    private setupDemoTasks;
    /**
     * Setup event listeners for demo
     */
    private setupEventListeners;
    /**
     * Create a demo task
     */
    private createTask;
    /**
     * Wait for completion with progress indicator
     */
    private waitForCompletion;
}
export { ParallelOptimizationDemo };

// ---- src/optimization/parallel/index.d.ts ----
/**
 * Phase 3.3.2: Parallel Processing Optimization Engine
 * Export all parallel optimization components
 */
import { ParallelOptimizer } from './parallel-optimizer.js';
import { TaskScheduler } from './task-scheduler.js';
import { ResourcePool } from './resource-pool.js';
export { ParallelOptimizer } from './parallel-optimizer.js';
export { TaskScheduler } from './task-scheduler.js';
export { ResourcePool } from './resource-pool.js';
export type { ParallelTask, TaskResult, ResourceRequirements, TaskPriority, TaskType, ResourceUsage, OptimizationStrategy, LoadBalancingStrategy, PriorityWeights, ResourceAllocationStrategy, AdaptiveScalingConfig, ParallelizationPlan, OptimizedTask, TaskGroup, ResourceUtilizationPlan, OptimizationMetrics } from './parallel-optimizer.js';
export type { ScheduledTask, SchedulingPolicy, SchedulingAlgorithm, PreemptionPolicy, PriorityBoostConfig, DeadlineHandling, FairnessConfig, SchedulingOptimization, SchedulingMetrics, TaskQueue, SchedulingDecision, ResourceAvailability } from './task-scheduler.js';
export type { PooledResource, ResourceType, ResourceCapacity, ResourceStatus, ResourceMetadata, ResourceConstraints, PerformanceMetrics, HealthCheckConfig, AllocationRecord, ResourceAllocation, PoolConfiguration, PoolStrategy, PoolSizing, AllocationPolicy, AllocationAlgorithm, PriorityHandling, FairnessPolicy, OverflowHandling, MonitoringConfig, AlertingConfig, OptimizationConfig, DefragmentationConfig, LoadBalancingConfig, CachingConfig, PredictionConfig, PoolMetrics } from './resource-pool.js';
/**
 * Create a complete parallel optimization system
 */
export declare class ParallelOptimizationSystem {
    private optimizer;
    private scheduler;
    private resourcePool;
    constructor(optimizerConfig?: any, schedulerConfig?: any, poolConfig?: any);
    /**
     * Start the complete system
     */
    start(): void;
    /**
     * Stop the complete system
     */
    stop(): Promise<void>;
    /**
     * Get the parallel optimizer
     */
    getOptimizer(): ParallelOptimizer;
    /**
     * Get the task scheduler
     */
    getScheduler(): TaskScheduler;
    /**
     * Get the resource pool
     */
    getResourcePool(): ResourcePool;
    /**
     * Get combined system metrics
     */
    getSystemMetrics(): {
        optimization: import("./parallel-optimizer.js").OptimizationMetrics;
        scheduling: import("./task-scheduler.js").SchedulingMetrics;
        resources: import("./resource-pool.js").PoolMetrics;
        timestamp: Date;
    };
    private setupIntegration;
    private getPriorityValue;
}

// ---- src/optimization/parallel/parallel-optimizer.d.ts ----
/**
 * Parallel Optimizer for Phase 3.3.2
 * Intelligent parallel processing optimization and task distribution
 */
import { EventEmitter } from 'events';
export interface ParallelTask<T = any, R = any> {
    id: string;
    name: string;
    type: TaskType;
    payload: T;
    priority: TaskPriority;
    dependencies: string[];
    estimatedDuration: number;
    maxRetries: number;
    timeout: number;
    resourceRequirements: ResourceRequirements;
    metadata: Record<string, any>;
}
export type TaskType = 'cpu_intensive' | 'io_bound' | 'memory_intensive' | 'network_request' | 'computation' | 'analysis' | 'test_execution' | 'code_generation';
export type TaskPriority = 'urgent' | 'high' | 'normal' | 'low' | 'background';
export interface ResourceRequirements {
    cpu: number;
    memory: number;
    io: number;
    network: number;
}
export interface TaskResult<R = any> {
    taskId: string;
    status: 'completed' | 'failed' | 'timeout' | 'cancelled';
    result?: R;
    error?: string;
    executionTime: number;
    resourceUsage: ResourceUsage;
    workerId?: string;
    retryCount: number;
}
export interface ResourceUsage {
    cpuTime: number;
    memoryPeak: number;
    ioOperations: number;
    networkBytes: number;
}
export interface OptimizationStrategy {
    name: string;
    description: string;
    maxConcurrency: number;
    loadBalancing: LoadBalancingStrategy;
    priorityWeighting: PriorityWeights;
    resourceAllocation: ResourceAllocationStrategy;
    adaptiveScaling: AdaptiveScalingConfig;
}
export type LoadBalancingStrategy = 'round_robin' | 'least_loaded' | 'resource_aware' | 'task_affinity' | 'smart_dispatch';
export interface PriorityWeights {
    urgent: number;
    high: number;
    normal: number;
    low: number;
    background: number;
}
export type ResourceAllocationStrategy = 'static' | 'dynamic' | 'predictive' | 'fair_share' | 'greedy';
export interface AdaptiveScalingConfig {
    enabled: boolean;
    scaleUpThreshold: number;
    scaleDownThreshold: number;
    maxWorkers: number;
    minWorkers: number;
    cooldownPeriod: number;
}
export interface ParallelizationPlan {
    id: string;
    originalTasks: ParallelTask[];
    optimizedTasks: OptimizedTask[];
    executionGroups: TaskGroup[];
    estimatedParallelTime: number;
    estimatedSequentialTime: number;
    speedupFactor: number;
    efficiency: number;
    resourceUtilization: ResourceUtilizationPlan;
}
export interface OptimizedTask extends ParallelTask {
    groupId: string;
    executionOrder: number;
    assignedResources: ResourceRequirements;
    scheduledStartTime: number;
    dependencies: string[];
}
export interface TaskGroup {
    id: string;
    tasks: string[];
    parallelExecutable: boolean;
    estimatedDuration: number;
    resourceRequirements: ResourceRequirements;
    dependencies: string[];
}
export interface ResourceUtilizationPlan {
    cpuUtilization: number;
    memoryUtilization: number;
    ioUtilization: number;
    networkUtilization: number;
    efficiency: number;
    bottlenecks: string[];
}
export interface OptimizationMetrics {
    totalTasksProcessed: number;
    averageExecutionTime: number;
    parallelEfficiency: number;
    resourceUtilization: number;
    successRate: number;
    throughput: number;
    queueLength: number;
    activeWorkers: number;
}
export declare class ParallelOptimizer extends EventEmitter {
    private strategy;
    private activeWorkers;
    private taskQueue;
    private executingTasks;
    private completedTasks;
    private resourceUsage;
    private metrics;
    private isRunning;
    private optimizationTimer?;
    constructor(strategy?: Partial<OptimizationStrategy>);
    /**
     * Start the parallel optimizer
     */
    start(): void;
    /**
     * Stop the parallel optimizer
     */
    stop(): Promise<void>;
    /**
     * Submit a task for parallel execution
     */
    submitTask<T, R>(task: ParallelTask<T, R>): Promise<string>;
    /**
     * Get task result
     */
    getTaskResult<R>(taskId: string): TaskResult<R> | null;
    /**
     * Wait for task completion
     */
    waitForTask<R>(taskId: string, timeout?: number): Promise<TaskResult<R>>;
    /**
     * Generate parallelization plan for a set of tasks
     */
    generateParallelizationPlan(tasks: ParallelTask[]): Promise<ParallelizationPlan>;
    /**
     * Execute tasks based on parallelization plan
     */
    executeParallelizationPlan<R>(plan: ParallelizationPlan): Promise<TaskResult<R>[]>;
    /**
     * Get current optimization metrics
     */
    getOptimizationMetrics(): OptimizationMetrics;
    /**
     * Update optimization strategy
     */
    updateStrategy(updates: Partial<OptimizationStrategy>): void;
    /**
     * Get current resource usage
     */
    getCurrentResourceUsage(): ResourceUsage;
    /**
     * Cancel a task
     */
    cancelTask(taskId: string): Promise<boolean>;
    private createDefaultStrategy;
    private setupWorkerPool;
    private createWorker;
    private terminateAllWorkers;
    private startOptimizationLoop;
    private processTaskQueue;
    private selectTasksForProcessing;
    private areTaskDependenciesSatisfied;
    private executeTask;
    private handleWorkerMessage;
    private handleTaskCompleted;
    private handleTaskError;
    private updateResourceUsage;
    private sortTasksByPriority;
    private getAvailableWorkers;
    private updateMetrics;
    private calculateParallelEfficiency;
    private calculateResourceUtilization;
    private calculateThroughput;
    private adaptiveScaling;
    private applyNewStrategy;
    private buildDependencyGraph;
    private groupTasksForParallelExecution;
    private topologicalSort;
    private canAddToGroup;
    private updateGroupResourceRequirements;
    private optimizeTaskScheduling;
    private allocateResources;
    private dynamicResourceAllocation;
    private fairShareAllocation;
    private calculateParallelExecutionTime;
    private planResourceUtilization;
    private executeTaskGroupParallel;
    private executeTaskGroupSequential;
}

// ---- src/optimization/parallel/resource-pool.d.ts ----
/**
 * Resource Pool Management for Phase 3.3.2
 * Advanced resource allocation and pooling for parallel optimization
 */
import { EventEmitter } from 'events';
import type { ResourceRequirements } from './parallel-optimizer.js';
export interface PooledResource {
    id: string;
    type: ResourceType;
    capacity: ResourceCapacity;
    allocated: ResourceCapacity;
    available: ResourceCapacity;
    status: ResourceStatus;
    metadata: ResourceMetadata;
    lastUsed: Date;
    allocationHistory: AllocationRecord[];
}
export type ResourceType = 'cpu_core' | 'memory_block' | 'io_channel' | 'network_bandwidth' | 'worker_thread' | 'compute_unit';
export interface ResourceCapacity {
    value: number;
    unit: string;
    scalable: boolean;
    maxScale: number;
}
export type ResourceStatus = 'available' | 'allocated' | 'reserved' | 'maintenance' | 'failed' | 'scaling';
export interface ResourceMetadata {
    priority: number;
    affinityTags: string[];
    constraints: ResourceConstraints;
    performance: PerformanceMetrics;
    healthCheck: HealthCheckConfig;
}
export interface ResourceConstraints {
    minAllocation: number;
    maxAllocation: number;
    allocationGranularity: number;
    exclusiveAccess: boolean;
    coLocationRules: string[];
}
export interface PerformanceMetrics {
    throughput: number;
    latency: number;
    reliability: number;
    efficiency: number;
    lastBenchmark: Date;
}
export interface HealthCheckConfig {
    enabled: boolean;
    interval: number;
    timeout: number;
    retryCount: number;
    healthThreshold: number;
}
export interface AllocationRecord {
    taskId: string;
    allocatedAt: Date;
    releasedAt?: Date;
    duration?: number;
    allocation: ResourceCapacity;
    utilization: number;
}
export interface ResourceAllocation {
    id: string;
    taskId: string;
    resources: PooledResource[];
    allocation: ResourceRequirements;
    grantedAt: Date;
    expiresAt?: Date;
    priority: number;
    preemptable: boolean;
}
export interface PoolConfiguration {
    name: string;
    strategy: PoolStrategy;
    sizing: PoolSizing;
    allocation: AllocationPolicy;
    monitoring: MonitoringConfig;
    optimization: OptimizationConfig;
}
export type PoolStrategy = 'static' | 'dynamic' | 'elastic' | 'predictive' | 'hybrid';
export interface PoolSizing {
    initialSize: number;
    minSize: number;
    maxSize: number;
    scaleUpThreshold: number;
    scaleDownThreshold: number;
    scaleUpIncrement: number;
    scaleDownDecrement: number;
    cooldownPeriod: number;
}
export interface AllocationPolicy {
    algorithm: AllocationAlgorithm;
    priorityHandling: PriorityHandling;
    preemption: PreemptionPolicy;
    fairness: FairnessPolicy;
    overflow: OverflowHandling;
}
export type AllocationAlgorithm = 'first_fit' | 'best_fit' | 'worst_fit' | 'buddy_system' | 'slab_allocation' | 'smart_placement';
export interface PriorityHandling {
    enabled: boolean;
    levels: number;
    aging: boolean;
    agingFactor: number;
    starvationPrevention: boolean;
}
export interface PreemptionPolicy {
    enabled: boolean;
    strategy: 'priority_based' | 'lru' | 'resource_pressure' | 'deadline_aware';
    gracePeriod: number;
    notificationEnabled: boolean;
}
export interface FairnessPolicy {
    enabled: boolean;
    algorithm: 'proportional_share' | 'lottery' | 'stride_scheduling';
    weights: Record<string, number>;
    quotas: Record<string, number>;
}
export interface OverflowHandling {
    strategy: 'queue' | 'reject' | 'redirect' | 'degrade';
    maxQueueSize: number;
    timeout: number;
    fallbackPool?: string;
}
export interface MonitoringConfig {
    metricsCollection: boolean;
    healthChecking: boolean;
    performanceTracking: boolean;
    allocationTracking: boolean;
    alerting: AlertingConfig;
}
export interface AlertingConfig {
    enabled: boolean;
    thresholds: {
        utilization: number;
        availability: number;
        performance: number;
        errors: number;
    };
    channels: string[];
}
export interface OptimizationConfig {
    defragmentation: DefragmentationConfig;
    loadBalancing: LoadBalancingConfig;
    caching: CachingConfig;
    prediction: PredictionConfig;
}
export interface DefragmentationConfig {
    enabled: boolean;
    threshold: number;
    algorithm: 'compact' | 'relocate' | 'merge';
    schedule: string;
}
export interface LoadBalancingConfig {
    enabled: boolean;
    algorithm: 'round_robin' | 'least_used' | 'resource_aware' | 'locality_aware';
    rebalanceThreshold: number;
    migrationCost: number;
}
export interface CachingConfig {
    enabled: boolean;
    size: number;
    ttl: number;
    evictionPolicy: 'lru' | 'lfu' | 'fifo' | 'random';
}
export interface PredictionConfig {
    enabled: boolean;
    algorithm: 'linear_regression' | 'arima' | 'neural_network';
    windowSize: number;
    accuracy: number;
}
export interface PoolMetrics {
    totalResources: number;
    availableResources: number;
    allocatedResources: number;
    utilizationRate: number;
    allocationRate: number;
    fragmentationRatio: number;
    averageAllocationTime: number;
    successfulAllocations: number;
    failedAllocations: number;
    preemptions: number;
    defragmentations: number;
}
export declare class ResourcePool extends EventEmitter {
    private config;
    private resources;
    private allocations;
    private waitingQueue;
    private metrics;
    private isRunning;
    private maintenanceTimer?;
    private monitoringTimer?;
    constructor(config?: Partial<PoolConfiguration>);
    /**
     * Start the resource pool
     */
    start(): void;
    /**
     * Stop the resource pool
     */
    stop(): void;
    /**
     * Allocate resources for a task
     */
    allocateResources(taskId: string, requirements: ResourceRequirements, priority?: number): Promise<ResourceAllocation>;
    /**
     * Release resources for a task
     */
    releaseResources(allocationId: string): boolean;
    /**
     * Get current pool metrics
     */
    getPoolMetrics(): PoolMetrics;
    /**
     * Get resource utilization
     */
    getResourceUtilization(): Record<ResourceType, number>;
    /**
     * Add resources to the pool
     */
    addResource(resource: PooledResource): void;
    /**
     * Remove resource from the pool
     */
    removeResource(resourceId: string): boolean;
    /**
     * Update pool configuration
     */
    updateConfiguration(updates: Partial<PoolConfiguration>): void;
    /**
     * Get current allocation status
     */
    getAllocationStatus(): Array<{
        taskId: string;
        allocation: ResourceAllocation;
        utilization: number;
        duration: number;
    }>;
    /**
     * Force defragmentation
     */
    defragment(): Promise<void>;
    private createDefaultConfiguration;
    private initializeMetrics;
    private initializePool;
    private createResource;
    private tryAllocate;
    private selectResources;
    private bestFitSelection;
    private firstFitSelection;
    private worstFitSelection;
    private canSatisfyRequirements;
    private allocateResource;
    private releaseResource;
    private shouldHandleOverflow;
    private handleOverflow;
    private degradeRequirements;
    private sortWaitingQueue;
    private processWaitingQueue;
    private releaseAllAllocations;
    private calculateAllocationUtilization;
    private startMaintenance;
    private startMonitoring;
    private performMaintenance;
    private cleanupExpiredAllocations;
    private shouldDefragment;
    private performDefragmentation;
    private autoScale;
    private scaleUp;
    private scaleDown;
    private updateMetrics;
    private calculateFragmentationRatio;
    private checkHealthStatus;
    private performHealthCheck;
    private checkAlerts;
    private applyConfigurationChanges;
}

// ---- src/optimization/parallel/task-scheduler.d.ts ----
/**
 * Task Scheduler for Phase 3.3.2
 * Advanced task scheduling with priorities, dependencies, and resource optimization
 */
import { EventEmitter } from 'events';
import type { ParallelTask, ResourceRequirements } from './parallel-optimizer.js';
export interface ScheduledTask extends ParallelTask {
    scheduledTime: Date;
    deadline?: Date;
    actualStartTime?: Date;
    actualEndTime?: Date;
    queueTime: number;
    waitTime: number;
    preemptable: boolean;
    affinityTags: string[];
}
export interface SchedulingPolicy {
    algorithm: SchedulingAlgorithm;
    preemption: PreemptionPolicy;
    priorityBoost: PriorityBoostConfig;
    deadline: DeadlineHandling;
    fairness: FairnessConfig;
    optimization: SchedulingOptimization;
}
export type SchedulingAlgorithm = 'fcfs' | 'sjf' | 'priority' | 'round_robin' | 'multilevel' | 'cfs' | 'deadline_aware' | 'resource_aware';
export interface PreemptionPolicy {
    enabled: boolean;
    strategy: 'priority_based' | 'time_slice' | 'resource_pressure' | 'deadline_pressure';
    timeSlice: number;
    priorityThreshold: number;
}
export interface PriorityBoostConfig {
    enabled: boolean;
    boostInterval: number;
    maxBoost: number;
    agingFactor: number;
}
export interface DeadlineHandling {
    strictMode: boolean;
    missedDeadlineAction: 'drop' | 'continue' | 'deprioritize';
    deadlineMargin: number;
}
export interface FairnessConfig {
    enabled: boolean;
    algorithm: 'proportional_share' | 'lottery' | 'deficit_round_robin';
    minimumShare: number;
    maxStarvationTime: number;
}
export interface SchedulingOptimization {
    loadBalancing: boolean;
    affinityOptimization: boolean;
    batchProcessing: boolean;
    adaptiveTimeSlicing: boolean;
}
export interface SchedulingMetrics {
    totalScheduled: number;
    averageWaitTime: number;
    averageResponseTime: number;
    averageTurnaroundTime: number;
    throughput: number;
    cpuUtilization: number;
    fairnessIndex: number;
    deadlineMissRate: number;
    preemptionCount: number;
    contextSwitches: number;
}
export interface TaskQueue {
    id: string;
    name: string;
    priority: number;
    tasks: ScheduledTask[];
    maxSize: number;
    timeSlice: number;
    algorithm: SchedulingAlgorithm;
}
export interface SchedulingDecision {
    taskId: string;
    action: 'schedule' | 'preempt' | 'defer' | 'reject';
    reason: string;
    estimatedStartTime: Date;
    estimatedCompletionTime: Date;
    assignedResources: ResourceRequirements;
    queueId?: string;
}
export interface ResourceAvailability {
    cpu: number;
    memory: number;
    io: number;
    network: number;
    workers: number;
    timestamp: Date;
}
export declare class TaskScheduler extends EventEmitter {
    private policy;
    private taskQueues;
    private activeTasks;
    private waitingTasks;
    private completedTasks;
    private metrics;
    private resourceAvailability;
    private schedulingTimer?;
    private isRunning;
    private virtualTime;
    private timeSliceCounter;
    constructor(policy?: Partial<SchedulingPolicy>);
    /**
     * Start the task scheduler
     */
    start(): void;
    /**
     * Stop the task scheduler
     */
    stop(): void;
    /**
     * Schedule a task
     */
    scheduleTask(task: ParallelTask, deadline?: Date): Promise<SchedulingDecision>;
    /**
     * Update resource availability
     */
    updateResourceAvailability(resources: Partial<ResourceAvailability>): void;
    /**
     * Get scheduling metrics
     */
    getSchedulingMetrics(): SchedulingMetrics;
    /**
     * Get current task queues status
     */
    getQueueStatus(): Array<{
        queueId: string;
        length: number;
        algorithm: string;
    }>;
    /**
     * Preempt a task
     */
    preemptTask(taskId: string, reason: string): Promise<boolean>;
    /**
     * Update scheduling policy
     */
    updatePolicy(updates: Partial<SchedulingPolicy>): void;
    /**
     * Add custom task queue
     */
    addTaskQueue(queue: TaskQueue): void;
    /**
     * Remove task queue
     */
    removeTaskQueue(queueId: string): boolean;
    /**
     * Get task by ID
     */
    getTask(taskId: string): ScheduledTask | null;
    /**
     * Cancel a scheduled task
     */
    cancelTask(taskId: string): boolean;
    private createDefaultPolicy;
    private initializeMetrics;
    private initializeResourceAvailability;
    private setupDefaultQueues;
    private startSchedulingLoop;
    private executeSchedulingCycle;
    private makeSchedulingDecision;
    private executeSchedulingDecision;
    private insertTaskIntoQueue;
    private insertByPriority;
    private insertByShortest;
    private insertByDeadline;
    private executeSchedulingAlgorithm;
    private executeTask;
    private simulateTaskExecution;
    private completeTask;
    private canSatisfyResourceRequirements;
    private allocateResources;
    private releaseResources;
    private selectQueue;
    private extractAffinityTags;
    private wouldMissDeadline;
    private estimateStartTime;
    private estimateCompletionTime;
    private optimizeResourceAllocation;
    private calculateLoadFactor;
    private processPriorityBoosting;
    private checkDeadlines;
    private handleMissedDeadline;
    private handlePreemption;
    private findLongestRunningTask;
    private processWaitingTasks;
    private reorganizeQueues;
    private findTaskInQueues;
    private updateMetrics;
    private getTotalQueuedTasks;
    private calculateThroughput;
    private calculateFairnessIndex;
}

// ---- src/providers/index.d.ts ----
export interface LLM {
    name: string;
    complete(input: {
        system?: string;
        prompt: string;
        temperature?: number;
    }): Promise<string>;
}
export declare function loadLLM(): Promise<LLM>;

// ---- src/providers/llm-anthropic.d.ts ----
import type { LLM } from './index.js';
declare const AnthropicProvider: LLM;
export default AnthropicProvider;

// ---- src/providers/llm-echo.d.ts ----
import type { LLM } from './index.js';
declare const Echo: LLM;
export default Echo;

// ---- src/providers/llm-gemini.d.ts ----
import type { LLM } from './index.js';
declare const GeminiProvider: LLM;
export default GeminiProvider;

// ---- src/providers/llm-openai.d.ts ----
import type { LLM } from './index.js';
declare const OpenAIProvider: LLM;
export default OpenAIProvider;

// ---- src/providers/recorder.d.ts ----
import type { LLM } from './index.js';
export declare function withRecorder(base: LLM, opts?: {
    dir?: string;
    replay?: boolean;
}): LLM;

// ---- src/quality/policy-loader.d.ts ----
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

// ---- src/quality/quality-gate-runner.d.ts ----
/**
 * Quality Gate Runner
 * Executes quality gates based on centralized policy configuration
 */
import { QualityPolicyLoader, QualityReport } from './policy-loader.js';
export interface QualityGateExecutionOptions {
    environment?: string;
    gates?: string[];
    parallel?: boolean;
    timeout?: number;
    dryRun?: boolean;
    verbose?: boolean;
    outputDir?: string;
}
export declare class QualityGateRunner {
    private policyLoader;
    private results;
    constructor(policyLoader?: QualityPolicyLoader);
    /**
     * Execute quality gates for environment
     */
    executeGates(options?: QualityGateExecutionOptions): Promise<QualityReport>;
    /**
     * Execute a single quality gate
     */
    private executeGate;
    /**
     * Execute a command with timeout
     */
    private executeCommand;
    /**
     * Parse command string into executable and arguments safely
     */
    private parseCommand;
    /**
     * Validate shell commands for security
     */
    private validateShellCommand;
    /**
     * Parse gate execution result
     */
    private parseGateResult;
    /**
     * Parse coverage results
     */
    private parseCoverageResult;
    /**
     * Parse linting results
     */
    private parseLintingResult;
    /**
     * Parse security results
     */
    private parseSecurityResult;
    /**
     * Parse performance results
     */
    private parsePerformanceResult;
    /**
     * Parse accessibility results
     */
    private parseAccessibilityResult;
    /**
     * Save quality report to file
     */
    private saveReport;
    /**
     * Generate empty report for when no gates are found
     */
    private generateEmptyReport;
    /**
     * Print execution summary
     */
    private printSummary;
}
export declare function runQualityGatesCLI(args: string[]): Promise<void>;

// ---- src/resilience/backoff-strategies.d.ts ----
/**
 * Exponential Backoff with Full Jitter Implementation
 * Implements resilient retry strategies with various jitter options
 */
export interface RetryOptions {
    maxRetries: number;
    baseDelayMs: number;
    maxDelayMs: number;
    jitterType: 'none' | 'full' | 'equal' | 'decorrelated';
    multiplier: number;
    onRetry?: (attempt: number, delay: number, error: Error) => void;
    shouldRetry?: (error: Error, attempt: number) => boolean;
    timeout?: number;
}
export interface RetryResult<T> {
    success: boolean;
    result?: T;
    error?: Error;
    attempts: number;
    totalTime: number;
    delays: number[];
}
export declare class BackoffStrategy {
    private options;
    constructor(options?: Partial<RetryOptions>);
    /**
     * Execute operation with exponential backoff and full jitter
     */
    executeWithRetry<T>(operation: () => Promise<T>, operationName?: string): Promise<RetryResult<T>>;
    /**
     * Calculate delay with jitter based on strategy
     */
    private calculateDelay;
    /**
     * Execute operation with timeout using AbortController for better resource management
     */
    private executeWithTimeout;
    /**
     * Sleep for specified milliseconds
     */
    private sleep;
    /**
     * Default retry condition - determines if error is retryable
     */
    private isRetryableError;
}
/**
 * Circuit Breaker Pattern Implementation
 */
export declare enum CircuitState {
    CLOSED = "CLOSED",
    OPEN = "OPEN",
    HALF_OPEN = "HALF_OPEN"
}
export interface CircuitBreakerOptions {
    failureThreshold: number;
    recoveryTimeout: number;
    monitoringPeriod: number;
    expectedErrors?: string[];
    onStateChange?: (state: CircuitState, error?: Error) => void;
}
export interface CircuitBreakerStats {
    state: CircuitState;
    failures: number;
    successes: number;
    totalRequests: number;
    lastFailureTime?: number;
    lastSuccessTime?: number;
    uptime: number;
}
export declare class CircuitBreaker {
    private options;
    private state;
    private failures;
    private successes;
    private totalRequests;
    private lastFailureTime?;
    private lastSuccessTime?;
    private nextAttemptTime?;
    private startTime;
    constructor(options: CircuitBreakerOptions);
    /**
     * Execute operation through circuit breaker
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Handle successful operation
     */
    private onSuccess;
    /**
     * Handle failed operation
     */
    private onFailure;
    /**
     * Check if circuit should be opened
     */
    private shouldOpenCircuit;
    /**
     * Check if circuit should attempt reset
     */
    private shouldAttemptReset;
    /**
     * Get time until next attempt is allowed
     */
    private getTimeUntilNextAttempt;
    /**
     * Get circuit breaker statistics
     */
    getStats(): CircuitBreakerStats;
    /**
     * Reset circuit breaker
     */
    reset(): void;
    /**
     * Force circuit open (for testing or maintenance)
     */
    forceOpen(): void;
    /**
     * Force circuit closed
     */
    forceClosed(): void;
    /**
     * Validate circuit breaker options
     */
    private validateOptions;
}
/**
 * Rate Limiter with Token Bucket Algorithm
 */
export interface RateLimiterOptions {
    tokensPerInterval: number;
    interval: number;
    maxTokens: number;
}
export declare class TokenBucketRateLimiter {
    private options;
    private tokens;
    private lastRefillTime;
    constructor(options: RateLimiterOptions);
    /**
     * Try to consume tokens for rate limiting
     */
    consume(tokens?: number): Promise<boolean>;
    /**
     * Wait until tokens are available
     */
    waitForTokens(tokens?: number): Promise<void>;
    /**
     * Get current token count
     */
    getTokenCount(): number;
    /**
     * Get time until next refill
     */
    private getTimeUntilNextRefill;
    /**
     * Refill tokens based on elapsed time
     */
    private refillTokens;
    /**
     * Sleep for specified milliseconds
     */
    private sleep;
    /**
     * Validate rate limiter options
     */
    private validateOptions;
}
/**
 * Resilient HTTP Client with all patterns combined
 */
export interface ResilientHttpOptions {
    retryOptions?: Partial<RetryOptions>;
    circuitBreakerOptions?: CircuitBreakerOptions;
    rateLimiterOptions?: RateLimiterOptions;
    baseURL?: string;
    defaultHeaders?: Record<string, string>;
    timeout?: number;
}
export declare class ResilientHttpClient {
    private options;
    private backoffStrategy;
    private circuitBreaker?;
    private rateLimiter?;
    constructor(options?: ResilientHttpOptions);
    /**
     * Make resilient HTTP request
     */
    request<T>(url: string, options?: RequestInit): Promise<T>;
    /**
     * Execute actual HTTP request
     */
    private executeHttpRequest;
    /**
     * Get system health stats
     */
    getHealthStats(): {
        circuitBreaker: CircuitBreakerStats;
        rateLimiter: {
            availableTokens: number;
            maxTokens: number;
        };
    };
}

// ---- src/resilience/bulkhead-isolation.d.ts ----
/**
 * Bulkhead Isolation Pattern Implementation
 * Isolates critical resources to prevent cascading failures
 */
export interface BulkheadOptions {
    name: string;
    maxConcurrent: number;
    maxQueued: number;
    timeoutMs: number;
    onReject?: (reason: 'capacity' | 'timeout' | 'queue_full') => void;
}
export interface BulkheadStats {
    name: string;
    active: number;
    queued: number;
    maxConcurrent: number;
    maxQueued: number;
    totalExecuted: number;
    totalRejected: number;
    averageExecutionTime: number;
    rejectionReasons: Record<string, number>;
}
export declare class Bulkhead {
    private options;
    private active;
    private queue;
    private totalExecuted;
    private totalRejected;
    private executionTimes;
    private rejectionReasons;
    constructor(options: BulkheadOptions);
    /**
     * Execute operation within bulkhead constraints
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Execute operation immediately
     */
    private executeImmediately;
    /**
     * Process queued operations
     */
    private processQueue;
    /**
     * Remove operation from queue
     */
    private removeFromQueue;
    /**
     * Handle operation rejection
     */
    private handleRejection;
    /**
     * Record successful execution
     */
    private recordExecution;
    /**
     * Get bulkhead statistics
     */
    getStats(): BulkheadStats;
    /**
     * Reset bulkhead statistics
     */
    reset(): void;
    /**
     * Get current load factor (0-1)
     */
    getLoadFactor(): number;
    /**
     * Check if bulkhead is healthy
     */
    isHealthy(): boolean;
    /**
     * Validate bulkhead options
     */
    private validateOptions;
}
/**
 * Bulkhead Manager for managing multiple isolated bulkheads
 */
export declare class BulkheadManager {
    private bulkheads;
    /**
     * Create or get a bulkhead
     */
    getBulkhead(options: BulkheadOptions): Bulkhead;
    /**
     * Execute operation in named bulkhead
     */
    executeInBulkhead<T>(bulkheadName: string, operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Get all bulkhead statistics
     */
    getAllStats(): Record<string, BulkheadStats>;
    /**
     * Get system health across all bulkheads
     */
    getSystemHealth(): {
        healthy: boolean;
        totalBulkheads: number;
        healthyBulkheads: number;
        totalActive: number;
        totalQueued: number;
        averageLoadFactor: number;
    };
    /**
     * Reset all bulkheads
     */
    resetAll(): void;
    /**
     * Remove a bulkhead
     */
    removeBulkhead(name: string): boolean;
    /**
     * Get bulkhead names
     */
    getBulkheadNames(): string[];
}

// ---- src/resilience/index.d.ts ----
/**
 * Comprehensive Resilience System
 * Exports all resilience patterns and utilities
 */
import { ResilientHttpClient, type CircuitBreakerStats } from './backoff-strategies.js';
import { BulkheadManager, type BulkheadStats } from './bulkhead-isolation.js';
import { TimeoutManager, type TimeoutStats } from './timeout-patterns.js';
export { BackoffStrategy, CircuitBreaker, CircuitState, TokenBucketRateLimiter, ResilientHttpClient, type RetryOptions, type RetryResult, type CircuitBreakerOptions, type CircuitBreakerStats, type RateLimiterOptions, type ResilientHttpOptions, } from './backoff-strategies.js';
export { Bulkhead, BulkheadManager, type BulkheadOptions, type BulkheadStats, } from './bulkhead-isolation.js';
export { TimeoutWrapper, AdaptiveTimeout, HierarchicalTimeout, TimeoutManager, TimeoutError, type TimeoutOptions, type AdaptiveTimeoutOptions, type TimeoutStats, } from './timeout-patterns.js';
/**
 * Comprehensive resilience configuration
 */
export interface ResilienceConfig {
    retry?: {
        enabled: boolean;
        maxRetries: number;
        baseDelayMs: number;
        maxDelayMs: number;
        jitterType: 'none' | 'full' | 'equal' | 'decorrelated';
        multiplier: number;
    };
    circuitBreaker?: {
        enabled: boolean;
        failureThreshold: number;
        recoveryTimeout: number;
        monitoringPeriod: number;
        expectedErrors?: string[];
    };
    rateLimiter?: {
        enabled: boolean;
        tokensPerInterval: number;
        interval: number;
        maxTokens: number;
    };
    bulkhead?: {
        enabled: boolean;
        maxConcurrent: number;
        maxQueued: number;
        timeoutMs: number;
    };
    timeout?: {
        enabled: boolean;
        timeoutMs: number;
        adaptive?: {
            enabled: boolean;
            baseTimeoutMs: number;
            maxTimeoutMs: number;
            minTimeoutMs: number;
            adaptationFactor: number;
            windowSize: number;
        };
    };
}
/**
 * Default resilience configuration
 */
export declare const DEFAULT_RESILIENCE_CONFIG: ResilienceConfig;
/**
 * Comprehensive resilience system that combines all patterns
 */
export declare class ResilienceSystem {
    private config;
    private backoffStrategy?;
    private circuitBreaker?;
    private rateLimiter?;
    private bulkheadManager;
    private timeoutManager;
    private httpClient?;
    constructor(config?: ResilienceConfig);
    /**
     * Initialize resilience components based on configuration
     */
    private initialize;
    /**
     * Execute operation with comprehensive resilience patterns
     */
    executeResilient<T>(operation: () => Promise<T>, options?: {
        operationName?: string;
        bulkheadName?: string;
        timeoutMs?: number;
        useAdaptiveTimeout?: boolean;
    }): Promise<T>;
    /**
     * Get resilient HTTP client
     */
    getHttpClient(): ResilientHttpClient;
    /**
     * Get bulkhead manager
     */
    getBulkheadManager(): BulkheadManager;
    /**
     * Get timeout manager
     */
    getTimeoutManager(): TimeoutManager;
    /**
     * Get comprehensive system health
     */
    getSystemHealth(): {
        overall: boolean;
        components: {
            circuitBreaker?: CircuitBreakerStats;
            rateLimiter?: {
                availableTokens: number;
                maxTokens: number;
            };
            bulkheads: Record<string, BulkheadStats>;
            timeouts: Record<string, TimeoutStats>;
            http?: any;
        };
        bulkheadSystem: ReturnType<BulkheadManager['getSystemHealth']>;
    };
    /**
     * Reset all resilience components
     */
    reset(): void;
    /**
     * Update configuration
     */
    updateConfig(config: Partial<ResilienceConfig>): void;
    /**
     * Get current configuration
     */
    getConfig(): ResilienceConfig;
}
/**
 * Create a pre-configured resilience system for common use cases
 */
export declare function createResilienceSystem(preset?: 'default' | 'aggressive' | 'conservative' | 'minimal'): ResilienceSystem;

// ---- src/resilience/timeout-patterns.d.ts ----
/**
 * Advanced Timeout Patterns Implementation
 * Provides sophisticated timeout handling strategies
 */
export interface TimeoutOptions {
    timeoutMs: number;
    onTimeout?: (duration: number) => void;
    abortController?: AbortController;
    timeoutMessage?: string;
}
export interface AdaptiveTimeoutOptions extends TimeoutOptions {
    baseTimeoutMs: number;
    maxTimeoutMs: number;
    minTimeoutMs: number;
    adaptationFactor: number;
    windowSize: number;
}
export interface TimeoutStats {
    totalOperations: number;
    timeouts: number;
    successfulOperations: number;
    averageExecutionTime: number;
    timeoutRate: number;
    currentTimeoutMs: number;
}
/**
 * Basic timeout wrapper for operations
 */
export declare class TimeoutWrapper {
    private options;
    constructor(options: TimeoutOptions);
    /**
     * Execute operation with timeout
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    private validateOptions;
}
/**
 * Custom timeout error
 */
export declare class TimeoutError extends Error {
    readonly timeoutMs: number;
    readonly actualDuration: number;
    readonly name = "TimeoutError";
    constructor(message: string, timeoutMs: number, actualDuration: number);
}
/**
 * Adaptive timeout that adjusts based on historical performance
 */
export declare class AdaptiveTimeout {
    private options;
    private executionTimes;
    private totalOperations;
    private timeouts;
    private successfulOperations;
    private currentTimeoutMs;
    constructor(options: AdaptiveTimeoutOptions);
    /**
     * Execute operation with adaptive timeout
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Record successful operation and adapt timeout
     */
    private recordSuccess;
    /**
     * Adapt timeout based on recent performance
     */
    private adaptTimeout;
    /**
     * Calculate percentile from sorted array
     */
    private calculatePercentile;
    /**
     * Get timeout statistics
     */
    getStats(): TimeoutStats;
    /**
     * Reset statistics and timeout to base value
     */
    reset(): void;
    /**
     * Get current timeout value
     */
    getCurrentTimeout(): number;
    /**
     * Manually set timeout value
     */
    setTimeout(timeoutMs: number): void;
    private validateOptions;
}
/**
 * Hierarchical timeout with cascading timeouts for nested operations
 */
export declare class HierarchicalTimeout {
    private static readonly MAX_TIMEOUT_MS;
    private static readonly FALLBACK_TIMEOUT_MS;
    private activeTimeouts;
    private operationStack;
    /**
     * Execute operation with hierarchical timeout
     */
    executeWithHierarchy<T>(operation: () => Promise<T>, operationId: string, timeoutMs: number, parentOperationId?: string): Promise<T>;
    /**
     * Clean up operation timeout
     */
    private cleanupOperation;
    /**
     * Cancel all active timeouts
     */
    cancelAll(): void;
    /**
     * Get active operations
     */
    getActiveOperations(): string[];
    /**
     * Check if operation is active
     */
    isOperationActive(operationId: string): boolean;
}
/**
 * Timeout manager for coordinating multiple timeout strategies
 */
export declare class TimeoutManager {
    private adaptiveTimeouts;
    private hierarchicalTimeout;
    /**
     * Create or get adaptive timeout instance
     */
    getAdaptiveTimeout(name: string, options: AdaptiveTimeoutOptions): AdaptiveTimeout;
    /**
     * Execute with adaptive timeout
     */
    executeWithAdaptiveTimeout<T>(name: string, operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Execute with hierarchical timeout
     */
    executeWithHierarchicalTimeout<T>(operation: () => Promise<T>, operationId: string, timeoutMs: number, parentOperationId?: string): Promise<T>;
    /**
     * Get all timeout statistics
     */
    getAllStats(): Record<string, TimeoutStats>;
    /**
     * Reset all timeout managers
     */
    resetAll(): void;
    /**
     * Get active hierarchical operations
     */
    getActiveHierarchicalOperations(): string[];
    /**
     * Cancel all active operations
     */
    cancelAllOperations(): void;
}

// ---- src/runner/main.d.ts ----
export declare function main(): Promise<void>;

// ---- src/runtime/conformance-guards.d.ts ----
/**
 * Runtime Conformance Guards
 *
 * Zod-based runtime validation with OpenTelemetry integration
 * for detecting contract mismatches and specification drift
 */
import { z } from 'zod';
export interface ConformanceResult<T = any> {
    success: boolean;
    data?: T;
    errors: string[];
    warnings: string[];
    metadata: {
        schemaName?: string;
        duration: number;
        timestamp: string;
        context?: Record<string, any>;
    };
}
export interface GuardConfig {
    enabled: boolean;
    failOnViolation: boolean;
    logViolations: boolean;
    generateArtifacts: boolean;
    telemetryEnabled: boolean;
    context?: Record<string, any>;
}
/**
 * Runtime Conformance Guard
 *
 * Validates data against Zod schemas with telemetry and error handling
 */
export declare class ConformanceGuard<T> {
    private schema;
    private schemaName;
    private config;
    constructor(schema: z.ZodSchema<T>, schemaName: string, config?: Partial<GuardConfig>);
    /**
     * Validate input data against schema
     */
    validateInput(data: unknown, context?: Record<string, any>): Promise<ConformanceResult<T>>;
    /**
     * Validate output data against schema
     */
    validateOutput(data: unknown, context?: Record<string, any>): Promise<ConformanceResult<T>>;
    /**
     * Core validation logic with telemetry
     */
    private validate;
    /**
     * Generate failure artifact for conformance violations
     */
    private generateFailureArtifact;
    /**
     * Sanitize data for logging (remove sensitive information)
     */
    private sanitizeForLogging;
    /**
     * Update guard configuration
     */
    updateConfig(newConfig: Partial<GuardConfig>): void;
    /**
     * Get current configuration
     */
    getConfig(): GuardConfig;
}
/**
 * Conformance Violation Error
 */
export declare class ConformanceViolationError extends Error {
    schemaName: string;
    direction: 'input' | 'output';
    validationErrors: string[];
    data: unknown;
    constructor(message: string, schemaName: string, direction: 'input' | 'output', validationErrors: string[], data: unknown);
}
/**
 * Factory for creating common guards
 */
export declare class GuardFactory {
    /**
     * Create API request guard
     */
    static apiRequest<T>(schema: z.ZodSchema<T>, operationId: string): ConformanceGuard<T>;
    /**
     * Create API response guard
     */
    static apiResponse<T>(schema: z.ZodSchema<T>, operationId: string): ConformanceGuard<T>;
    /**
     * Create database entity guard
     */
    static databaseEntity<T>(schema: z.ZodSchema<T>, entityName: string): ConformanceGuard<T>;
    /**
     * Create configuration guard
     */
    static configuration<T>(schema: z.ZodSchema<T>, configName: string): ConformanceGuard<T>;
    /**
     * Create event guard
     */
    static event<T>(schema: z.ZodSchema<T>, eventType: string): ConformanceGuard<T>;
}
/**
 * Decorator for automatic method validation
 */
export declare function ValidateInput<T>(guard: ConformanceGuard<T>): (target: any, propertyKey: string, descriptor: PropertyDescriptor) => PropertyDescriptor;
/**
 * Decorator for automatic output validation
 */
export declare function ValidateOutput<T>(guard: ConformanceGuard<T>): (target: any, propertyKey: string, descriptor: PropertyDescriptor) => PropertyDescriptor;
/**
 * Middleware factory for Express.js integration
 */
export declare function createExpressMiddleware<T>(guard: ConformanceGuard<T>, target?: 'body' | 'query' | 'params'): (req: any, res: any, next: any) => Promise<any>;
/**
 * Global conformance registry for schema management
 */
export declare class ConformanceRegistry {
    private static instance;
    private guards;
    private schemas;
    static getInstance(): ConformanceRegistry;
    /**
     * Register a schema with the registry
     */
    registerSchema<T>(name: string, schema: z.ZodSchema<T>): void;
    /**
     * Register a guard with the registry
     */
    registerGuard<T>(name: string, guard: ConformanceGuard<T>): void;
    /**
     * Get a guard by name
     */
    getGuard<T>(name: string): ConformanceGuard<T> | undefined;
    /**
     * Get a schema by name
     */
    getSchema<T>(name: string): z.ZodSchema<T> | undefined;
    /**
     * Create a guard from a registered schema
     */
    createGuard<T>(schemaName: string, guardName?: string, config?: Partial<GuardConfig>): ConformanceGuard<T> | null;
    /**
     * List all registered schemas
     */
    listSchemas(): string[];
    /**
     * List all registered guards
     */
    listGuards(): string[];
    /**
     * Clear all registrations
     */
    clear(): void;
}

// ---- src/runtime/runtime-middleware.d.ts ----
/**
 * Runtime Conformance Middleware
 *
 * Express and Fastify middleware for automatic runtime contract validation
 * with OpenTelemetry integration and failure artifact generation
 */
import { Request, Response, NextFunction } from 'express';
import { FastifyInstance } from 'fastify';
import { z } from 'zod';
export interface MiddlewareConfig {
    enabled: boolean;
    strictMode: boolean;
    logErrors: boolean;
    generateArtifacts: boolean;
    includeRequestInfo: boolean;
    customErrorHandler?: (error: any, req: any, res: any) => void;
}
/**
 * Express Middleware Factory
 */
export declare class ExpressConformanceMiddleware {
    private config;
    constructor(config?: Partial<MiddlewareConfig>);
    /**
     * Validate request body
     */
    validateRequestBody<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => Promise<void>;
    /**
     * Validate query parameters
     */
    validateQueryParams<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => Promise<void>;
    /**
     * Validate path parameters
     */
    validatePathParams<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => Promise<void>;
    /**
     * Validate response data
     */
    validateResponse<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => void;
    /**
     * Combined request/response validation middleware
     */
    validate<TReq, TRes>(requestSchema: z.ZodSchema<TReq> | null, responseSchema: z.ZodSchema<TRes> | null, operationId: string, target?: 'body' | 'query' | 'params'): ((req: Request, res: Response, next: NextFunction) => void)[];
    private createValidationContext;
    private handleValidationError;
    private handleMiddlewareError;
}
/**
 * Fastify Plugin for Runtime Conformance
 */
export declare function fastifyConformancePlugin(fastify: FastifyInstance, options?: {
    config?: Partial<MiddlewareConfig>;
    schemas?: Record<string, z.ZodSchema<any>>;
}): Promise<void>;
/**
 * OpenAPI Integration Helper
 */
export declare class OpenAPIConformanceIntegration {
    private middleware;
    constructor(config?: Partial<MiddlewareConfig>);
    /**
     * Generate middleware from OpenAPI operation
     */
    generateMiddleware(operation: {
        operationId: string;
        requestBody?: {
            schema: z.ZodSchema<any>;
        };
        parameters?: Array<{
            schema: z.ZodSchema<any>;
            in: 'query' | 'path';
        }>;
        responses?: {
            [status: string]: {
                schema: z.ZodSchema<any>;
            };
        };
    }): any[];
}
/**
 * Global middleware registry
 */
export declare class MiddlewareRegistry {
    private static instance;
    private expressMiddleware;
    private registeredRoutes;
    constructor(config?: Partial<MiddlewareConfig>);
    static getInstance(config?: Partial<MiddlewareConfig>): MiddlewareRegistry;
    /**
     * Register a route with validation
     */
    registerRoute(path: string, method: string, operationId: string, schemas: {
        request?: z.ZodSchema<any>;
        response?: z.ZodSchema<any>;
        query?: z.ZodSchema<any>;
        params?: z.ZodSchema<any>;
    }): any[];
    /**
     * Get middleware for a route
     */
    getMiddleware(path: string, method: string): any[];
    /**
     * List all registered routes
     */
    listRoutes(): Array<{
        path: string;
        method: string;
        operationId: string;
    }>;
}

// ---- src/schemas/llm.d.ts ----
import { z } from 'zod';
export declare const OpenAIChat: z.ZodObject<{
    choices: z.ZodArray<z.ZodObject<{
        message: z.ZodObject<{
            content: z.ZodDefault<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            content?: string;
        }, {
            content?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        message?: {
            content?: string;
        };
    }, {
        message?: {
            content?: string;
        };
    }>, "atleastone">;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    choices: z.ZodArray<z.ZodObject<{
        message: z.ZodObject<{
            content: z.ZodDefault<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            content?: string;
        }, {
            content?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        message?: {
            content?: string;
        };
    }, {
        message?: {
            content?: string;
        };
    }>, "atleastone">;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    choices: z.ZodArray<z.ZodObject<{
        message: z.ZodObject<{
            content: z.ZodDefault<z.ZodString>;
        }, "strip", z.ZodTypeAny, {
            content?: string;
        }, {
            content?: string;
        }>;
    }, "strip", z.ZodTypeAny, {
        message?: {
            content?: string;
        };
    }, {
        message?: {
            content?: string;
        };
    }>, "atleastone">;
}, z.ZodTypeAny, "passthrough">>;
export declare const AnthropicMsg: z.ZodObject<{
    content: z.ZodAny;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    content: z.ZodAny;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    content: z.ZodAny;
}, z.ZodTypeAny, "passthrough">>;
export declare const GeminiResp: z.ZodObject<{
    response: z.ZodAny;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    response: z.ZodAny;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    response: z.ZodAny;
}, z.ZodTypeAny, "passthrough">>;
export declare const BenchmarkResult: z.ZodObject<{
    summary: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        hz: z.ZodNumber;
        meanMs: z.ZodNumber;
        sdMs: z.ZodOptional<z.ZodNumber>;
        samples: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        name?: string;
        hz?: number;
        samples?: number;
        meanMs?: number;
        sdMs?: number;
    }, {
        name?: string;
        hz?: number;
        samples?: number;
        meanMs?: number;
        sdMs?: number;
    }>, "many">;
    date: z.ZodOptional<z.ZodString>;
    env: z.ZodOptional<z.ZodAny>;
    config: z.ZodOptional<z.ZodAny>;
}, "passthrough", z.ZodTypeAny, z.objectOutputType<{
    summary: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        hz: z.ZodNumber;
        meanMs: z.ZodNumber;
        sdMs: z.ZodOptional<z.ZodNumber>;
        samples: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        name?: string;
        hz?: number;
        samples?: number;
        meanMs?: number;
        sdMs?: number;
    }, {
        name?: string;
        hz?: number;
        samples?: number;
        meanMs?: number;
        sdMs?: number;
    }>, "many">;
    date: z.ZodOptional<z.ZodString>;
    env: z.ZodOptional<z.ZodAny>;
    config: z.ZodOptional<z.ZodAny>;
}, z.ZodTypeAny, "passthrough">, z.objectInputType<{
    summary: z.ZodArray<z.ZodObject<{
        name: z.ZodString;
        hz: z.ZodNumber;
        meanMs: z.ZodNumber;
        sdMs: z.ZodOptional<z.ZodNumber>;
        samples: z.ZodOptional<z.ZodNumber>;
    }, "strip", z.ZodTypeAny, {
        name?: string;
        hz?: number;
        samples?: number;
        meanMs?: number;
        sdMs?: number;
    }, {
        name?: string;
        hz?: number;
        samples?: number;
        meanMs?: number;
        sdMs?: number;
    }>, "many">;
    date: z.ZodOptional<z.ZodString>;
    env: z.ZodOptional<z.ZodAny>;
    config: z.ZodOptional<z.ZodAny>;
}, z.ZodTypeAny, "passthrough">>;

// ---- src/security/sbom-generator.d.ts ----
/**
 * Software Bill of Materials (SBOM) Generator
 * Generates comprehensive SBOMs for security and compliance
 */
export interface SBOMComponent {
    name: string;
    version: string;
    type: 'library' | 'framework' | 'application' | 'container' | 'file' | 'operating-system';
    supplier?: string;
    author?: string;
    description?: string;
    licenses?: string[];
    cpe?: string;
    purl?: string;
    hashes?: {
        algorithm: string;
        value: string;
    }[];
    externalReferences?: {
        type: string;
        url: string;
    }[];
    dependencies?: string[];
    vulnerabilities?: {
        id: string;
        severity: 'low' | 'medium' | 'high' | 'critical';
        description?: string;
        references?: string[];
    }[];
}
export interface SBOMMetadata {
    timestamp: string;
    tools: {
        vendor: string;
        name: string;
        version: string;
    }[];
    authors: string[];
    supplier?: string;
}
export interface SBOM {
    bomFormat: string;
    specVersion: string;
    serialNumber: string;
    version: number;
    metadata: SBOMMetadata;
    components: SBOMComponent[];
    dependencies?: {
        ref: string;
        dependsOn?: string[];
    }[];
    vulnerabilities?: {
        bom_ref: string;
        id: string;
        source?: {
            name: string;
            url: string;
        };
        ratings?: {
            source?: string;
            score?: number;
            severity?: string;
            method?: string;
        }[];
        cwes?: number[];
        description?: string;
        advisories?: {
            title?: string;
            url?: string;
        }[];
    }[];
}
export interface SBOMGeneratorOptions {
    projectRoot: string;
    outputPath?: string;
    includeDevDependencies?: boolean;
    includeLicenses?: boolean;
    includeHashes?: boolean;
    includeVulnerabilities?: boolean;
    format?: 'json' | 'xml';
    customComponents?: SBOMComponent[];
}
export declare class SBOMGenerator {
    private options;
    constructor(options: SBOMGeneratorOptions);
    /**
     * Generate complete SBOM
     */
    generate(): Promise<SBOM>;
    /**
     * Generate and save SBOM to file
     */
    generateAndSave(): Promise<string>;
    /**
     * Extract package dependencies from package.json and package-lock.json
     */
    private extractPackageDependencies;
    /**
     * Extract application files
     */
    private extractApplicationFiles;
    /**
     * Generate metadata section
     */
    private generateMetadata;
    /**
     * Extract dependency graph
     */
    private extractDependencyGraph;
    /**
     * Extract vulnerabilities (placeholder for vulnerability scanning integration)
     */
    private extractVulnerabilities;
    /**
     * Extract license information
     */
    private extractLicenses;
    /**
     * Generate file hashes
     */
    private generateFileHashes;
    /**
     * Generate serial number for SBOM
     */
    private generateSerialNumber;
    /**
     * Convert SBOM to XML format (CycloneDX XML)
     */
    private convertToXML;
    /**
     * Simple hash function for deterministic mock data generation
     */
    private simpleHash;
    /**
     * Escape XML characters
     */
    private escapeXML;
}

// ---- src/self-improvement/codebase-analysis.d.ts ----
/**
 * Phase 1: Codebase Analysis using NaturalLanguageTaskAdapter
 *
 * This module performs a comprehensive analysis of the ae-framework codebase
 * using the natural language processing capabilities to identify patterns,
 * issues, and improvement opportunities.
 */
export interface CodebaseAnalysisResult {
    summary: string;
    analysis: string;
    recommendations: string[];
    nextActions: string[];
    warnings: string[];
    shouldBlockProgress: boolean;
    typeScriptErrors: number;
    testCoverage: {
        files: number;
        coverage: number;
    };
    codeQuality: {
        score: number;
        issues: string[];
    };
}
export declare class CodebaseAnalyzer {
    private adapter;
    constructor();
    /**
     * Perform comprehensive analysis of the ae-framework codebase
     */
    analyzeCodebase(): Promise<CodebaseAnalysisResult>;
    /**
     * Count TypeScript compilation errors by running tsc
     */
    private countTypeScriptErrors;
    /**
     * Analyze test coverage by counting test files and estimating coverage
     */
    private analyzeTestCoverage;
    /**
     * Analyze code quality by identifying common issues
     */
    private analyzeCodeQuality;
    /**
     * Extract requirements-like statements from the codebase
     */
    private extractCodebaseRequirements;
    /**
     * Find all test files in the project
     */
    private findTestFiles;
    /**
     * Find all source files in the project
     */
    private findSourceFiles;
    /**
     * Generate detailed report from analysis results
     */
    generateReport(results: CodebaseAnalysisResult): string;
}
export default CodebaseAnalyzer;

// ---- src/self-improvement/demo.d.ts ----
/**
 * ae-framework Self-Improvement TDD Infrastructure Demo
 *
 * This module demonstrates the complete TDD infrastructure setup and validates
 * all components are working correctly for the self-improvement project.
 */
export interface DemoConfig {
    projectRoot: string;
    configFile: string;
    validateComponents: boolean;
    runSampleTDDCycle: boolean;
}
export declare class SelfImprovementDemo {
    private config;
    private tddSetup?;
    private gitHooksSetup?;
    constructor(config?: Partial<DemoConfig>);
    /**
     * Run complete TDD infrastructure demonstration
     */
    runDemo(): Promise<{
        success: boolean;
        phases: Array<{
            phase: string;
            success: boolean;
            message: string;
            duration: number;
        }>;
        summary: string;
    }>;
    /**
     * Run a single phase with timing and error handling
     */
    private runPhase;
    /**
     * Validate ae-framework-v2.yml configuration
     */
    private validateConfiguration;
    /**
     * Set up TDD infrastructure
     */
    private setupTDDInfrastructure;
    /**
     * Set up git hooks
     */
    private setupGitHooks;
    /**
     * Validate all components are working
     */
    private validateAllComponents;
    /**
     * Run a sample TDD cycle to demonstrate functionality
     */
    private runSampleTDDCycle;
    /**
     * Generate final report
     */
    private generateFinalReport;
    /**
     * Generate summary of demo results
     */
    private generateSummary;
}
export declare const createSelfImprovementDemo: (config?: Partial<DemoConfig>) => SelfImprovementDemo;
export declare const runSelfImprovementDemo: () => Promise<never>;

// ---- src/self-improvement/phase2-requirements-analysis.d.ts ----
/**
 * Phase 2: Natural Language Requirements Analysis
 *
 * Uses the ae-framework's NaturalLanguageTaskAdapter to systematically
 * analyze requirements for TypeScript error resolution and framework improvement.
 */
import { ProcessedRequirements } from '../agents/natural-language-task-adapter.js';
export interface Phase2AnalysisResult {
    errorRequirements: ProcessedRequirements;
    frameworkRequirements: ProcessedRequirements;
    architecturalRequirements: ProcessedRequirements;
    prioritizedActions: {
        high: string[];
        medium: string[];
        low: string[];
    };
    systematicPlan: {
        phase: string;
        description: string;
        tasks: string[];
        expectedOutcome: string;
    }[];
}
export declare class Phase2RequirementsAnalyzer {
    private adapter;
    constructor();
    /**
     * Perform comprehensive Phase 2 requirements analysis
     */
    analyzeRequirements(): Promise<Phase2AnalysisResult>;
    /**
     * Analyze requirements for TypeScript error resolution
     */
    private analyzeTypeScriptErrorRequirements;
    /**
     * Analyze framework architectural requirements
     */
    private analyzeFrameworkRequirements;
    /**
     * Analyze architectural improvement requirements
     */
    private analyzeArchitecturalRequirements;
    /**
     * Prioritize actions based on requirements analysis
     */
    private prioritizeActions;
    /**
     * Create systematic improvement plan
     */
    private createSystematicPlan;
    /**
     * Generate comprehensive requirements report
     */
    generateReport(results: Phase2AnalysisResult): string;
}
export default Phase2RequirementsAnalyzer;

// ---- src/self-improvement/phase3-formal-testing.d.ts ----
/**
 * Phase 3: Formal Specification & Testing Phase
 *
 * Uses ae-framework's FormalAgent and TDDAgent to create formal specifications
 * and automated tests for TypeScript error resolution and quality improvement.
 */
export interface Phase3Result {
    formalSpecifications: {
        typeScriptErrorResolution: any;
        codeQualityImprovement: any;
        testCoverageEnhancement: any;
    };
    generatedTests: {
        unitTests: string[];
        integrationTests: string[];
        typeValidationTests: string[];
    };
    validationResults: {
        specificationCompliance: boolean;
        testCoverage: number;
        qualityScore: number;
        errors: string[];
        warnings: string[];
    };
}
export declare class Phase3FormalTesting {
    private formalAgent;
    private tddAgent;
    private validationAdapter;
    constructor();
    /**
     * Execute Phase 3: Formal Specification and Testing
     */
    executePhase3(): Promise<Phase3Result>;
    /**
     * Generate formal specifications for TypeScript error resolution
     */
    private generateFormalSpecifications;
    /**
     * Generate automated tests using TDDAgent
     */
    private generateAutomatedTests;
    /**
     * Validate specifications and generated tests
     */
    private validateSpecificationsAndTests;
    /**
     * Calculate overall quality score
     */
    private calculateQualityScore;
    /**
     * Generate comprehensive report
     */
    generatePhase3Report(results: Phase3Result): string;
}
export default Phase3FormalTesting;

// ---- src/self-improvement/phase3-simple.d.ts ----
/**
 * Phase 3: Simplified Formal Specification & Testing Implementation
 */
export declare class Phase3Simple {
    private formalAgent;
    private tddAgent;
    constructor();
    /**
     * Execute simplified Phase 3
     */
    executeSimplePhase3(): Promise<any>;
    /**
     * Generate report
     */
    generateSimpleReport(results: any): string;
}
export default Phase3Simple;

// ---- src/self-improvement/phase3-typescript-fixes.d.ts ----
/**
 * Phase 3: Systematic TypeScript Error Resolution
 *
 * Uses the formal specifications and TDD guidance to systematically
 * resolve TypeScript compilation errors.
 */
export interface TypeScriptFix {
    file: string;
    line: number;
    errorCode: string;
    description: string;
    originalCode: string;
    fixedCode: string;
    confidence: 'high' | 'medium' | 'low';
    riskLevel: 'safe' | 'moderate' | 'risky';
}
export interface Phase3FixResults {
    fixesApplied: TypeScriptFix[];
    errorsRemaining: number;
    errorsFixed: number;
    testsCreated: string[];
    qualityScore: number;
}
export declare class Phase3TypeScriptFixer {
    private appliedFixes;
    /**
     * Execute systematic TypeScript error resolution
     */
    executeSystematicFixes(): Promise<Phase3FixResults>;
    /**
     * Fix Intent Agent undefined array access errors
     */
    private fixIntentAgentUndefinedAccess;
    /**
     * Fix Benchmark Runner type mismatch
     */
    private fixBenchmarkRunnerTypeMismatch;
    /**
     * Check if Enhanced State Manager needs fixing
     */
    private fixEnhancedStateManagerIfNeeded;
    /**
     * Count current TypeScript errors
     */
    private countCurrentErrors;
    /**
     * Calculate quality score based on fixes applied
     */
    private calculateQualityScore;
    /**
     * Generate comprehensive fix report
     */
    generateFixReport(results: Phase3FixResults): string;
}
export default Phase3TypeScriptFixer;

// ---- src/self-improvement/phase4-code-generation.d.ts ----
/**
 * Phase 4: Code Generation & Implementation
 *
 * Uses ae-framework's CodeGenerationAgent to systematically generate
 * fixes for TypeScript compilation errors based on formal specifications
 * and TDD guidance from Phase 3.
 */
export interface Phase4CodeFix {
    file: string;
    errorCode: string;
    errorLine: number;
    errorDescription: string;
    generatedFix: string;
    confidence: number;
    testCoverage: number;
    estimatedImpact: 'low' | 'medium' | 'high';
}
export interface Phase4Results {
    fixes: Phase4CodeFix[];
    errorsResolved: number;
    errorsRemaining: number;
    codeQualityImprovement: number;
    generatedTests: string[];
    overallSuccess: boolean;
}
export declare class Phase4CodeGeneration {
    private codeGenAgent;
    private appliedFixes;
    constructor();
    /**
     * Execute Phase 4: Systematic code generation for TypeScript error resolution
     */
    executePhase4(): Promise<Phase4Results>;
    /**
     * Analyze current TypeScript errors to identify patterns and priorities
     */
    private analyzeCurrentErrors;
    /**
     * Generate systematic fixes using CodeGenerationAgent
     */
    private generateSystematicFixes;
    /**
     * Generate fix for a specific TypeScript error
     */
    private generateFixForError;
    /**
     * Generate specific fix based on error type
     */
    private generateSpecificFix;
    /**
     * Generate null safety fix
     */
    private generateNullSafetyFix;
    /**
     * Generate type compatibility fix
     */
    private generateTypeCompatibilityFix;
    /**
     * Generate object literal fix
     */
    private generateObjectLiteralFix;
    /**
     * Generate undefined check fix
     */
    private generateUndefinedCheckFix;
    /**
     * Generate missing properties fix
     */
    private generateMissingPropertiesFix;
    /**
     * Apply high-confidence fixes
     */
    private applyHighConfidenceFixes;
    /**
     * Verify fixes with tests
     */
    private verifyFixesWithTests;
    /**
     * Get current TypeScript error count
     */
    private getCurrentErrorCount;
    /**
     * Categorize error severity
     */
    private categorizeErrorSeverity;
    /**
     * Estimate impact of fix
     */
    private estimateImpact;
    /**
     * Calculate quality improvement score
     */
    private calculateQualityImprovement;
    /**
     * Generate comprehensive Phase 4 report
     */
    generatePhase4Report(results: Phase4Results): string;
}
export default Phase4CodeGeneration;

// ---- src/self-improvement/phase5-verification-final.d.ts ----
/**
 * Phase 5: Verification & Final Error Resolution
 *
 * Systematic approach to resolving remaining TypeScript errors through
 * targeted manual fixes, comprehensive testing, and quality validation.
 * Final verification of ae-framework self-improvement process.
 */
export interface TypeScriptError {
    file: string;
    line: number;
    column: number;
    code: string;
    message: string;
    severity: 'error' | 'warning';
    category: 'type-safety' | 'interface' | 'import' | 'syntax' | 'other';
}
export interface ErrorFix {
    file: string;
    line: number;
    errorCode: string;
    originalLine: string;
    fixedLine: string;
    explanation: string;
    riskLevel: 'low' | 'medium' | 'high';
    testRequired: boolean;
}
export interface Phase5Results {
    initialErrorCount: number;
    finalErrorCount: number;
    errorsResolved: number;
    appliedFixes: ErrorFix[];
    verificationResults: {
        compilationSuccess: boolean;
        testsPass: boolean;
        qualityMetrics: {
            codeComplexity: number;
            maintainabilityScore: number;
            testCoverage: number;
        };
    };
    overallSuccess: boolean;
    completionTime: number;
}
export declare class Phase5VerificationFinal {
    private appliedFixes;
    private startTime;
    constructor();
    /**
     * Execute Phase 5: Complete verification and final error resolution
     */
    executePhase5(): Promise<Phase5Results>;
    /**
     * Analyze all TypeScript errors in the project
     */
    private analyzeAllErrors;
    /**
     * Categorize errors by type and priority
     */
    private categorizeErrors;
    /**
     * Apply critical fixes for high-priority errors
     */
    private applyCriticalFixes;
    /**
     * Apply systematic fixes by error pattern
     */
    private applySystematicFixes;
    /**
     * Fix undefined access patterns
     */
    private fixUndefinedAccess;
    /**
     * Fix type assignment issues
     */
    private fixTypeAssignment;
    /**
     * Fix interface property errors
     */
    private fixInterfaceProperty;
    /**
     * Fix missing properties errors
     */
    private fixMissingProperties;
    /**
     * Apply a fix to the file
     */
    private applyFix;
    /**
     * Perform final verification
     */
    private performFinalVerification;
    /**
     * Get current error count
     */
    private getCurrentErrorCount;
    /**
     * Categorize error type
     */
    private categorizeErrorType;
    /**
     * Generate comprehensive Phase 5 report
     */
    generatePhase5Report(results: Phase5Results): string;
}
export default Phase5VerificationFinal;

// ---- src/self-improvement/setup-context-manager.d.ts ----
/**
 * Phase 1: ContextManager Setup for Efficient Development
 *
 * This module configures the ContextManager with optimal settings for
 * the self-improvement development process, enabling efficient context
 * management during TypeScript error fixes and codebase improvements.
 */
import { ContextManager, ContextOptions } from '../utils/context-manager.js';
export interface ContextSetupResult {
    success: boolean;
    contextManager: ContextManager;
    initialContext: any;
    optimizedSettings: ContextOptions;
    errors: string[];
    recommendations: string[];
}
export declare class ContextManagerSetup {
    private contextManager;
    private phaseStateManager;
    private projectRoot;
    constructor(projectRoot?: string);
    /**
     * Set up ContextManager with optimal settings for Phase 1 development
     */
    setupForPhase1(): Promise<ContextSetupResult>;
    /**
     * Initialize Phase 1 in the phase state manager
     */
    private initializePhase1;
    /**
     * Set up working memory with TypeScript-specific patterns and solutions
     */
    private setupTypeScriptWorkingMemory;
    /**
     * Add items to working memory through context manager
     */
    private addToWorkingMemory;
    /**
     * Validate the context manager setup
     */
    private validateSetup;
    /**
     * Generate a setup report
     */
    generateSetupReport(result: ContextSetupResult): string;
}
export default ContextManagerSetup;

// ---- src/self-improvement/setup-git-hooks.d.ts ----
/**
 * Git Hooks Setup for ae-framework Self-Improvement
 *
 * This module sets up git hooks to enforce TDD compliance during development
 */
export interface GitHooksSetupConfig {
    projectRoot: string;
    forceOverwrite: boolean;
    enableTDDEnforcement: boolean;
}
export declare class GitHooksSetup {
    private config;
    constructor(config?: Partial<GitHooksSetupConfig>);
    /**
     * Set up git hooks for TDD enforcement
     */
    setupGitHooks(): Promise<{
        success: boolean;
        hooksInstalled: string[];
        message: string;
    }>;
    /**
     * Install pre-commit hook
     */
    private installPreCommitHook;
    /**
     * Install pre-push hook for additional validation
     */
    private installPrePushHook;
    /**
     * Validate git hooks installation
     */
    validateGitHooks(): Promise<{
        preCommitInstalled: boolean;
        prePushInstalled: boolean;
        allHooksWorking: boolean;
        issues: string[];
    }>;
    /**
     * Uninstall git hooks (for cleanup)
     */
    uninstallGitHooks(): Promise<{
        success: boolean;
        hooksRemoved: string[];
        message: string;
    }>;
}
export declare const createGitHooksSetup: (config?: Partial<GitHooksSetupConfig>) => GitHooksSetup;

// ---- src/self-improvement/tdd-setup.d.ts ----
/**
 * TDD Infrastructure Setup for ae-framework Self-Improvement
 *
 * This module configures and initializes the TDD infrastructure using
 * ae-framework's existing components for quality-controlled reimplementation.
 */
import { HybridTDDSystem } from '../integration/hybrid-tdd-system.js';
import { TDDAgent } from '../agents/tdd-agent.js';
import { MetricsCollector } from '../cli/metrics/MetricsCollector.js';
export interface SelfImprovementTDDConfig {
    projectRoot: string;
    configFile: string;
    enableRealTimeMonitoring: boolean;
    strictModeEnforcement: boolean;
    targetCoverage: number;
    metricsOutputPath: string;
}
export declare class SelfImprovementTDDSetup {
    private hybridTDD?;
    private tddAgent?;
    private metricsCollector?;
    private config;
    constructor(config?: Partial<SelfImprovementTDDConfig>);
    /**
     * Initialize TDD infrastructure for self-improvement project
     */
    initializeTDDInfrastructure(): Promise<{
        success: boolean;
        components: {
            hybridTDD: boolean;
            tddAgent: boolean;
            metricsCollector: boolean;
        };
        message: string;
    }>;
    /**
     * Load self-improvement configuration
     */
    private loadSelfImprovementConfig;
    /**
     * Set up HybridTDDSystem for Claude Code integration
     */
    private setupHybridTDDSystem;
    /**
     * Configure TDDAgent for real-time enforcement
     */
    private setupTDDAgent;
    /**
     * Initialize MetricsCollector for progress tracking
     */
    private setupMetricsCollector;
    /**
     * Validate TDD infrastructure is operational
     */
    validateTDDInfrastructure(): Promise<{
        operational: boolean;
        checks: {
            hybridTDDActive: boolean;
            tddAgentReady: boolean;
            metricsCollecting: boolean;
            configValid: boolean;
        };
        recommendations: string[];
    }>;
    /**
     * Get TDD system instance for external use
     */
    getHybridTDDSystem(): HybridTDDSystem | undefined;
    /**
     * Get TDD Agent instance for external use
     */
    getTDDAgent(): TDDAgent | undefined;
    /**
     * Get MetricsCollector instance for external use
     */
    getMetricsCollector(): MetricsCollector | undefined;
    /**
     * Generate initial setup report
     */
    generateSetupReport(): string;
}
export declare const createSelfImprovementTDDSetup: (config?: Partial<SelfImprovementTDDConfig>) => SelfImprovementTDDSetup;

// ---- src/services/approval-service.d.ts ----
/**
 * Approval Service for managing phase approvals in ae-framework
 */
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { EventEmitter } from 'events';
export interface ApprovalRequest {
    phase: PhaseType;
    projectId: string;
    projectName?: string;
    requestedBy: string;
    requestedAt: Date;
    artifacts: string[];
    summary?: string;
    metadata?: Record<string, any>;
}
export interface ApprovalResponse {
    approved: boolean;
    approvedBy: string;
    approvedAt: Date;
    notes?: string;
    conditions?: string[];
}
export interface ApprovalPolicy {
    requireMultipleApprovers?: boolean;
    minApprovers?: number;
    approverRoles?: string[];
    autoApproveConditions?: ApprovalCondition[];
    timeoutHours?: number;
    escalationPath?: string[];
}
export interface ApprovalCondition {
    type: 'test-coverage' | 'code-review' | 'security-scan' | 'custom';
    threshold?: number;
    customCheck?: (artifacts: string[]) => Promise<boolean>;
}
export interface PendingApproval {
    request: ApprovalRequest;
    policy: ApprovalPolicy;
    status: 'pending' | 'approved' | 'rejected' | 'expired';
    responses: ApprovalResponse[];
    createdAt: Date;
    expiresAt?: Date;
}
export declare class ApprovalService extends EventEmitter {
    private phaseStateManager;
    private approvalsDir;
    private pendingApprovals;
    private policies;
    constructor(projectRoot?: string, phaseStateManager?: PhaseStateManager);
    /**
     * Initialize default approval policies
     */
    private initializeDefaultPolicies;
    /**
     * Set custom policy for a phase
     */
    setPolicy(phase: PhaseType, policy: ApprovalPolicy): void;
    /**
     * Request approval for a phase
     */
    requestApproval(phase: PhaseType, requestedBy: string, summary?: string): Promise<ApprovalRequest>;
    /**
     * Approve a phase
     */
    approve(phase: PhaseType, approvedBy: string, notes?: string, conditions?: string[]): Promise<void>;
    /**
     * Reject a phase approval
     */
    reject(phase: PhaseType, rejectedBy: string, reason: string): Promise<void>;
    /**
     * Get pending approvals
     */
    getPendingApprovals(): Promise<PendingApproval[]>;
    /**
     * Get approval history for a phase
     */
    getApprovalHistory(phase: PhaseType): Promise<PendingApproval[]>;
    /**
     * Check auto-approval conditions
     */
    private checkAutoApproval;
    /**
     * Evaluate a single approval condition
     */
    private evaluateCondition;
    /**
     * Check test coverage (placeholder implementation)
     */
    private checkTestCoverage;
    /**
     * Check code review status (placeholder implementation)
     */
    private checkCodeReview;
    /**
     * Check security scan results (placeholder implementation)
     */
    private checkSecurityScan;
    /**
     * Auto-approve a phase
     */
    private autoApprove;
    /**
     * Generate approval ID
     */
    private generateApprovalId;
    /**
     * Save pending approval to disk
     */
    private savePendingApproval;
    /**
     * Remove pending approval from disk
     */
    private removePendingApproval;
    /**
     * Load pending approvals from disk
     */
    private loadPendingApprovals;
    /**
     * Check for expired approvals
     */
    checkExpiredApprovals(): Promise<void>;
    /**
     * Get approval status for a phase
     */
    getApprovalStatus(phase: PhaseType): Promise<{
        required: boolean;
        status: 'not-required' | 'pending' | 'approved' | 'rejected' | 'expired';
        details?: PendingApproval;
    }>;
}

// ---- src/services/container/container-engine.d.ts ----
/**
 * Container Engine Abstraction Layer
 * Phase 3 of Issue #37: Unified interface for Docker and Podman container engines
 */
import { EventEmitter } from 'events';
export type ContainerEngineName = 'docker' | 'podman';
export interface ContainerCapabilities {
    rootless: boolean;
    compose: boolean;
    buildx: boolean;
    systemd: boolean;
    selinux: boolean;
    pods: boolean;
}
export interface ContainerEngineInfo {
    name: ContainerEngineName;
    version: string;
    available: boolean;
    capabilities: ContainerCapabilities;
    executable: string;
    composeCommand?: string;
}
export interface ResourceLimits {
    memory?: string;
    cpus?: string;
    cpuShares?: number;
    diskSpace?: string;
    maxProcesses?: number;
}
export interface VolumeMount {
    source: string;
    target: string;
    readonly?: boolean;
    type?: 'bind' | 'volume' | 'tmpfs';
}
export interface PortMapping {
    containerPort: number;
    hostPort?: number;
    protocol?: 'tcp' | 'udp';
    hostIp?: string;
}
export interface ContainerNetworkConfig {
    mode: 'bridge' | 'host' | 'none' | 'container' | 'custom';
    customNetworkName?: string;
    isolation?: boolean;
}
export interface SecurityContext {
    user?: string;
    group?: string;
    capabilities?: {
        add?: string[];
        drop?: string[];
    };
    seLinuxLabel?: string;
    appArmor?: string;
    seccomp?: string;
    noNewPrivileges?: boolean;
    readOnlyRootFilesystem?: boolean;
}
export interface ContainerConfig {
    name: string;
    image: string;
    tag?: string;
    command?: string[];
    args?: string[];
    environment?: Record<string, string>;
    workingDir?: string;
    volumes?: VolumeMount[];
    ports?: PortMapping[];
    resources?: ResourceLimits;
    network?: ContainerNetworkConfig;
    security?: SecurityContext;
    labels?: Record<string, string>;
    healthCheck?: {
        command: string[];
        interval?: string;
        timeout?: string;
        retries?: number;
        startPeriod?: string;
    };
    restart?: 'no' | 'always' | 'unless-stopped' | 'on-failure';
    autoRemove?: boolean;
    interactive?: boolean;
    tty?: boolean;
    detached?: boolean;
}
export interface ContainerRunOptions {
    timeout?: number;
    capture?: boolean;
    stream?: boolean;
    cleanup?: boolean;
}
export interface ContainerStatus {
    id: string;
    name: string;
    state: 'created' | 'running' | 'paused' | 'restarting' | 'removing' | 'exited' | 'dead';
    status: string;
    image: string;
    ports?: PortMapping[];
    createdAt: Date;
    startedAt?: Date;
    finishedAt?: Date;
    exitCode?: number;
    error?: string;
    health?: 'healthy' | 'unhealthy' | 'starting' | 'none';
}
export interface ContainerLogs {
    stdout: string;
    stderr: string;
    combined: string;
    timestamp: Date;
}
export interface ContainerStats {
    cpu: {
        usage: number;
        systemUsage: number;
    };
    memory: {
        usage: number;
        limit: number;
        percentage: number;
    };
    network: {
        rx: number;
        tx: number;
    };
    io: {
        read: number;
        write: number;
    };
    timestamp: Date;
}
export interface ImageBuildContext {
    contextPath: string;
    dockerfilePath?: string;
    target?: string;
    buildArgs?: Record<string, string>;
    labels?: Record<string, string>;
    platforms?: string[];
    cache?: boolean;
    squash?: boolean;
    pullBaseImage?: boolean;
}
export interface ImageInfo {
    id: string;
    repository: string;
    tag: string;
    digest?: string;
    size: number;
    created: Date;
    labels?: Record<string, string>;
}
/**
 * Abstract base class for container engines
 */
export declare abstract class ContainerEngine extends EventEmitter {
    protected engineInfo: ContainerEngineInfo;
    constructor(engineInfo: ContainerEngineInfo);
    getEngineInfo(): ContainerEngineInfo;
    getName(): ContainerEngineName;
    getVersion(): string;
    isAvailable(): boolean;
    getCapabilities(): ContainerCapabilities;
    abstract checkAvailability(): Promise<boolean>;
    abstract createContainer(config: ContainerConfig): Promise<string>;
    abstract startContainer(containerId: string, options?: ContainerRunOptions): Promise<void>;
    abstract stopContainer(containerId: string, timeout?: number): Promise<void>;
    abstract removeContainer(containerId: string, force?: boolean): Promise<void>;
    abstract restartContainer(containerId: string): Promise<void>;
    abstract runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<{
        containerId: string;
        exitCode: number;
        output: ContainerLogs;
    }>;
    abstract executeInContainer(containerId: string, command: string[], options?: {
        user?: string;
        workingDir?: string;
        environment?: Record<string, string>;
    }): Promise<{
        exitCode: number;
        output: ContainerLogs;
    }>;
    abstract getContainerStatus(containerId: string): Promise<ContainerStatus>;
    abstract listContainers(filters?: Record<string, string>): Promise<ContainerStatus[]>;
    abstract getContainerLogs(containerId: string, options?: {
        tail?: number;
        since?: Date;
        follow?: boolean;
    }): Promise<ContainerLogs | AsyncIterable<string>>;
    abstract getContainerStats(containerId: string): Promise<ContainerStats>;
    abstract buildImage(buildContext: ImageBuildContext, imageTag: string): Promise<string>;
    abstract pullImage(image: string, tag?: string): Promise<void>;
    abstract pushImage(image: string, tag?: string): Promise<void>;
    abstract removeImage(image: string, force?: boolean): Promise<void>;
    abstract listImages(filters?: Record<string, string>): Promise<ImageInfo[]>;
    abstract tagImage(sourceImage: string, targetImage: string): Promise<void>;
    abstract createVolume(name: string, labels?: Record<string, string>): Promise<void>;
    abstract removeVolume(name: string, force?: boolean): Promise<void>;
    abstract listVolumes(): Promise<Array<{
        name: string;
        driver: string;
        mountpoint: string;
        labels?: Record<string, string>;
        size?: number;
    }>>;
    abstract createNetwork(name: string, options?: {
        driver?: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }): Promise<void>;
    abstract removeNetwork(name: string): Promise<void>;
    abstract listNetworks(): Promise<Array<{
        id: string;
        name: string;
        driver: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }>>;
    abstract supportsCompose(): boolean;
    abstract runCompose?(composeFile: string, options?: {
        projectName?: string;
        environment?: Record<string, string>;
        detached?: boolean;
    }): Promise<void>;
    abstract stopCompose?(composeFile: string, projectName?: string): Promise<void>;
    abstract cleanup(options?: {
        containers?: boolean;
        images?: boolean;
        volumes?: boolean;
        networks?: boolean;
        force?: boolean;
    }): Promise<{
        containers: number;
        images: number;
        volumes: number;
        networks: number;
        spaceSaved: number;
    }>;
    protected validateContainerName(name: string): boolean;
    protected buildCommandArgs(config: ContainerConfig): string[];
    protected parseContainerStatus(statusOutput: string): Partial<ContainerStatus>;
    protected formatResourceLimits(resources: ResourceLimits): Record<string, string>;
}
/**
 * Container engine factory
 */
export declare class ContainerEngineFactory {
    private static detectedEngines;
    static detectAvailableEngines(): Promise<ContainerEngineInfo[]>;
    static createEngine(engineName: ContainerEngineName): Promise<ContainerEngine>;
    static createPreferredEngine(): Promise<ContainerEngine>;
    static clearCache(): void;
}

// ---- src/services/container/container-manager.d.ts ----
/**
 * Container Manager - Container Lifecycle Management
 * Phase 3 of Issue #37: Orchestrates container operations across different engines
 */
import { EventEmitter } from 'events';
import { ContainerLogs, type ContainerEngineName } from './container-engine.js';
export interface ContainerManagerConfig {
    preferredEngine?: ContainerEngineName;
    autoCleanup?: boolean;
    maxConcurrentContainers?: number;
    defaultTimeout?: number;
    resourceLimits?: {
        memory?: string;
        cpus?: string;
    };
    securityDefaults?: {
        rootless?: boolean;
        readOnlyRootFilesystem?: boolean;
        noNewPrivileges?: boolean;
    };
}
export interface VerificationEnvironment {
    name: string;
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    baseImage: string;
    resources: {
        memory: string;
        cpus: string;
    };
    volumes: Array<{
        source: string;
        target: string;
        readonly?: boolean;
    }>;
    environment: Record<string, string>;
}
export interface VerificationJob {
    id: string;
    name: string;
    projectPath: string;
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    containerId?: string;
    status: 'pending' | 'running' | 'completed' | 'failed';
    startTime?: Date;
    endTime?: Date;
    results?: any;
    logs?: ContainerLogs;
    error?: string;
}
export interface ContainerHealthCheck {
    containerId: string;
    healthy: boolean;
    lastCheck: Date;
    checks: {
        running: boolean;
        responsive: boolean;
        resourceUsage: {
            cpu: number;
            memory: number;
        };
    };
}
export declare class ContainerManager extends EventEmitter {
    private engine;
    private config;
    private activeJobs;
    private healthChecks;
    private cleanupTimer?;
    private healthCheckTimer?;
    constructor(config?: ContainerManagerConfig);
    /**
     * Initialize the container manager
     */
    initialize(): Promise<void>;
    /**
     * Create a verification environment
     */
    createVerificationEnvironment(env: VerificationEnvironment): Promise<string>;
    /**
     * Run verification job in container
     */
    runVerificationJob(job: Omit<VerificationJob, 'id' | 'status' | 'startTime'>): Promise<VerificationJob>;
    /**
     * Get job status
     */
    getJob(jobId: string): VerificationJob | undefined;
    /**
     * List all jobs
     */
    listJobs(filter?: {
        status?: VerificationJob['status'];
        language?: string;
    }): VerificationJob[];
    /**
     * Cancel a running job
     */
    cancelJob(jobId: string): Promise<void>;
    /**
     * Build verification container image
     */
    buildVerificationImage(language: 'rust' | 'elixir' | 'multi', tools: string[], options?: {
        tag?: string;
        buildArgs?: Record<string, string>;
        push?: boolean;
    }): Promise<string>;
    /**
     * Get container engine information
     */
    getEngineInfo(): import("./container-engine.js").ContainerEngineInfo;
    /**
     * List available container engines
     */
    listAvailableEngines(): Promise<import("./container-engine.js").ContainerEngineInfo[]>;
    /**
     * Get system health status
     */
    getHealthStatus(): Promise<{
        healthy: boolean;
        engine: {
            name: string;
            version: string;
            available: boolean;
        };
        jobs: {
            total: number;
            running: number;
            completed: number;
            failed: number;
        };
        resources: {
            activeContainers: number;
            images: number;
            volumes: number;
        };
    }>;
    /**
     * Cleanup old jobs and containers
     */
    cleanup(options?: {
        maxAge?: number;
        keepCompleted?: number;
        force?: boolean;
    }): Promise<{
        jobsRemoved: number;
        containersRemoved: number;
        spaceSaved: number;
    }>;
    /**
     * Shutdown the container manager
     */
    shutdown(): Promise<void>;
    private setupEngineEventListeners;
    private startBackgroundServices;
    private stopBackgroundServices;
    private getVerificationEnvironment;
    private buildVerificationCommand;
    private buildRustVerificationScript;
    private buildElixirVerificationScript;
    private buildMultiLanguageVerificationScript;
    private parseVerificationResults;
}

// ---- src/services/container/docker-engine.d.ts ----
/**
 * Docker Container Engine Implementation
 * Phase 3 of Issue #37: Docker container engine implementation for comparison with Podman
 */
import { ContainerEngine, ContainerConfig, ContainerRunOptions, ContainerStatus, ContainerLogs, ContainerStats, ImageBuildContext, ImageInfo } from './container-engine.js';
export declare class DockerEngine extends ContainerEngine {
    private dockerPath;
    private composePath?;
    constructor();
    checkAvailability(): Promise<boolean>;
    createContainer(config: ContainerConfig): Promise<string>;
    startContainer(containerId: string, options?: ContainerRunOptions): Promise<void>;
    stopContainer(containerId: string, timeout?: number): Promise<void>;
    removeContainer(containerId: string, force?: boolean): Promise<void>;
    restartContainer(containerId: string): Promise<void>;
    runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<{
        containerId: string;
        exitCode: number;
        output: ContainerLogs;
    }>;
    executeInContainer(containerId: string, command: string[], options?: {
        user?: string;
        workingDir?: string;
        environment?: Record<string, string>;
    }): Promise<{
        exitCode: number;
        output: ContainerLogs;
    }>;
    getContainerStatus(containerId: string): Promise<ContainerStatus>;
    listContainers(filters?: Record<string, string>): Promise<ContainerStatus[]>;
    getContainerLogs(containerId: string, options?: {
        tail?: number;
        since?: Date;
        follow?: boolean;
    }): Promise<ContainerLogs | AsyncIterable<string>>;
    private streamLogs;
    getContainerStats(containerId: string): Promise<ContainerStats>;
    buildImage(buildContext: ImageBuildContext, imageTag: string): Promise<string>;
    pullImage(image: string, tag?: string): Promise<void>;
    pushImage(image: string, tag?: string): Promise<void>;
    removeImage(image: string, force?: boolean): Promise<void>;
    listImages(filters?: Record<string, string>): Promise<ImageInfo[]>;
    tagImage(sourceImage: string, targetImage: string): Promise<void>;
    createVolume(name: string, labels?: Record<string, string>): Promise<void>;
    removeVolume(name: string, force?: boolean): Promise<void>;
    listVolumes(): Promise<Array<{
        name: string;
        driver: string;
        mountpoint: string;
        labels?: Record<string, string>;
        size?: number;
    }>>;
    createNetwork(name: string, options?: {
        driver?: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }): Promise<void>;
    removeNetwork(name: string): Promise<void>;
    listNetworks(): Promise<Array<{
        id: string;
        name: string;
        driver: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }>>;
    supportsCompose(): boolean;
    runCompose(composeFile: string, options?: {
        projectName?: string;
        environment?: Record<string, string>;
        detached?: boolean;
    }): Promise<void>;
    stopCompose(composeFile: string, projectName?: string): Promise<void>;
    cleanup(options?: {
        containers?: boolean;
        images?: boolean;
        volumes?: boolean;
        networks?: boolean;
        force?: boolean;
    }): Promise<{
        containers: number;
        images: number;
        volumes: number;
        networks: number;
        spaceSaved: number;
    }>;
    private mapDockerState;
    private parsePorts;
    private parseSize;
}

// ---- src/services/container/podman-engine.d.ts ----
/**
 * Podman Container Engine Implementation
 * Phase 3 of Issue #37: Podman-specific container engine implementation
 */
import { ContainerEngine, ContainerConfig, ContainerRunOptions, ContainerStatus, ContainerLogs, ContainerStats, ImageBuildContext, ImageInfo } from './container-engine.js';
export declare class PodmanEngine extends ContainerEngine {
    private podmanPath;
    private composePath?;
    constructor();
    checkAvailability(): Promise<boolean>;
    createContainer(config: ContainerConfig): Promise<string>;
    startContainer(containerId: string, options?: ContainerRunOptions): Promise<void>;
    stopContainer(containerId: string, timeout?: number): Promise<void>;
    removeContainer(containerId: string, force?: boolean): Promise<void>;
    restartContainer(containerId: string): Promise<void>;
    runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<{
        containerId: string;
        exitCode: number;
        output: ContainerLogs;
    }>;
    executeInContainer(containerId: string, command: string[], options?: {
        user?: string;
        workingDir?: string;
        environment?: Record<string, string>;
    }): Promise<{
        exitCode: number;
        output: ContainerLogs;
    }>;
    getContainerStatus(containerId: string): Promise<ContainerStatus>;
    listContainers(filters?: Record<string, string>): Promise<ContainerStatus[]>;
    getContainerLogs(containerId: string, options?: {
        tail?: number;
        since?: Date;
        follow?: boolean;
    }): Promise<ContainerLogs | AsyncIterable<string>>;
    private streamLogs;
    getContainerStats(containerId: string): Promise<ContainerStats>;
    buildImage(buildContext: ImageBuildContext, imageTag: string): Promise<string>;
    pullImage(image: string, tag?: string): Promise<void>;
    pushImage(image: string, tag?: string): Promise<void>;
    removeImage(image: string, force?: boolean): Promise<void>;
    listImages(filters?: Record<string, string>): Promise<ImageInfo[]>;
    tagImage(sourceImage: string, targetImage: string): Promise<void>;
    createVolume(name: string, labels?: Record<string, string>): Promise<void>;
    removeVolume(name: string, force?: boolean): Promise<void>;
    listVolumes(): Promise<Array<{
        name: string;
        driver: string;
        mountpoint: string;
        labels?: Record<string, string>;
        size?: number;
    }>>;
    createNetwork(name: string, options?: {
        driver?: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }): Promise<void>;
    removeNetwork(name: string): Promise<void>;
    listNetworks(): Promise<Array<{
        id: string;
        name: string;
        driver: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }>>;
    supportsCompose(): boolean;
    runCompose(composeFile: string, options?: {
        projectName?: string;
        environment?: Record<string, string>;
        detached?: boolean;
    }): Promise<void>;
    stopCompose(composeFile: string, projectName?: string): Promise<void>;
    cleanup(options?: {
        containers?: boolean;
        images?: boolean;
        volumes?: boolean;
        networks?: boolean;
        force?: boolean;
    }): Promise<{
        containers: number;
        images: number;
        volumes: number;
        networks: number;
        spaceSaved: number;
    }>;
    private mapPodmanState;
    private parsePorts;
    private parseSize;
}

// ---- src/services/index.d.ts ----
/**
 * Service modules for ae-framework
 */
export { ApprovalService } from './approval-service.js';
export { PersonaIntegrationService } from './persona-integration.js';
export type { AdaptedCommandBehavior } from './persona-integration.js';

// ---- src/services/mcp-server.d.ts ----
/**
 * MCP Server Extensions for ae-framework
 * Provides extensible server capabilities and plugin architecture
 */
import { EventEmitter } from 'events';
export interface MCPServerConfig {
    name: string;
    version: string;
    description?: string;
    endpoints: MCPEndpoint[];
    middleware?: MCPMiddleware[];
    plugins?: MCPPlugin[];
    capabilities: MCPCapability[];
    authentication?: MCPAuthConfig;
    rateLimit?: MCPRateLimitConfig;
}
export interface MCPEndpoint {
    path: string;
    method: 'GET' | 'POST' | 'PUT' | 'DELETE' | 'PATCH';
    handler: MCPEndpointHandler;
    description?: string;
    parameters?: MCPParameter[];
    response?: MCPResponseSchema;
    authentication?: boolean;
    rateLimit?: number;
}
export interface MCPParameter {
    name: string;
    type: 'string' | 'number' | 'boolean' | 'object' | 'array';
    required: boolean;
    description?: string;
    validation?: MCPValidationRule[];
}
export interface MCPValidationRule {
    type: 'min' | 'max' | 'pattern' | 'enum' | 'custom';
    value: any;
    message?: string;
}
export interface MCPResponseSchema {
    type: 'object' | 'array' | 'string' | 'number' | 'boolean';
    properties?: Record<string, MCPParameter>;
    items?: MCPParameter;
}
export type MCPEndpointHandler = (request: MCPRequest) => Promise<MCPResponse>;
export interface MCPRequest {
    path: string;
    method: string;
    params: Record<string, any>;
    body?: any;
    headers: Record<string, string>;
    user?: MCPUser;
    context: MCPContext;
}
export interface MCPResponse {
    status: number;
    data?: any;
    error?: string;
    headers?: Record<string, string>;
    metadata?: Record<string, any>;
}
export interface MCPContext {
    requestId: string;
    timestamp: number;
    serverName: string;
    version: string;
    environment: 'development' | 'production' | 'testing';
    projectRoot: string;
}
export interface MCPUser {
    id: string;
    name: string;
    roles: string[];
    permissions: string[];
}
export interface MCPMiddleware {
    name: string;
    handler: MCPMiddlewareHandler;
    order?: number;
}
export type MCPMiddlewareHandler = (request: MCPRequest, response: MCPResponse, next: () => Promise<void>) => Promise<void>;
export interface MCPPlugin {
    name: string;
    version: string;
    description?: string;
    initialize: (server: MCPServer) => Promise<void>;
    terminate?: (server: MCPServer) => Promise<void>;
    dependencies?: string[];
    endpoints?: MCPEndpoint[];
    middleware?: MCPMiddleware[];
}
export interface MCPCapability {
    name: string;
    version: string;
    description?: string;
    enabled: boolean;
    configuration?: Record<string, any>;
}
export interface MCPAuthConfig {
    type: 'jwt' | 'apikey' | 'basic' | 'custom';
    configuration: Record<string, any>;
}
export interface MCPRateLimitConfig {
    windowMs: number;
    maxRequests: number;
    skipSuccessfulRequests?: boolean;
    skipFailedRequests?: boolean;
}
export interface MCPServerMetrics {
    requestCount: number;
    errorCount: number;
    averageResponseTime: number;
    uptime: number;
    activeConnections: number;
    pluginsLoaded: number;
    endpointsRegistered: number;
}
export declare class MCPServer extends EventEmitter {
    private config;
    private endpoints;
    private middleware;
    private plugins;
    private capabilities;
    private isRunning;
    private startTime;
    private metrics;
    private totalResponseTime;
    private projectRoot;
    constructor(config: MCPServerConfig, projectRoot: string);
    /**
     * Start the MCP server
     */
    start(): Promise<void>;
    /**
     * Stop the MCP server
     */
    stop(): Promise<void>;
    /**
     * Process an incoming request
     */
    processRequest(request: MCPRequest): Promise<MCPResponse>;
    /**
     * Register a plugin
     */
    registerPlugin(plugin: MCPPlugin): Promise<void>;
    /**
     * Register an endpoint
     */
    registerEndpoint(endpoint: MCPEndpoint): void;
    /**
     * Register middleware
     */
    registerMiddlewareItem(middleware: MCPMiddleware): void;
    /**
     * Get server capabilities
     */
    getCapabilities(): MCPCapability[];
    /**
     * Enable/disable capability
     */
    setCapability(name: string, enabled: boolean): void;
    /**
     * Get server metrics
     */
    getMetrics(): MCPServerMetrics;
    /**
     * Get server status
     */
    getStatus(): {
        running: boolean;
        uptime: number;
        config: MCPServerConfig;
    };
    private setupDefaultCapabilities;
    private loadPlugins;
    private registerMiddleware;
    private registerEndpoints;
    private setupDefaultEndpoints;
    private runMiddleware;
    private validateRequest;
    private validateValue;
}
/**
 * Factory function to create MCP server with Rust verification plugin
 */
export declare function createRustVerificationServer(projectRoot: string): Promise<MCPServer>;

// ---- src/services/persona-integration.d.ts ----
/**
 * Persona Integration Service for ae-framework
 * Integrates Smart Persona System with existing commands
 */
import { PersonaManager, UserPreferences } from '../utils/persona-manager.js';
import type { CommandResult } from '../commands/slash-command-manager.js';
export interface AdaptedCommandBehavior {
    verbosity: UserPreferences['verbosity'];
    includeExplanations: boolean;
    suggestionLevel: 'minimal' | 'moderate' | 'comprehensive';
    evidenceValidation: boolean;
    proactiveSuggestions: string[];
}
export declare class PersonaIntegrationService {
    private personaManager;
    private initialized;
    constructor(projectRoot: string);
    /**
     * Initialize the persona integration service
     */
    initialize(): Promise<void>;
    /**
     * Adapt command behavior based on persona preferences
     */
    adaptCommandBehavior(command: string, context?: any): Promise<AdaptedCommandBehavior>;
    /**
     * Learn from command execution results
     */
    learnFromExecution(command: string, result: CommandResult, context?: any, userFeedback?: 'positive' | 'negative'): Promise<void>;
    /**
     * Apply persona adaptations to command result
     */
    adaptCommandResult(result: CommandResult, command: string, adaptedBehavior: AdaptedCommandBehavior): Promise<CommandResult>;
    /**
     * Get persona-aware validation options
     */
    getValidationOptions(command: string): {
        validate: boolean;
        minConfidence: number;
    };
    /**
     * Get persona-specific command options
     */
    getPersonalizedCommandOptions(command: string): Record<string, any>;
    /**
     * Provide contextual help based on user patterns
     */
    getContextualHelp(command: string, error?: string): string[];
    /**
     * Update user preferences from command usage patterns
     */
    updatePreferencesFromUsage(): Promise<void>;
    /**
     * Get persona manager instance for direct access
     */
    getPersonaManager(): PersonaManager;
    private mapSuggestionBehavior;
    private minimizeMessage;
    private enhanceMessage;
}

// ---- src/services/plugins/index.d.ts ----
/**
 * MCP Server Plugins Index
 * Export all available plugins for the MCP server
 */
export { RustVerificationPlugin } from './rust-verification-plugin.js';
export type { RustVerificationPluginConfig } from './rust-verification-plugin.js';
export type { MCPPlugin, MCPServer, MCPEndpoint, MCPRequest, MCPResponse, MCPContext, MCPParameter, MCPValidationRule } from '../mcp-server.js';

// ---- src/services/plugins/rust-verification-plugin.d.ts ----
/**
 * Rust Verification MCP Plugin
 * Phase 2 of Issue #33: Enhanced Rust formal verification integration
 */
import type { MCPPlugin, MCPServer, MCPEndpoint } from '../mcp-server.js';
export interface RustVerificationPluginConfig {
    enabledTools: string[];
    defaultOptions: {
        timeout: number;
        memoryLimit: number;
        unwindLimit: number;
        strictMode: boolean;
        generateReport: boolean;
    };
    projectDiscovery: {
        autoDetect: boolean;
        searchDepth: number;
    };
}
export declare class RustVerificationPlugin implements MCPPlugin {
    name: string;
    version: string;
    description: string;
    private rustAgent;
    private verifyAgent;
    private config;
    constructor(config?: Partial<RustVerificationPluginConfig>);
    initialize(server: MCPServer): Promise<void>;
    terminate(server: MCPServer): Promise<void>;
    get endpoints(): MCPEndpoint[];
    private verifyRustProject;
    private getAvailableTools;
    private discoverRustProjects;
    private analyzeRustCode;
    private discoverSourceFiles;
    private generateVerificationSummary;
    private generateRecommendations;
    private getToolDescription;
    private findRustProjects;
    private performCodeAnalysis;
    private generateAnalysisRecommendations;
}

// ---- src/services/service-registry.d.ts ----
/**
 * @fileoverview Service Registry Implementation
 * Phase 3: Services & Integration - Service registry for unified management
 * Manages registration and lifecycle of all services
 */
import { ServiceConfig, ServiceType, ServiceState, ServiceRegistryInterface } from './service-types.js';
/**
 * Centralized service registry for the unified service layer
 */
export declare class ServiceRegistry implements ServiceRegistryInterface {
    private services;
    private serviceStates;
    private dependencyGraph;
    constructor();
    /**
     * Register a new service in the registry
     */
    registerService(config: ServiceConfig): Promise<boolean>;
    /**
     * Unregister a service from the registry
     */
    unregisterService(id: string): Promise<boolean>;
    /**
     * Get service configuration by ID
     */
    getService(id: string): Promise<ServiceConfig | undefined>;
    /**
     * Get all registered services
     */
    getAllServices(): Promise<ServiceConfig[]>;
    /**
     * Get services by type
     */
    getServicesByType(type: ServiceType): Promise<ServiceConfig[]>;
    /**
     * Get total number of registered services
     */
    getServiceCount(): number;
    /**
     * Get all unique service types
     */
    getServiceTypes(): ServiceType[];
    /**
     * Get service state
     */
    getServiceState(id: string): ServiceState | undefined;
    /**
     * Update service state
     */
    updateServiceState(id: string, updates: Partial<ServiceState>): boolean;
    /**
     * Get services that depend on the given service
     */
    getDependents(serviceId: string): string[];
    /**
     * Get dependencies of a service
     */
    getDependencies(serviceId: string): string[];
    /**
     * Check if service is registered
     */
    isServiceRegistered(id: string): boolean;
    /**
     * Get services in dependency order (topological sort)
     */
    getServicesInDependencyOrder(): string[];
    /**
     * Validate service registry integrity
     */
    validateRegistry(): Array<{
        issue: string;
        severity: 'error' | 'warning';
    }>;
    /**
     * Clear all services (for testing)
     */
    clear(): void;
    /**
     * Update dependency graph for a service
     */
    private updateDependencyGraph;
}

// ---- src/services/service-types.d.ts ----
/**
 * @fileoverview Service Layer Domain Types
 * Phase 3: Services & Integration - Service layer type definitions
 * Core domain types for unified service layer architecture
 */
/**
 * Service types supported by the unified service layer
 */
export declare enum ServiceType {
    APPROVAL = "approval",
    CONTAINER = "container",
    MCP = "mcp",
    PERSONA = "persona",
    OPTIMIZATION = "optimization",
    INTEGRATION = "integration",
    MONITORING = "monitoring"
}
/**
 * Service configuration structure
 */
export interface ServiceConfig {
    id: string;
    type: ServiceType;
    config: Record<string, any>;
    dependencies: string[];
    enabled?: boolean;
    timeout?: number;
}
/**
 * Service task specification
 */
export interface ServiceTaskSpecification {
    requirements: string;
    acceptance: string[];
    context: Record<string, any>;
}
/**
 * Service task definition
 */
export interface ServiceTask {
    id: string;
    type: ServiceType;
    specification: ServiceTaskSpecification;
    metadata: {
        priority: number;
        estimatedDuration: number;
        dependencies?: string[];
        deadline?: Date;
    };
}
/**
 * Service execution result
 */
export interface ServiceResult {
    success: boolean;
    taskId: string;
    serviceId?: string;
    artifacts: string[];
    performanceMetrics?: {
        responseTime: number;
        memoryOptimized: boolean;
        throughput: number;
        cacheHitRate?: number;
    };
    approvalResult?: {
        approved: boolean;
        approver?: string;
        timestamp: Date;
        reason?: string;
    };
    containerResult?: {
        containerId: string;
        status: string;
        exitCode?: number;
        logs?: string[];
    };
    mcpResult?: {
        toolsAvailable: number;
        resourcesAvailable: number;
        connectionStatus: string;
        capabilities: string[];
    };
    dependenciesAffected?: string[];
    errors?: string[];
}
/**
 * Service state management
 */
export interface ServiceState {
    id: string;
    status: 'registered' | 'starting' | 'running' | 'stopping' | 'stopped' | 'error';
    startedAt?: Date;
    stoppedAt?: Date;
    errorMessage?: string;
    healthStatus: 'healthy' | 'unhealthy' | 'unknown';
}
/**
 * Service registry interface
 */
export interface ServiceRegistryInterface {
    registerService(config: ServiceConfig): Promise<boolean>;
    unregisterService(id: string): Promise<boolean>;
    getService(id: string): Promise<ServiceConfig | undefined>;
    getAllServices(): Promise<ServiceConfig[]>;
    getServicesByType(type: ServiceType): Promise<ServiceConfig[]>;
    getServiceCount(): number;
    getServiceTypes(): ServiceType[];
}
/**
 * Performance metrics tracking
 */
export interface PerformanceMetrics {
    averageResponseTime: number;
    memoryUsage: number;
    throughput: number;
    errorRate: number;
    uptime: number;
}
/**
 * Coverage metrics for validation
 */
export interface CoverageMetrics {
    lineCoverage: number;
    branchCoverage: number;
    functionCoverage: number;
    statementCoverage: number;
}
/**
 * Service layer validation result
 */
export interface ServiceLayerValidation {
    serviceLayerOptimized: boolean;
    performanceImproved: boolean;
    typeScriptCompliant: boolean;
    errorCount: number;
    coverageThresholdMet: boolean;
    validationDetails: Array<{
        check: string;
        passed: boolean;
        message: string;
        value?: any;
    }>;
}
/**
 * Optimization configuration
 */
export interface OptimizationConfig {
    caching: boolean;
    connectionPooling: boolean;
    requestBatching: boolean;
    compressionEnabled?: boolean;
    timeoutOptimization?: boolean;
}
/**
 * Service lifecycle management
 */
export interface ServiceLifecycleResult {
    success: boolean;
    serviceId: string;
    action: 'start' | 'stop' | 'restart' | 'health-check';
    timestamp: Date;
    duration: number;
    dependenciesAffected?: string[];
    message?: string;
}

// ---- src/services/unified-service-manager.d.ts ----
/**
 * @fileoverview Unified Service Manager Implementation
 * Phase 3: Services & Integration - Core service management
 * Unified manager for all service types with optimization and validation
 */
import { ServiceConfig, ServiceTask, ServiceResult, ServiceLifecycleResult, PerformanceMetrics, CoverageMetrics, ServiceLayerValidation, OptimizationConfig } from './service-types.js';
import { ServiceRegistry } from './service-registry.js';
/**
 * Unified service manager implementing service layer optimization
 */
export declare class UnifiedServiceManager {
    private registry;
    private initialized;
    private optimizationConfig;
    private performanceBaseline?;
    private taskExecutionCount;
    private totalExecutionTime;
    constructor(registry?: ServiceRegistry);
    /**
     * Initialize the service manager
     */
    initialize(): Promise<void>;
    /**
     * Shutdown the service manager
     */
    shutdown(): Promise<void>;
    /**
     * Register a service
     */
    registerService(config: ServiceConfig): Promise<boolean>;
    /**
     * Get a service by ID
     */
    getService(id: string): Promise<ServiceConfig | undefined>;
    /**
     * Start a service and its dependencies
     */
    startService(serviceId: string): Promise<ServiceLifecycleResult>;
    /**
     * Stop a service
     */
    stopService(serviceId: string): Promise<ServiceLifecycleResult>;
    /**
     * Execute a service task
     */
    executeTask(task: ServiceTask): Promise<ServiceResult>;
    /**
     * Enable performance optimizations
     */
    enableOptimizations(config: OptimizationConfig): Promise<void>;
    /**
     * Get performance baseline
     */
    getPerformanceBaseline(): Promise<PerformanceMetrics>;
    /**
     * Get current performance metrics
     */
    getCurrentPerformance(): Promise<PerformanceMetrics>;
    /**
     * Get coverage metrics
     */
    getCoverageMetrics(): Promise<CoverageMetrics>;
    /**
     * Validate service layer
     */
    validateServiceLayer(): Promise<ServiceLayerValidation>;
    /**
     * Check if service is registered
     */
    isServiceRegistered(id: string): boolean;
    /**
     * Unregister service
     */
    unregisterService(id: string): Promise<boolean>;
    /**
     * Get registry instance
     */
    getRegistry(): ServiceRegistry;
    /**
     * Route task to appropriate service handler
     */
    private routeTaskToService;
    /**
     * Handle approval service tasks
     */
    private handleApprovalTask;
    /**
     * Handle container service tasks
     */
    private handleContainerTask;
    /**
     * Handle MCP service tasks
     */
    private handleMcpTask;
    /**
     * Handle optimization tasks
     */
    private handleOptimizationTask;
    /**
     * Handle generic tasks
     */
    private handleGenericTask;
    /**
     * Perform service-specific startup
     */
    private performServiceStartup;
    /**
     * Perform service-specific shutdown
     */
    private performServiceShutdown;
    /**
     * Measure current performance
     */
    private measureCurrentPerformance;
    /**
     * Calculate current throughput
     */
    private calculateThroughput;
    /**
     * Check if performance has improved
     */
    private hasPerformanceImprovement;
}

// ---- src/telemetry/enhanced-telemetry.d.ts ----
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

// ---- src/telemetry/phase6-metrics.d.ts ----
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

// ---- src/telemetry/runtime-guards.d.ts ----
/**
 * Runtime Guards with OpenTelemetry Integration
 * Implements comprehensive request/response validation with telemetry tracking
 */
import { z } from 'zod';
import { FastifyRequest, FastifyReply } from 'fastify';
export declare enum ViolationType {
    SCHEMA_VALIDATION = "schema_validation",
    RATE_LIMIT = "rate_limit",
    AUTHORIZATION = "authorization",
    BUSINESS_RULE = "business_rule",
    DATA_INTEGRITY = "data_integrity",
    TIMEOUT = "timeout"
}
export declare enum ViolationSeverity {
    LOW = "low",
    MEDIUM = "medium",
    HIGH = "high",
    CRITICAL = "critical"
}
export interface ContractViolation {
    id: string;
    type: ViolationType;
    severity: ViolationSeverity;
    message: string;
    timestamp: Date;
    requestId?: string;
    endpoint?: string;
    details?: Record<string, any>;
}
export interface ValidationResult {
    valid: boolean;
    data?: any;
    violations: ContractViolation[];
}
export declare class RuntimeGuard {
    private tracer;
    private violations;
    /**
     * Validate request payload against Zod schema
     */
    validateRequest<T>(schema: z.ZodSchema<T>, data: unknown, context?: {
        requestId?: string;
        endpoint?: string;
        operation?: string;
    }): ValidationResult;
    /**
     * Validate response data against Zod schema
     */
    validateResponse<T>(schema: z.ZodSchema<T>, data: unknown, context?: {
        requestId?: string;
        endpoint?: string;
        statusCode?: number;
    }): ValidationResult;
    /**
     * Record business rule violation
     */
    recordBusinessRuleViolation(rule: string, message: string, severity?: ViolationSeverity, details?: Record<string, any>): ContractViolation;
    /**
     * Record rate limit violation
     */
    recordRateLimitViolation(endpoint: string, limit: number, current: number, windowMs: number, requestId?: string): ContractViolation;
    /**
     * Create Fastify middleware for request validation
     */
    createRequestValidator<T>(schema: z.ZodSchema<T>): (request: FastifyRequest, reply: FastifyReply) => Promise<never>;
    /**
     * Create Fastify middleware for response validation
     */
    createResponseValidator<T>(schema: z.ZodSchema<T>): (request: FastifyRequest, reply: FastifyReply, payload: any) => Promise<any>;
    /**
     * Get all violations within a time window
     */
    getViolations(since?: Date): ContractViolation[];
    /**
     * Get violation statistics
     */
    getViolationStats(): {
        total: number;
        byType: Record<ViolationType, number>;
        bySeverity: Record<ViolationSeverity, number>;
        last24Hours: number;
    };
    /**
     * Clear old violations (cleanup)
     */
    clearOldViolations(olderThan: Date): number;
    private createValidationViolation;
    private recordViolation;
}
export declare const runtimeGuard: RuntimeGuard;
export declare const CommonSchemas: {
    readonly HealthResponse: z.ZodObject<{
        status: z.ZodLiteral<"healthy">;
        timestamp: z.ZodString;
        service: z.ZodString;
    }, "strip", z.ZodTypeAny, {
        status?: "healthy";
        timestamp?: string;
        service?: string;
    }, {
        status?: "healthy";
        timestamp?: string;
        service?: string;
    }>;
    readonly ErrorResponse: z.ZodObject<{
        error: z.ZodString;
        message: z.ZodOptional<z.ZodString>;
        details: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodAny>>;
    }, "strip", z.ZodTypeAny, {
        message?: string;
        error?: string;
        details?: Record<string, any>;
    }, {
        message?: string;
        error?: string;
        details?: Record<string, any>;
    }>;
    readonly ReservationRequest: z.ZodObject<{
        orderId: z.ZodString;
        itemId: z.ZodString;
        quantity: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        orderId?: string;
        itemId?: string;
        quantity?: number;
    }, {
        orderId?: string;
        itemId?: string;
        quantity?: number;
    }>;
    readonly ReservationResponse: z.ZodObject<{
        ok: z.ZodBoolean;
        reservationId: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        ok?: boolean;
        reservationId?: string;
    }, {
        ok?: boolean;
        reservationId?: string;
    }>;
};

// ---- src/telemetry/telemetry-service.d.ts ----
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

// ---- src/telemetry/telemetry-setup.d.ts ----
import { NodeSDK } from '@opentelemetry/sdk-node';
export declare const telemetrySDK: NodeSDK;
export declare function initializeTelemetry(): void;
export declare function shutdownTelemetry(): Promise<void>;

// ---- src/testing/fc-assert.d.ts ----
import fc from 'fast-check';
export declare function aeAssert<T>(prop: fc.IProperty<T>, opts?: Partial<fc.Parameters<T>>): void;
export declare function aeAssertRepro<T>(name: string, prop: fc.IProperty<T>, opts?: Partial<fc.Parameters<T>>): void;

// ---- src/testing/intelligent-test-selection.d.ts ----
/**
 * Intelligent Test Selection System for Phase 3.2
 * AI-driven test selection with risk analysis and optimization
 */
import { EventEmitter } from 'events';
import type { SequentialInferenceEngine } from '../engines/sequential-inference-engine.js';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';
export interface CodeChange {
    id: string;
    type: 'addition' | 'modification' | 'deletion';
    filePath: string;
    componentId: string;
    impact: 'low' | 'medium' | 'high';
    changeType: 'logic' | 'config' | 'interface' | 'test' | 'feature';
    linesChanged: number;
    additions: number;
    deletions: number;
    riskScore: number;
    description: string;
}
export interface TestCase {
    id: string;
    name: string;
    type: 'unit' | 'integration' | 'e2e';
    filePath: string;
    componentCoverage: string[];
    priority: 'critical' | 'high' | 'medium' | 'low';
    executionTime: number;
    lastRun: Date;
    successRate: number;
    tags: string[];
}
export interface TestSuite {
    id: string;
    name: string;
    type: 'unit' | 'integration' | 'e2e';
    tests: TestCase[];
}
export interface TestInventory {
    id: string;
    timestamp: Date;
    totalTests: number;
    testSuites: TestSuite[];
    coverage: {
        overall: number;
        byComponent: Record<string, number>;
        byTestType: Record<string, number>;
    };
    metrics: {
        avgExecutionTime: number;
        flakyTests: number;
        recentFailures: number;
    };
}
export interface TestSelectionRequest {
    id: string;
    changes: CodeChange[];
    testInventory: TestInventory;
    dependencyAnalysis: DependencyAnalysisResult;
    constraints: {
        maxExecutionTime: number;
        maxTests: number;
        minCoverage: number;
        budgetLimits: {
            timePerTest: number;
            totalBudget: number;
        };
    };
    strategy: 'risk_based' | 'coverage_optimized' | 'balanced' | 'ml_optimized';
    preferences: {
        prioritizeRecentChanges: boolean;
        includeFlakyTests: boolean;
        parallelExecution: boolean;
        regressionFocus: boolean;
    };
}
export interface SelectedTestSuite {
    id: string;
    name: string;
    tests: TestCase[];
    totalTests: number;
    estimatedExecutionTime: number;
    coverageProjection: number;
}
export interface SelectionReasoning {
    strategy: string;
    factors: Array<{
        name: string;
        weight: number;
        description: string;
        impact: 'high' | 'medium' | 'low';
    }>;
    tradeoffs: Array<{
        decision: string;
        rationale: string;
        alternativeConsidered: string;
    }>;
    confidence: number;
}
export interface TestSelectionResult {
    requestId: string;
    selectedTests: SelectedTestSuite;
    reasoning: SelectionReasoning;
    optimization: {
        parallelizationGains: number;
        recommendations: string[];
        potentialSavings: number;
    };
    recommendations: string[];
}
export interface CoverageAnalysisResult {
    overallCoverage: number;
    componentCoverage: Record<string, number>;
    riskCoverage: Record<string, number>;
    gaps: Array<{
        type: 'component' | 'path' | 'scenario';
        severity: 'high' | 'medium' | 'low';
        description: string;
        impact: string;
    }>;
    recommendations: Array<{
        type: string;
        priority: 'high' | 'medium' | 'low';
        description: string;
        effort: 'high' | 'medium' | 'low';
        impact: string;
    }>;
    projectedCoverage: Record<string, number>;
}
export interface ExecutionTimePrediction {
    estimatedTime: number;
    confidence: number;
    breakdown: {
        sequential: number;
        parallel: number;
        overhead: number;
    };
    factors: Array<{
        name: string;
        impact: number;
        description: string;
    }>;
    optimization: {
        parallelizationGains: number;
        recommendations: string[];
        potentialSavings: number;
    };
}
export interface IntelligentTestSelectionConfig {
    riskThreshold: number;
    maxTestsPerComponent: number;
    enableMLPrediction: boolean;
    cacheEnabled: boolean;
    parallelExecutionEnabled: boolean;
}
/**
 * Main Intelligent Test Selection class that orchestrates the entire system
 */
export declare class IntelligentTestSelection extends EventEmitter {
    private changeAnalyzer;
    private riskAssessor;
    private selectionEngine;
    private coverageAnalyzer;
    private timePredictor;
    private inferenceEngine;
    private config;
    constructor(inferenceEngine: SequentialInferenceEngine, config?: Partial<IntelligentTestSelectionConfig>);
    selectTests(request: TestSelectionRequest): Promise<TestSelectionResult>;
    analyzeCoverage(changes: CodeChange[], testInventory: TestInventory): Promise<CoverageAnalysisResult>;
    predictExecutionTime(tests: SelectedTestSuite): ExecutionTimePrediction;
    private enhanceWithInferenceEngine;
    private applyMLInsights;
    private calculateCoverageProjection;
    private generateRecommendations;
}

// ---- src/testing/playwright-integration.d.ts ----
/**
 * Playwright Integration System for Phase 3.2
 * Provides E2E test automation and intelligent test generation
 */
import { EventEmitter } from 'events';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';
import type { SequentialInferenceEngine } from '../engines/sequential-inference-engine.js';
export interface PlaywrightConfig {
    baseURL: string;
    browserType: 'chromium' | 'firefox' | 'webkit';
    headless: boolean;
    viewport: {
        width: number;
        height: number;
    };
    timeout: number;
    retries: number;
    outputDir: string;
    screenshotMode: 'only-on-failure' | 'off' | 'on';
    videoMode: 'retain-on-failure' | 'off' | 'on';
}
export interface E2ETestCase {
    id: string;
    name: string;
    description: string;
    priority: 'critical' | 'high' | 'medium' | 'low';
    tags: string[];
    steps: TestStep[];
    expectedOutcome: string;
    preconditions: string[];
    testData: Record<string, any>;
    dependencies: string[];
}
export interface TestStep {
    id: string;
    action: TestAction;
    selector?: string;
    value?: string;
    options?: Record<string, any>;
    description: string;
    timeout?: number;
    retry?: boolean;
}
export type TestAction = 'navigate' | 'click' | 'fill' | 'select' | 'wait' | 'assert' | 'screenshot' | 'hover' | 'keyboard' | 'upload' | 'download';
export interface TestGenerationRequest {
    id: string;
    sourceAnalysis: DependencyAnalysisResult;
    targetComponents: string[];
    testTypes: E2ETestType[];
    userFlows: UserFlow[];
    coverage: {
        minCoverage: number;
        includeEdgeCases: boolean;
        includeCriticalPaths: boolean;
    };
    constraints: {
        maxTests: number;
        maxDuration: number;
        browser: PlaywrightConfig['browserType'][];
    };
}
export type E2ETestType = 'smoke' | 'regression' | 'user_journey' | 'integration' | 'critical_path' | 'edge_case';
export interface UserFlow {
    id: string;
    name: string;
    description: string;
    steps: UserFlowStep[];
    priority: 'critical' | 'high' | 'medium' | 'low';
    frequency: 'daily' | 'weekly' | 'monthly' | 'rare';
}
export interface UserFlowStep {
    action: string;
    target: string;
    data?: any;
    expectedResult: string;
}
export interface TestGenerationResult {
    requestId: string;
    generatedTests: E2ETestCase[];
    testSuite: {
        name: string;
        description: string;
        estimatedDuration: number;
        coverage: TestCoverage;
    };
    playwrightConfig: PlaywrightConfig;
    executionPlan: TestExecutionPlan;
    recommendations: TestRecommendation[];
}
export interface TestCoverage {
    componentCoverage: number;
    userFlowCoverage: number;
    criticalPathCoverage: number;
    edgeCaseCoverage: number;
    riskCoverage: {
        high: number;
        medium: number;
        low: number;
    };
}
export interface TestExecutionPlan {
    phases: TestPhase[];
    totalEstimatedTime: number;
    parallelization: {
        maxParallel: number;
        grouping: 'by_component' | 'by_priority' | 'by_dependency';
    };
    retryStrategy: {
        maxRetries: number;
        retryOnFailure: boolean;
        flakyTestHandling: 'retry' | 'skip' | 'quarantine';
    };
}
export interface TestPhase {
    id: string;
    name: string;
    tests: string[];
    dependencies: string[];
    estimatedDuration: number;
    canRunInParallel: boolean;
}
export interface TestRecommendation {
    id: string;
    type: 'performance' | 'coverage' | 'maintenance' | 'optimization';
    priority: 'high' | 'medium' | 'low';
    title: string;
    description: string;
    impact: string;
    effort: 'low' | 'medium' | 'high';
    implementation: string[];
}
export interface TestExecutionResult {
    executionId: string;
    testResults: TestResult[];
    summary: ExecutionSummary;
    failures: TestFailure[];
    performance: PerformanceMetrics;
    artifacts: TestArtifact[];
}
export interface TestResult {
    testId: string;
    status: 'passed' | 'failed' | 'skipped' | 'flaky';
    duration: number;
    browser: string;
    attempts: number;
    error?: string;
    screenshots: string[];
    videos: string[];
    traces: string[];
}
export interface ExecutionSummary {
    total: number;
    passed: number;
    failed: number;
    skipped: number;
    flaky: number;
    duration: number;
    successRate: number;
}
export interface TestFailure {
    testId: string;
    step: string;
    error: string;
    screenshot?: string;
    stackTrace: string;
    reproducible: boolean;
    category: 'environment' | 'flaky' | 'regression' | 'data' | 'timing';
}
export interface PerformanceMetrics {
    avgTestDuration: number;
    slowestTests: Array<{
        testId: string;
        duration: number;
    }>;
    browserPerformance: Record<string, number>;
    memoryUsage: number;
    parallelEfficiency: number;
}
export interface TestArtifact {
    type: 'screenshot' | 'video' | 'trace' | 'report' | 'log';
    path: string;
    testId: string;
    timestamp: Date;
    size: number;
}
export declare class PlaywrightIntegration extends EventEmitter {
    private inferenceEngine;
    private config;
    private activeExecutions;
    private testCache;
    constructor(inferenceEngine: SequentialInferenceEngine, config?: Partial<PlaywrightConfig>);
    /**
     * Generate E2E tests based on dependency analysis and user flows
     */
    generateE2ETests(request: TestGenerationRequest): Promise<TestGenerationResult>;
    /**
     * Execute generated E2E tests
     */
    executeTests(tests: E2ETestCase[], config?: Partial<PlaywrightConfig>): Promise<TestExecutionResult>;
    /**
     * Analyze test coverage based on dependency analysis
     */
    analyzeTestCoverage(tests: E2ETestCase[], dependencyAnalysis: DependencyAnalysisResult): Promise<TestCoverage>;
    /**
     * Generate test recommendations based on analysis
     */
    generateTestRecommendations(tests: E2ETestCase[], dependencyAnalysis: DependencyAnalysisResult, executionPlan: TestExecutionPlan): TestRecommendation[];
    private createDefaultConfig;
    private setupEventHandlers;
    private generateTestsFromAnalysis;
    private createComponentTest;
    private createUserFlowTest;
    private createCircularDependencyTest;
    private createTestSuite;
    private optimizePlaywrightConfig;
    private createExecutionPlan;
    private executeIndividualTest;
    private extractComponentFromSelector;
    private calculateUserFlowCoverage;
    private calculateCriticalPathCoverage;
    private calculateEdgeCaseCoverage;
    private calculateRiskCoverage;
    private calculatePerformanceMetrics;
    private getComponentURL;
    private getComponentSelector;
    private mapFlowActionToTestAction;
    private generateSelectorFromTarget;
    private estimatePhaseTime;
}

// ---- src/testing/properties.d.ts ----
import fc from 'fast-check';
export declare const arbEmail: fc.Arbitrary<string>;
export declare function multiset<T>(arr: T[]): Map<T, number>;
export declare function expectMultisetEqual<T>(a: T[], b: T[]): void;

// ---- src/testing/visual-regression.d.ts ----
/**
 * Visual Regression Testing System for Phase 3.2
 * Provides automated visual testing and change detection
 */
import { EventEmitter } from 'events';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';
import type { PlaywrightConfig } from './playwright-integration.js';
export interface VisualTestConfig {
    threshold: number;
    includeText: boolean;
    ignoreRegions: IgnoreRegion[];
    browsers: string[];
    viewports: Viewport[];
    waitConditions: WaitCondition[];
}
export interface Viewport {
    name: string;
    width: number;
    height: number;
    deviceScaleFactor?: number;
}
export interface IgnoreRegion {
    name: string;
    selector: string;
    reason: string;
}
export interface WaitCondition {
    type: 'selector' | 'networkidle' | 'timeout' | 'custom';
    value: string | number;
    description: string;
}
export interface VisualTestCase {
    id: string;
    name: string;
    description: string;
    url: string;
    selector?: string;
    config: VisualTestConfig;
    baseline: string;
    priority: 'critical' | 'high' | 'medium' | 'low';
    tags: string[];
    dependencies: string[];
}
export interface VisualTestRequest {
    id: string;
    sourceAnalysis: DependencyAnalysisResult;
    testTargets: VisualTestTarget[];
    config: Partial<VisualTestConfig>;
    baselineMode: 'create' | 'update' | 'compare';
    scope: {
        includeComponents: boolean;
        includePages: boolean;
        includeCriticalPaths: boolean;
    };
}
export interface VisualTestTarget {
    type: 'page' | 'component' | 'flow';
    identifier: string;
    url: string;
    selector?: string;
    state?: ComponentState;
}
export interface ComponentState {
    props?: Record<string, any>;
    interactions?: StateInteraction[];
    dataState?: Record<string, any>;
}
export interface StateInteraction {
    action: 'hover' | 'focus' | 'click' | 'fill';
    selector: string;
    value?: string;
    description: string;
}
export interface VisualTestResult {
    testId: string;
    status: 'passed' | 'failed' | 'baseline_created' | 'baseline_updated';
    comparison: VisualComparison;
    browser: string;
    viewport: Viewport;
    artifacts: VisualArtifact[];
    executionTime: number;
}
export interface VisualComparison {
    pixelDifference: number;
    percentageDifference: number;
    threshold: number;
    passed: boolean;
    regions: DifferenceRegion[];
}
export interface DifferenceRegion {
    x: number;
    y: number;
    width: number;
    height: number;
    severity: 'low' | 'medium' | 'high';
    description: string;
}
export interface VisualArtifact {
    type: 'baseline' | 'actual' | 'diff' | 'annotated';
    path: string;
    description: string;
    metadata: {
        width: number;
        height: number;
        format: string;
        size: number;
    };
}
export interface VisualTestSuite {
    id: string;
    name: string;
    description: string;
    tests: VisualTestCase[];
    config: VisualTestConfig;
    baseline: {
        version: string;
        timestamp: Date;
        commit?: string;
        branch?: string;
    };
}
export interface VisualRegressionReport {
    suiteId: string;
    executionId: string;
    timestamp: Date;
    summary: {
        total: number;
        passed: number;
        failed: number;
        newBaselines: number;
        updatedBaselines: number;
    };
    results: VisualTestResult[];
    analysis: VisualAnalysis;
    recommendations: VisualRecommendation[];
}
export interface VisualAnalysis {
    changePatterns: ChangePattern[];
    impactAssessment: VisualImpactAssessment;
    riskFactors: VisualRiskFactor[];
    trends: VisualTrend[];
}
export interface ChangePattern {
    type: 'layout' | 'color' | 'typography' | 'content' | 'animation';
    frequency: number;
    affectedComponents: string[];
    severity: 'low' | 'medium' | 'high';
    description: string;
}
export interface VisualImpactAssessment {
    overallImpact: 'minimal' | 'moderate' | 'significant' | 'major';
    userExperienceImpact: number;
    affectedUserFlows: string[];
    businessImpact: string;
    technicalImpact: string;
}
export interface VisualRiskFactor {
    id: string;
    type: 'layout_shift' | 'color_contrast' | 'text_readability' | 'interactive_element';
    severity: 'low' | 'medium' | 'high' | 'critical';
    description: string;
    affectedTests: string[];
    mitigation: string;
}
export interface VisualTrend {
    metric: 'difference_rate' | 'test_duration' | 'false_positives';
    direction: 'increasing' | 'decreasing' | 'stable';
    change: number;
    timeframe: string;
    significance: 'low' | 'medium' | 'high';
}
export interface VisualRecommendation {
    id: string;
    type: 'threshold' | 'coverage' | 'maintenance' | 'optimization';
    priority: 'high' | 'medium' | 'low';
    title: string;
    description: string;
    impact: string;
    effort: 'low' | 'medium' | 'high';
    implementation: string[];
}
export declare class VisualRegressionTesting extends EventEmitter {
    private config;
    private activeTests;
    private baselines;
    private testHistory;
    constructor(config?: Partial<VisualTestConfig>);
    /**
     * Generate visual tests from dependency analysis
     */
    generateVisualTests(request: VisualTestRequest): Promise<VisualTestSuite>;
    /**
     * Execute visual regression tests
     */
    executeVisualTests(testSuite: VisualTestSuite, playwrightConfig: PlaywrightConfig): Promise<VisualRegressionReport>;
    /**
     * Create or update baseline images
     */
    manageBaselines(testSuite: VisualTestSuite, mode: 'create' | 'update' | 'selective'): Promise<{
        created: number;
        updated: number;
        skipped: number;
    }>;
    /**
     * Analyze visual changes and their impact
     */
    analyzeVisualChanges(results: VisualTestResult[], dependencyAnalysis: DependencyAnalysisResult): VisualImpactAssessment;
    private createDefaultConfig;
    private setupEventHandlers;
    private generateComponentVisualTests;
    private generatePageVisualTests;
    private generateCriticalPathVisualTests;
    private executeVisualTest;
    private simulateScreenshot;
    private simulateVisualComparison;
    private analyzeVisualResults;
    private identifyChangePatterns;
    private identifyVisualRiskFactors;
    private calculateVisualTrends;
    private generateVisualRecommendations;
    private calculateSummary;
    private createBaseline;
    private updateBaseline;
    private shouldUpdateBaseline;
    private identifyCriticalPaths;
    private identifyAffectedUserFlows;
    private assessBusinessImpact;
    private assessTechnicalImpact;
    private extractComponentName;
    private getComponentURL;
}

// ---- src/types/llm.d.ts ----
export interface LLM {
    name: string;
    complete(input: {
        system?: string;
        prompt: string;
        temperature?: number;
    }): Promise<string>;
}

// ---- src/utils/circuit-breaker.d.ts ----
import { EventEmitter } from 'events';
/**
 * Circuit Breaker States
 */
export declare enum CircuitState {
    CLOSED = "CLOSED",// Normal operation
    OPEN = "OPEN",// Failing fast, rejecting calls
    HALF_OPEN = "HALF_OPEN"
}
/**
 * Circuit Breaker Configuration Options
 */
export interface CircuitBreakerOptions {
    /** Failure threshold to open circuit (default: 5) */
    failureThreshold: number;
    /** Success threshold to close circuit from half-open (default: 3) */
    successThreshold: number;
    /** Timeout before attempting to half-open (ms, default: 60000) */
    timeout: number;
    /** Monitor window for failures (ms, default: 60000) */
    monitoringWindow: number;
    /** Expected error types that should trigger circuit breaking */
    expectedErrors?: Array<new (...args: any[]) => Error>;
    /** Fallback function when circuit is open */
    fallback?: (...args: any[]) => any;
    /** Enable detailed monitoring and metrics */
    enableMonitoring?: boolean;
}
/**
 * Circuit Breaker Statistics
 */
export interface CircuitBreakerStats {
    state: CircuitState;
    failureCount: number;
    successCount: number;
    lastFailureTime: number | null;
    lastSuccessTime: number | null;
    totalRequests: number;
    totalFailures: number;
    totalSuccesses: number;
    circuitOpenCount: number;
    averageResponseTime: number;
    uptime: number;
}
/**
 * Circuit Breaker Error
 */
export declare class CircuitBreakerOpenError extends Error {
    constructor(message: string);
}
/**
 * Circuit Breaker Implementation with Auto-Recovery
 */
export declare class CircuitBreaker extends EventEmitter {
    private name;
    private options;
    private state;
    private failureCount;
    private successCount;
    private lastFailureTime;
    private lastSuccessTime;
    private nextAttempt;
    private totalRequests;
    private totalFailures;
    private totalSuccesses;
    private circuitOpenCount;
    private readonly startTime;
    private responseTimes;
    private requestHistory;
    private halfOpenTimer?;
    constructor(name: string, options: CircuitBreakerOptions);
    /**
     * Execute a function with circuit breaker protection
     */
    execute<T>(operation: () => Promise<T>, ...args: any[]): Promise<T>;
    /**
     * Handle successful operation
     */
    private onSuccess;
    /**
     * Handle failed operation
     */
    private onFailure;
    /**
     * Transition to OPEN state
     */
    private transitionToOpen;
    /**
     * Transition to HALF_OPEN state
     */
    private transitionToHalfOpen;
    /**
     * Transition to CLOSED state
     */
    private transitionToClosed;
    /**
     * Clean up old request history
     */
    private cleanupOldHistory;
    /**
     * Get current circuit breaker statistics
     */
    getStats(): CircuitBreakerStats;
    /**
     * Get current circuit state
     */
    getState(): CircuitState;
    /**
     * Get circuit name
     */
    getName(): string;
    /**
     * Force circuit to open (for testing or manual intervention)
     */
    forceOpen(): void;
    /**
     * Force circuit to close (for testing or manual intervention)
     */
    forceClose(): void;
    /**
     * Reset circuit breaker to initial state
     */
    reset(): void;
    /**
     * Check if circuit breaker is in a healthy state
     */
    isHealthy(): boolean;
    /**
     * Cleanup resources
     */
    destroy(): void;
}
export default CircuitBreaker;

// ---- src/utils/context-manager.d.ts ----
/**
 * Context Manager for ae-framework
 * Manages context window and optimizes information flow to AI agents
 */
import { PhaseType } from './phase-state-manager.js';
export interface ContextWindow {
    steering: string;
    phaseInfo: string;
    workingMemory: string;
    relevantFiles: string;
    totalTokens: number;
}
export interface ContextOptions {
    maxTokens?: number;
    includeHistory?: boolean;
    includeArtifacts?: boolean;
    focusPhase?: PhaseType;
    relevantKeywords?: string[];
}
export declare class ContextManager {
    private tokenOptimizer;
    private steeringLoader;
    private phaseStateManager;
    private workingMemory;
    private readonly DEFAULT_MAX_TOKENS;
    private readonly STEERING_TOKEN_BUDGET;
    private readonly PHASE_TOKEN_BUDGET;
    private readonly TOKEN_ESTIMATE_RATIO;
    private readonly FILES_TOKEN_BUDGET;
    constructor(projectRoot?: string);
    /**
     * Build optimized context for current phase
     */
    buildContext(options?: ContextOptions): Promise<ContextWindow>;
    /**
     * Build steering context with compression
     */
    private buildSteeringContext;
    /**
     * Build phase-specific context
     */
    private buildPhaseContext;
    /**
     * Build working memory context
     */
    private buildWorkingMemory;
    /**
     * Build relevant files context
     */
    private buildRelevantFiles;
    /**
     * Find relevant files based on phase and keywords
     */
    private findRelevantFiles;
    /**
     * Scan directory for files
     */
    private scanDirectory;
    /**
     * Compress file content based on type
     */
    private compressFileContent;
    /**
     * Get steering document priority based on phase
     */
    private getSteeringPriority;
    /**
     * Allocate token budget across context components
     */
    private allocateTokenBudget;
    /**
     * Add item to working memory
     */
    addToMemory(key: string, value: any): void;
    /**
     * Clear working memory
     */
    clearMemory(): void;
    /**
     * Get memory item
     */
    getFromMemory(key: string): any;
    /**
     * Estimate token count - delegates to TokenOptimizer for consistency
     */
    private estimateTokens;
    /**
     * Truncate text to token limit
     */
    private truncateToTokens;
    /**
     * Get context statistics
     */
    getContextStats(options?: ContextOptions): Promise<{
        components: Record<string, number>;
        total: number;
        compressionRatio: number;
    }>;
}

// ---- src/utils/enhanced-state-manager.d.ts ----
import { EventEmitter } from 'events';
/**
 * Minimal AEIR stub type for build fix.
 * TODO: Replace with import from '@ae-framework/spec-compiler' when available.
 */
export interface AEIR {
    id?: string;
    name?: string;
    type?: string;
    version?: string;
}
/**
 * Enhanced State Storage Entry with versioning and metadata
 */
export interface StateEntry<T = any> {
    id: string;
    logicalKey: string;
    timestamp: string;
    version: number;
    checksum: string;
    data: T;
    compressed: boolean;
    tags: Record<string, string>;
    ttl?: number;
    metadata: {
        size: number;
        created: string;
        accessed: string;
        source: string;
        phase?: string;
    };
}
/**
 * Storage options for enhanced state management
 */
export interface StorageOptions {
    databasePath?: string;
    enableCompression?: boolean;
    compressionThreshold?: number;
    defaultTTL?: number;
    gcInterval?: number;
    maxVersions?: number;
    enableTransactions?: boolean;
}
/**
 * Failure artifact information for CEGIS integration
 */
export interface FailureArtifact {
    id: string;
    timestamp: string;
    phase: string;
    type: 'validation' | 'compilation' | 'test' | 'verification' | 'generation';
    error: Error;
    context: Record<string, any>;
    artifacts: string[];
    retryable: boolean;
    severity: 'low' | 'medium' | 'high' | 'critical';
}
/**
 * Snapshot metadata for compressed storage
 */
export interface SnapshotMetadata {
    id: string;
    timestamp: string;
    phase: string;
    entities: string[];
    checksum: string;
    compressed: boolean;
    size: number;
    ttl?: number;
}
/**
 * Enhanced State Manager with SQLite-like storage, compression, and EventBus integration
 */
export declare class EnhancedStateManager extends EventEmitter {
    private storage;
    private keyIndex;
    private versionIndex;
    private ttlIndex;
    private activeTransactions;
    private gcTimer?;
    private isInitialized;
    private readonly options;
    private readonly dataDir;
    private readonly databaseFile;
    constructor(projectRoot?: string, options?: StorageOptions);
    /**
     * Initialize the enhanced state manager
     */
    initialize(): Promise<void>;
    /**
     * Save Single Source of Truth (SSOT) data with versioning
     */
    saveSSOT(logicalKey: string, data: AEIR, options?: {
        phase?: string;
        tags?: Record<string, string>;
        ttl?: number;
        source?: string;
        transactionId?: string;
    }): Promise<string>;
    /**
     * Load SSOT data by logical key (latest version by default)
     */
    loadSSOT(logicalKey: string, version?: number): Promise<AEIR | null>;
    /**
     * Create compressed snapshot of current state
     */
    createSnapshot(phase: string, entities?: string[]): Promise<string>;
    /**
     * Load snapshot by ID
     */
    loadSnapshot(snapshotId: string): Promise<Record<string, StateEntry> | null>;
    /**
     * Persist failure artifact and notify EventBus for CEGIS integration
     */
    persistFailureArtifact(artifact: FailureArtifact): Promise<void>;
    /**
     * Begin transaction for atomic operations
     */
    beginTransaction(): Promise<string>;
    /**
     * Commit transaction
     */
    commitTransaction(txId: string): Promise<void>;
    /**
     * Rollback transaction
     */
    rollbackTransaction(txId: string): Promise<void>;
    /**
     * Get all versions of a logical key
     */
    getVersions(logicalKey: string): Promise<Array<{
        version: number;
        timestamp: string;
        key: string;
    }>>;
    /**
     * Cleanup old versions beyond maxVersions limit
     */
    private cleanupOldVersions;
    /**
     * Start garbage collection process
     */
    private startGarbageCollection;
    /**
     * Run garbage collection to remove expired entries
     */
    private runGarbageCollection;
    /**
     * Stop garbage collection
     */
    stopGarbageCollection(): void;
    /**
     * Get storage statistics
     */
    getStatistics(): {
        totalEntries: number;
        totalSize: number;
        compressedEntries: number;
        logicalKeys: number;
        averageVersions: number;
        oldestEntry: string | null;
        newestEntry: string | null;
        activeTransactions: number;
    };
    /**
     * Export state for backup or migration
     */
    exportState(): Promise<{
        metadata: {
            version: string;
            timestamp: string;
            options: StorageOptions;
        };
        entries: StateEntry[];
        indices: {
            keyIndex: Record<string, string[]>;
            versionIndex: Record<string, number>;
        };
    }>;
    /**
     * Import state from backup or migration
     */
    importState(exportedState: Awaited<ReturnType<typeof this.exportState>>): Promise<void>;
    private ensureInitialized;
    private getNextVersion;
    private findLatestKey;
    private findKeyByVersion;
    private updateIndices;
    private shouldCompress;
    private compress;
    private decompress;
    private calculateChecksum;
    private saveEntry;
    private saveInTransaction;
    private loadFromPersistence;
    private persistToDisk;
    /**
     * Cleanup and shutdown
     */
    shutdown(): Promise<void>;
}

// ---- src/utils/evidence-validator.d.ts ----
/**
 * Evidence Validator for ae-framework
 * Validates AI suggestions with evidence from documentation and code
 */
export interface ValidationResult {
    isValid: boolean;
    evidence: Evidence[];
    confidence: number;
    suggestions?: string[];
}
export interface Evidence {
    type: 'documentation' | 'code' | 'test' | 'standard' | 'pattern';
    source: string;
    content: string;
    relevance: number;
    location?: {
        file?: string;
        line?: number;
        url?: string;
    };
}
export interface ValidationOptions {
    requireDocumentation?: boolean;
    requireTests?: boolean;
    minConfidence?: number;
    searchDepth?: number;
    includeExternalDocs?: boolean;
}
export declare class EvidenceValidator {
    private documentationCache;
    private patternDatabase;
    private readonly DEFAULT_MIN_CONFIDENCE;
    constructor();
    /**
     * Validate a claim or suggestion with evidence
     */
    validateClaim(claim: string, context: string, options?: ValidationOptions): Promise<ValidationResult>;
    /**
     * Validate code implementation against specifications
     */
    validateImplementation(code: string, specification: string): Promise<ValidationResult>;
    /**
     * Search official documentation for evidence
     */
    private searchOfficialDocs;
    /**
     * Find evidence in codebase
     */
    private findCodeEvidence;
    /**
     * Check test results for evidence
     */
    private checkTestResults;
    /**
     * Check against known patterns
     */
    private checkPatterns;
    /**
     * Check against coding standards
     */
    private checkStandards;
    /**
     * Calculate confidence score based on evidence
     */
    private calculateConfidence;
    /**
     * Check if evidence meets requirements
     */
    private meetsRequirements;
    /**
     * Generate suggestions when confidence is low
     */
    private generateSuggestions;
    /**
     * Sort evidence by relevance
     */
    private sortEvidenceByRelevance;
    /**
     * Extract keywords from claim
     */
    private extractKeywords;
    /**
     * Search local documentation
     */
    private searchLocalDocs;
    /**
     * Search package documentation
     */
    private searchPackageDocs;
    /**
     * Search codebase for patterns
     */
    private searchCodebase;
    /**
     * Find usage patterns in code
     */
    private findUsagePatterns;
    /**
     * Find test files
     */
    private findTestFiles;
    /**
     * Extract relevant tests from test file
     */
    private extractRelevantTests;
    /**
     * Run tests and get results
     */
    private runTests;
    /**
     * Find project standards file
     */
    private findStandardsFile;
    /**
     * Extract relevant standards
     */
    private extractRelevantStandards;
    /**
     * Check against common coding standards
     */
    private checkCommonStandards;
    /**
     * Match code against specification
     */
    private matchSpecification;
    /**
     * Validate against required patterns
     */
    private validatePatterns;
    /**
     * Detect anti-patterns in code
     */
    private detectAntiPatterns;
    /**
     * Check if claim matches a pattern
     */
    private matchesPattern;
    /**
     * Find keyword matches in content
     */
    private findKeywordMatches;
    /**
     * Scan directory for files
     */
    private scanDirectory;
    /**
     * Initialize pattern database with common patterns
     */
    private initializePatternDatabase;
    /**
     * Validate a solution with evidence
     */
    validateSolution(problem: string, solution: string, options?: ValidationOptions): Promise<ValidationResult>;
    /**
     * Get evidence summary
     */
    getEvidenceSummary(evidence: Evidence[]): string;
}

// ---- src/utils/index.d.ts ----
/**
 * Utility modules for ae-framework
 */
export { PhaseStateManager } from './phase-state-manager.js';
export { SteeringLoader } from './steering-loader.js';
export { EvidenceValidator } from './evidence-validator.js';
export { TokenOptimizer } from './token-optimizer.js';
export { ContextManager } from './context-manager.js';
export { PersonaManager } from './persona-manager.js';
export type { UserPreferences, WorkingContext, PersonaProfile, AdaptationRule, LearningData } from './persona-manager.js';

// ---- src/utils/installer-manager.d.ts ----
/**
 * Integrated Installer Manager for ae-framework
 * Manages project setup, dependency installation, and configuration
 */
export interface InstallationTemplate {
    id: string;
    name: string;
    description: string;
    category: 'web' | 'api' | 'cli' | 'library' | 'fullstack' | 'mobile';
    framework?: string;
    language: 'typescript' | 'javascript' | 'python' | 'rust' | 'go' | 'java' | 'elixir';
    dependencies: Dependency[];
    devDependencies?: Dependency[];
    scripts: Record<string, string>;
    files: TemplateFile[];
    configurations: Configuration[];
    postInstallSteps?: InstallStep[];
}
export interface Dependency {
    name: string;
    version?: string;
    optional?: boolean;
    condition?: string;
    alternatives?: string[];
}
export interface TemplateFile {
    path: string;
    content: string | (() => string);
    overwrite?: boolean;
    condition?: string;
}
export interface Configuration {
    file: string;
    format: 'json' | 'yaml' | 'env' | 'ini' | 'js' | 'ts' | 'elixir';
    content: Record<string, any> | string;
    merge?: boolean;
}
export interface InstallStep {
    type: 'command' | 'file' | 'config' | 'message';
    description: string;
    action: string | (() => Promise<void>);
    condition?: string;
    required?: boolean;
}
export interface InstallationContext {
    projectRoot: string;
    projectName: string;
    packageManager: 'npm' | 'yarn' | 'pnpm';
    nodeVersion?: string;
    existingPackageJson?: any;
    userPreferences?: Record<string, any>;
}
export interface InstallationResult {
    success: boolean;
    message: string;
    installedDependencies: string[];
    createdFiles: string[];
    configuredFiles: string[];
    executedSteps: string[];
    warnings: string[];
    errors: string[];
    duration: number;
}
export declare class InstallerManager {
    private templates;
    private projectRoot;
    constructor(projectRoot: string);
    /**
     * Get available installation templates
     */
    getAvailableTemplates(): InstallationTemplate[];
    /**
     * Get templates by category
     */
    getTemplatesByCategory(category: InstallationTemplate['category']): InstallationTemplate[];
    /**
     * Get template by ID
     */
    getTemplate(id: string): InstallationTemplate | undefined;
    /**
     * Install a template
     */
    installTemplate(templateId: string, context?: Partial<InstallationContext>): Promise<InstallationResult>;
    /**
     * Detect project type and suggest templates
     */
    suggestTemplates(): Promise<{
        suggestions: string[];
        reasoning: string[];
    }>;
    /**
     * Create a custom template
     */
    createCustomTemplate(template: InstallationTemplate): Promise<void>;
    /**
     * Update package manager detection
     */
    detectPackageManager(): Promise<'npm' | 'yarn' | 'pnpm'>;
    private loadDefaultTemplates;
    private prepareContext;
    private installDependencies;
    private createTemplateFiles;
    private applyConfigurations;
    private executePostInstallSteps;
    private ensurePackageJson;
    private updatePackageJsonScripts;
    private runPackageManagerCommand;
    private runCommand;
    private fileExists;
    private getProjectFiles;
    private saveCustomTemplate;
}

// ---- src/utils/mcp-plugin-manager.d.ts ----
/**
 * MCP Plugin Manager for ae-framework
 * Manages loading, registration, and lifecycle of MCP plugins
 */
import { MCPPlugin, MCPServer } from '../services/mcp-server.js';
export interface PluginManifest {
    name: string;
    version: string;
    description?: string;
    main: string;
    dependencies?: string[];
    mcpDependencies?: string[];
    author?: string;
    license?: string;
    keywords?: string[];
    repository?: string;
    homepage?: string;
    engines?: {
        node?: string;
        'ae-framework'?: string;
    };
}
export interface PluginRegistration {
    manifest: PluginManifest;
    plugin: MCPPlugin;
    filePath: string;
    loadedAt: number;
    enabled: boolean;
}
export interface PluginLoadResult {
    success: boolean;
    plugin?: PluginRegistration;
    error?: string;
    warnings?: string[];
}
export interface PluginDiscoveryOptions {
    searchPaths: string[];
    includeDevPlugins: boolean;
    skipValidation: boolean;
}
export declare class MCPPluginManager {
    private plugins;
    private pluginPaths;
    private projectRoot;
    private server?;
    constructor(projectRoot: string, pluginPaths?: string[]);
    /**
     * Set the MCP server instance for plugin registration
     */
    setServer(server: MCPServer): void;
    /**
     * Discover all available plugins
     */
    discoverPlugins(options?: Partial<PluginDiscoveryOptions>): Promise<PluginManifest[]>;
    /**
     * Load a plugin from its manifest
     */
    loadPlugin(manifest: PluginManifest, filePath: string): Promise<PluginLoadResult>;
    /**
     * Load plugins from directory
     */
    loadPluginsFromDirectory(directoryPath: string): Promise<PluginLoadResult[]>;
    /**
     * Enable a plugin
     */
    enablePlugin(name: string): Promise<boolean>;
    /**
     * Disable a plugin
     */
    disablePlugin(name: string): Promise<boolean>;
    /**
     * Unload a plugin
     */
    unloadPlugin(name: string): Promise<boolean>;
    /**
     * Get all loaded plugins
     */
    getLoadedPlugins(): PluginRegistration[];
    /**
     * Get plugin by name
     */
    getPlugin(name: string): PluginRegistration | undefined;
    /**
     * Get enabled plugins
     */
    getEnabledPlugins(): PluginRegistration[];
    /**
     * Create a new plugin template
     */
    createPluginTemplate(name: string, targetDir: string): Promise<void>;
    private scanPluginDirectory;
    private validateManifest;
    private loadPluginModule;
}

// ---- src/utils/persona-manager.d.ts ----
/**
 * Smart Persona Manager for ae-framework
 * Adapts AI behavior based on user patterns and preferences
 */
export interface UserPreferences {
    verbosity: 'minimal' | 'normal' | 'detailed';
    codeStyle: 'functional' | 'object-oriented' | 'mixed';
    explanationLevel: 'beginner' | 'intermediate' | 'expert';
    preferredLanguages: string[];
    preferredFrameworks: string[];
    testingPreference: 'unit' | 'integration' | 'e2e' | 'all';
    suggestionFrequency: 'low' | 'medium' | 'high';
    autoValidation: boolean;
    evidenceRequirement: 'low' | 'medium' | 'high';
}
export interface WorkingContext {
    currentProject: string;
    recentCommands: string[];
    frequentPatterns: string[];
    timeOfDay: 'morning' | 'afternoon' | 'evening' | 'night';
    workSession: {
        startTime: string;
        commandCount: number;
        errorCount: number;
        successRate: number;
    };
}
export interface PersonaProfile {
    id: string;
    name: string;
    description: string;
    preferences: UserPreferences;
    adaptationRules: AdaptationRule[];
    learningData: LearningData;
}
export interface AdaptationRule {
    trigger: {
        context?: Partial<WorkingContext>;
        command?: string;
        pattern?: RegExp;
    };
    adaptation: {
        verbosity?: UserPreferences['verbosity'];
        suggestionBehavior?: 'proactive' | 'reactive' | 'minimal';
        evidenceLevel?: 'strict' | 'normal' | 'relaxed';
    };
    confidence: number;
}
export interface LearningData {
    commandUsage: Record<string, number>;
    successPatterns: string[];
    errorPatterns: string[];
    timePreferences: Record<string, number>;
    lastUpdated: string;
}
export declare class PersonaManager {
    private profilePath;
    private currentProfile;
    private workingContext;
    private interactionCount;
    private saveThreshold;
    constructor(projectRoot: string);
    /**
     * Initialize or load user persona profile
     */
    initialize(): Promise<PersonaProfile>;
    /**
     * Get current persona profile
     */
    getCurrentProfile(): PersonaProfile | null;
    /**
     * Update working context with new command execution
     */
    updateContext(command: string, success: boolean): void;
    /**
     * Learn from user interactions and adapt preferences
     */
    learnFromInteraction(command: string, context: any, feedback?: 'positive' | 'negative'): Promise<void>;
    /**
     * Get adapted behavior based on current context and learned patterns
     */
    getAdaptedBehavior(command: string, context?: any): {
        verbosity: UserPreferences['verbosity'];
        suggestionBehavior: 'proactive' | 'reactive' | 'minimal';
        evidenceLevel: 'strict' | 'normal' | 'relaxed';
        recommendations: string[];
    };
    /**
     * Get personalized command suggestions based on context and history
     */
    getPersonalizedSuggestions(currentCommand?: string): string[];
    /**
     * Update user preferences based on explicit feedback
     */
    updatePreferences(updates: Partial<UserPreferences>): Promise<void>;
    /**
     * Export persona data for backup or migration
     */
    exportPersonaData(): Promise<string>;
    /**
     * Import persona data from backup
     */
    importPersonaData(data: string): Promise<void>;
    private initializeWorkingContext;
    private profileExists;
    private loadProfile;
    private saveProfile;
    private createDefaultProfile;
    private createEmergencyProfile;
    private updateFrequentPatterns;
    private extractPattern;
    private extractCommandPattern;
    private getTimeSlot;
    private matchesRule;
    private getContextValue;
    private compareContextValues;
    private reducedVerbosity;
    private getDefaultBehavior;
    private inferInitialLanguagePreferences;
    /**
     * Update language preferences based on actual command usage patterns
     */
    private updateLanguagePreferencesFromUsage;
    private extractLanguageHints;
}

// ---- src/utils/phase-state-manager.d.ts ----
/**
 * Phase status for tracking completion and approval
 */
export interface PhaseStatus {
    completed: boolean;
    approved: boolean;
    startedAt?: Date;
    completedAt?: Date;
    approvedAt?: Date;
    approvedBy?: string;
    artifacts: string[];
    notes?: string;
}
/**
 * Project phase state
 */
export interface PhaseState {
    projectId: string;
    projectName?: string;
    createdAt: Date;
    updatedAt: Date;
    currentPhase: PhaseType;
    phaseStatus: {
        intent: PhaseStatus;
        formal: PhaseStatus;
        test: PhaseStatus;
        code: PhaseStatus;
        verify: PhaseStatus;
        operate: PhaseStatus;
    };
    approvalsRequired: boolean;
    metadata?: Record<string, any>;
}
/**
 * Phase types in ae-framework
 */
export type PhaseType = 'intent' | 'formal' | 'test' | 'code' | 'verify' | 'operate';
/**
 * PhaseStateManager manages the state of project phases
 */
export declare class PhaseStateManager {
    private stateFilePath;
    private state;
    constructor(projectRoot?: string);
    /**
     * Initialize a new project state
     */
    initializeProject(projectName?: string, approvalsRequired?: boolean): Promise<PhaseState>;
    /**
     * Load existing project state
     */
    loadState(): Promise<PhaseState | null>;
    /**
     * Save state to file
     */
    private saveState;
    /**
     * Get current state
     */
    getCurrentState(): Promise<PhaseState | null>;
    /**
     * Start a phase
     */
    startPhase(phase: PhaseType): Promise<void>;
    /**
     * Complete a phase
     */
    completePhase(phase: PhaseType, artifacts: string[]): Promise<void>;
    /**
     * Approve a phase
     */
    approvePhase(phase: PhaseType, approvedBy: string, notes?: string): Promise<void>;
    /**
     * Check if can transition to next phase
     */
    canTransitionToNextPhase(): Promise<boolean>;
    /**
     * Transition to next phase
     */
    transitionToNextPhase(): Promise<PhaseType | null>;
    /**
     * Get next phase
     */
    getNextPhase(currentPhase: PhaseType): PhaseType | null;
    /**
     * Get phase progress percentage
     */
    getProgressPercentage(): Promise<number>;
    /**
     * Get phase timeline
     */
    getPhaseTimeline(): Promise<Array<{
        phase: PhaseType;
        startedAt?: Date;
        completedAt?: Date;
        duration?: number;
        status: 'pending' | 'in-progress' | 'completed' | 'approved';
    }>>;
    /**
     * Add metadata to state
     */
    addMetadata(key: string, value: any): Promise<void>;
    /**
     * Get artifacts for a phase
     */
    getPhaseArtifacts(phase: PhaseType): Promise<string[]>;
    /**
     * Generate status report
     */
    generateStatusReport(): Promise<string>;
    /**
     * Reset phase (for testing or rollback)
     */
    resetPhase(phase: PhaseType): Promise<void>;
    /**
     * Create empty phase status
     */
    private createEmptyPhaseStatus;
    /**
     * Check if project exists
     */
    hasProject(): Promise<boolean>;
}

// ---- src/utils/quality-policy-loader.d.ts ----
/**
 * Quality Policy Configuration Types
 */
export interface QualityThresholds {
    lines?: number;
    functions?: number;
    branches?: number;
    statements?: number;
    critical?: number;
    serious?: number;
    moderate?: number;
    minor?: number;
    total_warnings?: number;
    errors?: number;
    warnings?: number;
    performance?: number;
    accessibility?: number;
    bestPractices?: number;
    seo?: number;
    pwa?: string;
    pixelDifference?: number;
    failureThreshold?: number;
    uiViolations?: number;
    designSystemViolations?: number;
    accessibilityViolations?: number;
    mutationScore?: number;
    survived?: number;
    testToCodeRatio?: number;
    redGreenCycleCompliance?: number;
    high?: number;
    low?: number;
}
export interface QualityGate {
    description: string;
    enforcement: 'strict' | 'warn' | 'off';
    thresholds: QualityThresholds;
    tools: string[];
    phases: string[];
    enabledFromPhase?: string;
    excludePatterns?: string[];
    config?: Record<string, any>;
    targetPaths?: string[];
}
export interface QualityPolicy {
    $schema?: string;
    $id?: string;
    title: string;
    description: string;
    version: string;
    lastUpdated: string;
    quality: Record<string, QualityGate>;
    environments: Record<string, {
        description: string;
        overrides: Record<string, any>;
    }>;
    reporting: {
        outputDirectory: string;
        formats: string[];
        retention: {
            days: number;
            artifacts: string[];
        };
    };
    notifications: {
        onFailure: Record<string, any>;
        onThresholdChange: {
            requireApproval: boolean;
            reviewers: string[];
        };
    };
}
/**
 * Get the current quality profile from environment variable or parameter
 * @param environment - Optional environment override
 * @returns Profile name ('development', 'ci', 'production')
 */
export declare const getQualityProfile: (environment?: string) => string;
/**
 * Loads the centralized quality policy configuration
 * @param environment - Optional environment to apply overrides ('development', 'ci', 'production')
 * @returns Parsed quality policy with environment overrides applied
 */
export declare const loadQualityPolicy: (environment?: string) => QualityPolicy;
/**
 * Get quality gate configuration for a specific gate type
 * @param gateType - The type of quality gate (e.g., 'accessibility', 'coverage', 'lighthouse')
 * @param environment - Optional environment for overrides
 * @returns Quality gate configuration
 */
export declare const getQualityGate: (gateType: string, environment?: string) => QualityGate;
/**
 * Check if a quality gate should be enforced for the current phase
 * @param gateType - The type of quality gate
 * @param currentPhase - Current development phase
 * @param environment - Optional environment for overrides
 * @returns True if the gate should be enforced
 */
export declare const shouldEnforceGate: (gateType: string, currentPhase: string, environment?: string) => boolean;
/**
 * Get threshold value for a specific quality gate and metric
 * @param gateType - The type of quality gate
 * @param metric - The specific metric name
 * @param environment - Optional environment for overrides
 * @returns The threshold value
 */
export declare const getThreshold: (gateType: string, metric: string, environment?: string) => number | string | undefined;
/**
 * Generate command line arguments for threshold-based tools
 * @param gateType - The type of quality gate
 * @param environment - Optional environment for overrides
 * @returns Array of command line arguments
 */
export declare const getThresholdArgs: (gateType: string, environment?: string) => string[];
/**
 * Validate quality gate results against policy thresholds
 * @param gateType - The type of quality gate
 * @param results - The results to validate
 * @param environment - Optional environment for overrides
 * @returns Validation result with pass/fail status and messages
 */
export declare const validateQualityResults: (gateType: string, results: Record<string, number>, environment?: string) => {
    passed: boolean;
    failures: string[];
    warnings: string[];
};
/**
 * Get current development phase from project state
 * @returns Current phase identifier
 */
export declare const getCurrentPhase: () => string;
/**
 * Export main function for backward compatibility and CLI usage
 */
export default loadQualityPolicy;

// ---- src/utils/steering-loader.d.ts ----
/**
 * SteeringLoader provides utilities for loading and managing steering documents
 */
export declare class SteeringLoader {
    private steeringPath;
    private cache;
    constructor(projectRoot?: string);
    /**
     * Load a specific steering document
     */
    loadDocument(documentName: string): Promise<string | null>;
    /**
     * Load all core steering documents
     */
    loadCoreDocuments(): Promise<Record<string, string>>;
    /**
     * Load custom steering documents (those starting with 'custom-')
     */
    loadCustomDocuments(): Promise<Record<string, string>>;
    /**
     * Load all steering documents (core + custom)
     */
    loadAllDocuments(): Promise<Record<string, string>>;
    /**
     * Get steering context as a formatted string for AI agents
     */
    getSteeringContext(): Promise<string>;
    /**
     * Check if steering documents exist
     */
    hasSteeringDocuments(): Promise<boolean>;
    /**
     * Initialize default steering documents if they don't exist
     */
    initializeDefaults(): Promise<void>;
    /**
     * Clear the document cache
     */
    clearCache(): void;
}

// ---- src/utils/token-optimizer.d.ts ----
/**
 * Token Optimizer for ae-framework
 * Reduces token usage by up to 70% through intelligent compression and caching
 */
export interface CompressionOptions {
    maxTokens?: number;
    preservePriority?: string[];
    compressionLevel?: 'low' | 'medium' | 'high';
    enableCaching?: boolean;
}
export interface TokenStats {
    original: number;
    compressed: number;
    reductionPercentage: number;
}
export declare class TokenOptimizer {
    private cache;
    private readonly CACHE_SIZE;
    private readonly TOKEN_ESTIMATE_RATIO;
    private readonly KEY_INDICATOR_REGEX;
    /**
     * Compress steering documents by removing redundancy and focusing on essentials
     */
    compressSteeringDocuments(docs: Record<string, string>, options?: CompressionOptions): Promise<{
        compressed: string;
        stats: TokenStats;
    }>;
    /**
     * Optimize context window by intelligent selection and compression
     */
    optimizeContext(context: string, maxTokens: number, relevantKeywords?: string[]): Promise<{
        optimized: string;
        stats: TokenStats;
    }>;
    /**
     * Compress text by removing redundancy while preserving meaning
     */
    private processDocument;
    /**
     * Remove duplicate patterns in text
     */
    private deduplicatePatterns;
    /**
     * Extract key points from text
     */
    private extractKeyPoints;
    /**
     * Compress general text
     */
    private compressText;
    /**
     * Split text into logical chunks
     */
    private splitIntoChunks;
    /**
     * Calculate relevance score for a text chunk
     */
    private calculateRelevanceScore;
    /**
     * Estimate token count (rough approximation)
     */
    estimateTokens(text: string): number;
    /**
     * Truncate text to approximate token count
     */
    private truncateToTokens;
    /**
     * Generate cache key for content
     */
    private generateCacheKey;
    /**
     * Update cache with size limit
     */
    private updateCache;
    /**
     * Calculate compression statistics
     */
    private calculateStats;
    /**
     * Clear the cache
     */
    clearCache(): void;
    /**
     * Get cache statistics
     */
    getCacheStats(): {
        size: number;
        maxSize: number;
    };
}

// ---- telemetry/enhanced-telemetry.d.ts ----
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

// ---- telemetry/runtime-guards.d.ts ----
/**
 * Runtime Guards with OpenTelemetry Integration
 * Implements comprehensive request/response validation with telemetry tracking
 */
import { z } from 'zod';
import { FastifyRequest, FastifyReply } from 'fastify';
export declare enum ViolationType {
    SCHEMA_VALIDATION = "schema_validation",
    RATE_LIMIT = "rate_limit",
    AUTHORIZATION = "authorization",
    BUSINESS_RULE = "business_rule",
    DATA_INTEGRITY = "data_integrity",
    TIMEOUT = "timeout"
}
export declare enum ViolationSeverity {
    LOW = "low",
    MEDIUM = "medium",
    HIGH = "high",
    CRITICAL = "critical"
}
export interface ContractViolation {
    id: string;
    type: ViolationType;
    severity: ViolationSeverity;
    message: string;
    timestamp: Date;
    requestId?: string;
    endpoint?: string;
    details?: Record<string, any>;
}
export interface ValidationResult {
    valid: boolean;
    data?: any;
    violations: ContractViolation[];
}
export declare class RuntimeGuard {
    private tracer;
    private violations;
    /**
     * Validate request payload against Zod schema
     */
    validateRequest<T>(schema: z.ZodSchema<T>, data: unknown, context?: {
        requestId?: string;
        endpoint?: string;
        operation?: string;
    }): ValidationResult;
    /**
     * Validate response data against Zod schema
     */
    validateResponse<T>(schema: z.ZodSchema<T>, data: unknown, context?: {
        requestId?: string;
        endpoint?: string;
        statusCode?: number;
    }): ValidationResult;
    /**
     * Record business rule violation
     */
    recordBusinessRuleViolation(rule: string, message: string, severity?: ViolationSeverity, details?: Record<string, any>): ContractViolation;
    /**
     * Record rate limit violation
     */
    recordRateLimitViolation(endpoint: string, limit: number, current: number, windowMs: number, requestId?: string): ContractViolation;
    /**
     * Create Fastify middleware for request validation
     */
    createRequestValidator<T>(schema: z.ZodSchema<T>): (request: FastifyRequest, reply: FastifyReply) => Promise<never>;
    /**
     * Create Fastify middleware for response validation
     */
    createResponseValidator<T>(schema: z.ZodSchema<T>): (request: FastifyRequest, reply: FastifyReply, payload: any) => Promise<any>;
    /**
     * Get all violations within a time window
     */
    getViolations(since?: Date): ContractViolation[];
    /**
     * Get violation statistics
     */
    getViolationStats(): {
        total: number;
        byType: Record<ViolationType, number>;
        bySeverity: Record<ViolationSeverity, number>;
        last24Hours: number;
    };
    /**
     * Clear old violations (cleanup)
     */
    clearOldViolations(olderThan: Date): number;
    private createValidationViolation;
    private recordViolation;
}
export declare const runtimeGuard: RuntimeGuard;
export declare const CommonSchemas: {
    readonly HealthResponse: z.ZodObject<{
        status: z.ZodLiteral<"healthy">;
        timestamp: z.ZodString;
        service: z.ZodString;
    }, "strip", z.ZodTypeAny, {
        status?: "healthy";
        timestamp?: string;
        service?: string;
    }, {
        status?: "healthy";
        timestamp?: string;
        service?: string;
    }>;
    readonly ErrorResponse: z.ZodObject<{
        error: z.ZodString;
        message: z.ZodOptional<z.ZodString>;
        details: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodAny>>;
    }, "strip", z.ZodTypeAny, {
        message?: string;
        error?: string;
        details?: Record<string, any>;
    }, {
        message?: string;
        error?: string;
        details?: Record<string, any>;
    }>;
    readonly ReservationRequest: z.ZodObject<{
        orderId: z.ZodString;
        itemId: z.ZodString;
        quantity: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        orderId?: string;
        itemId?: string;
        quantity?: number;
    }, {
        orderId?: string;
        itemId?: string;
        quantity?: number;
    }>;
    readonly ReservationResponse: z.ZodObject<{
        ok: z.ZodBoolean;
        reservationId: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        ok?: boolean;
        reservationId?: string;
    }, {
        ok?: boolean;
        reservationId?: string;
    }>;
};

// ---- telemetry/telemetry-service.d.ts ----
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

// ---- tests/_failures/repro-writer.d.ts ----
export declare function writeRepro(name: string, seed: number, data: unknown): Promise<void>;

