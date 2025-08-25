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
