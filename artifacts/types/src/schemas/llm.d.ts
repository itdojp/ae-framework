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
