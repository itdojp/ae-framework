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
