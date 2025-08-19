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
//# sourceMappingURL=types.d.ts.map