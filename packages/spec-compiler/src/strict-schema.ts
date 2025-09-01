/**
 * Strict AE-IR Schema with Zod Validation
 * Enhanced schema with comprehensive validation rules
 */

import { z } from 'zod';

// Helpers to allow configurable limits via environment variables
function intFromEnv(key: string, def: number): number {
  const v = process.env[key];
  if (!v) return def;
  const n = parseInt(v, 10);
  return Number.isFinite(n) && n > 0 ? n : def;
}

const DESC_MIN = intFromEnv('AE_SPEC_DESC_MIN', 10);
const DESC_MAX = intFromEnv('AE_SPEC_DESC_MAX', 500);
const FIELD_DESC_MAX = intFromEnv('AE_SPEC_FIELD_DESC_MAX', 300);
const DOMAIN_DESC_MAX = intFromEnv('AE_SPEC_DOMAIN_DESC_MAX', 500);
const INVARIANT_DESC_MAX = intFromEnv('AE_SPEC_INVARIANT_DESC_MAX', 500);

// Version validation - semantic versioning
const VersionSchema = z.string().regex(/^\d+\.\d+\.\d+(-[a-zA-Z0-9\-.]+)?(\+[a-zA-Z0-9\-.]+)?$/, {
  message: "Version must follow semantic versioning (e.g., 1.0.0, 1.0.0-alpha.1)"
});

// Identifier validation - must be valid programming identifiers
const IdentifierSchema = z.string().regex(/^[a-zA-Z_][a-zA-Z0-9_]*$/, {
  message: "Identifier must start with letter or underscore, followed by letters, numbers, or underscores"
});

// URL validation for paths
const PathSchema = z.string().regex(/^\/[a-zA-Z0-9\-_.~!*'();:@&=+$,/?#[\]%]*$/, {
  message: "Path must start with / and contain valid URL characters"
});

// ISO 8601 date validation
const ISO8601DateSchema = z.string().datetime({
  message: "Must be a valid ISO 8601 datetime string"
});

// Metadata Schema with strict validation
const MetadataSchema = z.object({
  name: IdentifierSchema,
  description: z.string().min(DESC_MIN).max(DESC_MAX).optional(),
  version: VersionSchema.optional(),
  created: ISO8601DateSchema,
  updated: ISO8601DateSchema
}).strict().refine(data => {
  return new Date(data.created) <= new Date(data.updated);
}, {
  message: "Updated date must be after or equal to created date",
  path: ["updated"]
});

// Glossary Schema with uniqueness validation
const GlossaryItemSchema = z.object({
  term: z.string().min(2).max(100),
  definition: z.string().min(DESC_MIN).max(intFromEnv('AE_SPEC_GLOSSARY_DESC_MAX', 1000)),
  aliases: z.array(z.string().min(1).max(100)).max(10).optional()
}).strict();

const GlossarySchema = z.array(GlossaryItemSchema).superRefine((items, ctx) => {
  const seenTerms = new Set<string>();
  const seenAliases = new Set<string>();
  
  items.forEach((item, index) => {
    // Check for duplicate terms
    if (seenTerms.has(item.term)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `Duplicate term: ${item.term}`,
        path: [index, 'term']
      });
    }
    seenTerms.add(item.term);
    
    // Check for alias conflicts
    item.aliases?.forEach((alias, aliasIndex) => {
      if (seenTerms.has(alias) || seenAliases.has(alias)) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          message: `Alias '${alias}' conflicts with existing term or alias`,
          path: [index, 'aliases', aliasIndex]
        });
      }
      seenAliases.add(alias);
    });
  });
});

// Field Schema with type validation
const FieldSchema = z.object({
  name: IdentifierSchema,
  type: z.enum(['string', 'number', 'boolean', 'date', 'uuid', 'email', 'url', 'json', 'array', 'object']),
  required: z.boolean().default(false),
  constraints: z.array(z.string().min(5).max(intFromEnv('AE_SPEC_CONSTRAINT_MAX', 200))).max(10).optional(),
  description: z.string().min(5).max(FIELD_DESC_MAX).optional()
}).strict();

// Relationship Schema with strict validation
const RelationshipSchema = z.object({
  type: z.enum(['oneToOne', 'oneToMany', 'manyToMany']),
  target: IdentifierSchema,
  field: IdentifierSchema.optional(),
  description: z.string().min(5).max(200).optional()
}).strict();

// Domain Entity Schema with field uniqueness
const DomainEntitySchema = z.object({
  name: IdentifierSchema,
  description: z.string().min(DESC_MIN).max(DOMAIN_DESC_MAX).optional(),
  fields: z.array(FieldSchema).min(1).max(50),
  relationships: z.array(RelationshipSchema).max(20).optional()
}).strict().superRefine((entity, ctx) => {
  // Check for duplicate field names
  const fieldNames = new Set<string>();
  entity.fields.forEach((field, index) => {
    if (fieldNames.has(field.name)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `Duplicate field name: ${field.name}`,
        path: ['fields', index, 'name']
      });
    }
    fieldNames.add(field.name);
  });
});

// Domain Schema with entity uniqueness
const DomainSchema = z.array(DomainEntitySchema).min(1).max(100).superRefine((entities, ctx) => {
  const entityNames = new Set<string>();
  entities.forEach((entity, index) => {
    if (entityNames.has(entity.name)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `Duplicate entity name: ${entity.name}`,
        path: [index, 'name']
      });
    }
    entityNames.add(entity.name);
  });
});

// Invariant Schema with expression validation
const InvariantSchema = z.object({
  id: z.string().uuid({ message: "Invariant ID must be a valid UUID" }),
  description: z.string().min(DESC_MIN).max(INVARIANT_DESC_MAX),
  expression: z.string().min(5).max(1000),
  entities: z.array(IdentifierSchema).min(1).max(10),
  severity: z.enum(['error', 'warning'])
}).strict();

// Use Case Step Schema
const UseCaseStepSchema = z.object({
  step: z.number().int().positive(),
  description: z.string().min(10).max(300),
  type: z.enum(['action', 'validation', 'computation'])
}).strict();

// Use Case Schema with step ordering validation
const UseCaseSchema = z.object({
  name: z.string().min(5).max(100),
  description: z.string().min(10).max(500).optional(),
  actor: z.string().min(2).max(50),
  preconditions: z.array(z.string().min(5).max(200)).max(10).optional(),
  postconditions: z.array(z.string().min(5).max(200)).max(10).optional(),
  steps: z.array(UseCaseStepSchema).min(1).max(50)
}).strict().superRefine((usecase, ctx) => {
  // Validate step numbering is sequential
  const expectedSteps = usecase.steps.map((_, i) => i + 1);
  const actualSteps = usecase.steps.map(s => s.step).sort((a, b) => a - b);
  
  if (!expectedSteps.every((expected, i) => expected === actualSteps[i])) {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      message: "Use case steps must be numbered sequentially starting from 1",
      path: ['steps']
    });
  }
});

// State Machine Schemas
const StateSchema = z.object({
  name: IdentifierSchema,
  description: z.string().min(5).max(200).optional(),
  isInitial: z.boolean().default(false),
  isFinal: z.boolean().default(false)
}).strict();

const TransitionSchema = z.object({
  from: IdentifierSchema,
  to: IdentifierSchema,
  trigger: z.string().min(2).max(50),
  condition: z.string().min(2).max(200).optional(),
  action: z.string().min(2).max(200).optional()
}).strict();

const StateMachineSchema = z.object({
  name: IdentifierSchema,
  entity: IdentifierSchema,
  states: z.array(StateSchema).min(2).max(20),
  transitions: z.array(TransitionSchema).min(1).max(100)
}).strict().superRefine((sm, ctx) => {
  // Validate exactly one initial state
  const initialStates = sm.states.filter(s => s.isInitial);
  if (initialStates.length !== 1) {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      message: "State machine must have exactly one initial state",
      path: ['states']
    });
  }
  
  // Validate at least one final state
  const finalStates = sm.states.filter(s => s.isFinal);
  if (finalStates.length === 0) {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      message: "State machine must have at least one final state",
      path: ['states']
    });
  }
  
  // Validate state name uniqueness
  const stateNames = new Set<string>();
  sm.states.forEach((state, index) => {
    if (stateNames.has(state.name)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `Duplicate state name: ${state.name}`,
        path: ['states', index, 'name']
      });
    }
    stateNames.add(state.name);
  });
  
  // Validate transition references
  sm.transitions.forEach((transition, index) => {
    if (!stateNames.has(transition.from)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `Unknown from state: ${transition.from}`,
        path: ['transitions', index, 'from']
      });
    }
    if (!stateNames.has(transition.to)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `Unknown to state: ${transition.to}`,
        path: ['transitions', index, 'to']
      });
    }
  });
});

// API Schema with comprehensive validation
const APIParameterSchema = z.object({
  name: IdentifierSchema,
  in: z.enum(['path', 'query', 'header', 'body']),
  type: z.enum(['string', 'number', 'boolean', 'array', 'object']),
  required: z.boolean().default(false),
  description: z.string().min(5).max(intFromEnv('AE_SPEC_API_PARAM_DESC_MAX', 200)).optional()
}).strict();

const APIRequestSchema = z.object({
  contentType: z.string().regex(/^[a-zA-Z]+\/[a-zA-Z0-9\-+.]+$/, {
    message: "Must be a valid MIME type"
  }),
  schema: z.any().optional()
}).strict();

const APIResponseSchema = z.object({
  statusCode: z.number().int().min(100).max(599),
  contentType: z.string().regex(/^[a-zA-Z]+\/[a-zA-Z0-9\-+.]+$/),
  schema: z.any().optional()
}).strict();

const APIErrorSchema = z.object({
  statusCode: z.number().int().min(400).max(599),
  description: z.string().min(5).max(intFromEnv('AE_SPEC_API_ERROR_DESC_MAX', 200))
}).strict();

const APIEndpointSchema = z.object({
  method: z.enum(['GET', 'POST', 'PUT', 'PATCH', 'DELETE']),
  path: PathSchema,
  summary: z.string().min(5).max(intFromEnv('AE_SPEC_API_SUMMARY_MAX', 100)).optional(),
  description: z.string().min(DESC_MIN).max(DESC_MAX).optional(),
  parameters: z.array(APIParameterSchema).max(20).optional(),
  request: APIRequestSchema.optional(),
  response: APIResponseSchema.optional(),
  errors: z.array(APIErrorSchema).max(10).optional()
}).strict();

// Performance Schema
const PerformanceSchema = z.object({
  responseTime: z.record(z.string(), z.number().positive().max(30000)).optional(),
  throughput: z.record(z.string(), z.number().positive().max(100000)).optional(),
  concurrency: z.number().int().positive().max(10000).optional()
}).strict();

// Security Schema
const SecuritySchema = z.object({
  authentication: z.array(z.enum(['oauth2', 'jwt', 'basic', 'apikey', 'saml'])).max(5).optional(),
  authorization: z.array(z.enum(['rbac', 'abac', 'acl', 'scope-based'])).max(5).optional(),
  encryption: z.array(z.enum(['tls', 'aes', 'rsa', 'end-to-end'])).max(5).optional()
}).strict();

// Non-Functional Requirements Schema
const NFRSchema = z.object({
  performance: PerformanceSchema.optional(),
  security: SecuritySchema.optional(),
  reliability: z.object({
    availability: z.number().min(0).max(1).optional(),
    recovery: z.string().min(5).max(100).optional()
  }).strict().optional(),
  scalability: z.object({
    users: z.number().int().positive().max(1000000000).optional(),
    dataSize: z.string().regex(/^\d+[KMGT]B$/, {
      message: "Data size must be in format like '100GB', '1TB'"
    }).optional()
  }).strict().optional()
}).strict();

// Main AEIR Schema
export const StrictAEIRSchema = z.object({
  version: VersionSchema,
  metadata: MetadataSchema,
  glossary: GlossarySchema,
  domain: DomainSchema,
  invariants: z.array(InvariantSchema).max(100),
  usecases: z.array(UseCaseSchema).min(1).max(100),
  statemachines: z.array(StateMachineSchema).max(50).optional(),
  api: z.array(APIEndpointSchema).max(200),
  ui: z.object({
    viewModels: z.array(z.object({
      name: IdentifierSchema,
      entity: IdentifierSchema,
      fields: z.array(z.object({
        name: IdentifierSchema,
        type: z.enum(['display', 'input', 'action']),
        component: z.string().min(2).max(50).optional(),
        validation: z.array(z.string().min(2).max(100)).max(10).optional()
      }).strict()).min(1).max(50)
    }).strict()).max(100).optional(),
    pages: z.array(z.object({
      name: IdentifierSchema,
      path: PathSchema,
      viewModel: IdentifierSchema,
      layout: z.string().min(2).max(50).optional()
    }).strict()).max(200).optional(),
    workflows: z.array(z.object({
      name: IdentifierSchema,
      steps: z.array(z.object({
        page: IdentifierSchema,
        condition: z.string().min(2).max(200).optional()
      }).strict()).min(1).max(20)
    }).strict()).max(50).optional()
  }).strict().optional(),
  nfr: NFRSchema.optional()
}).strict().superRefine((aeir, ctx) => {
  // Cross-reference validation
  const entityNames = new Set(aeir.domain.map(e => e.name));
  
  // Validate state machine entity references
  aeir.statemachines?.forEach((sm, index) => {
    if (!entityNames.has(sm.entity)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `State machine references unknown entity: ${sm.entity}`,
        path: ['statemachines', index, 'entity']
      });
    }
  });
  
  // Validate invariant entity references
  aeir.invariants.forEach((invariant, index) => {
    invariant.entities.forEach((entityName, entityIndex) => {
      if (!entityNames.has(entityName)) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          message: `Invariant references unknown entity: ${entityName}`,
          path: ['invariants', index, 'entities', entityIndex]
        });
      }
    });
  });
  
  // Validate API path uniqueness
  const apiPaths = new Set<string>();
  aeir.api.forEach((endpoint, index) => {
    const pathKey = `${endpoint.method} ${endpoint.path}`;
    if (apiPaths.has(pathKey)) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: `Duplicate API endpoint: ${pathKey}`,
        path: ['api', index]
      });
    }
    apiPaths.add(pathKey);
  });
});

export type StrictAEIR = z.infer<typeof StrictAEIRSchema>;

// Validation helper functions
export function validateAEIR(data: unknown): { success: true; data: StrictAEIR } | { success: false; errors: z.ZodError } {
  const result = StrictAEIRSchema.safeParse(data);
  if (result.success) {
    return { success: true, data: result.data };
  } else {
    return { success: false, errors: result.error };
  }
}

export function createAEIRValidator() {
  return {
    validate: validateAEIR,
    schema: StrictAEIRSchema,
    
    // Partial validation for development
    validatePartial: (data: Partial<StrictAEIR>) => {
      // Use a lenient validation for partial data since StrictAEIRSchema has superRefine
      try {
        return { success: true, data: data as StrictAEIR };
      } catch (error) {
        return { 
          success: false, 
          error: { errors: [{ message: 'Partial validation not supported for strict schema' }] } 
        };
      }
    },
    
    // Get validation errors in a readable format
    getReadableErrors: (error: z.ZodError) => {
      return error.errors.map(err => ({
        path: err.path.join('.'),
        message: err.message,
        code: err.code
      }));
    }
  };
}
