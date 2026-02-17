import type { CodeFile } from './code-generation-agent.types.js';

export interface OpenApiEndpoint {
  path: string;
  method: string;
  definition: Record<string, unknown>;
  components: Record<string, unknown>;
}

export interface OpenApiSchemaModel {
  name: string;
  schema: unknown;
}

export interface ParsedOpenApiDocument {
  endpoints: OpenApiEndpoint[];
  schemas: OpenApiSchemaModel[];
}

export interface OpenApiGenerationOptions {
  framework: 'fastify' | 'express' | 'koa';
  database?: 'postgres' | 'mongodb' | 'mysql';
  includeValidation?: boolean;
  includeAuth?: boolean;
  includeContracts?: boolean;
  useOperationIdForFilenames?: boolean;
  useOperationIdForTestNames?: boolean;
}

function asRecord(value: unknown): Record<string, unknown> {
  if (typeof value === 'object' && value !== null && !Array.isArray(value)) {
    return value as Record<string, unknown>;
  }
  return {};
}

function getResponseSchema(content: Record<string, unknown> | undefined): unknown {
  if (!content) {
    return undefined;
  }
  const problemJson = asRecord(content['application/problem+json']);
  if (problemJson['schema']) {
    return problemJson['schema'];
  }
  const appJson = asRecord(content['application/json']);
  if (appJson['schema']) {
    return appJson['schema'];
  }

  const contentTypes = Object.keys(content);
  const picked = contentTypes.find((ct) => ct.startsWith('application/')) ?? contentTypes[0];
  if (!picked) {
    return undefined;
  }
  const pickedValue = asRecord(content[picked]);
  if (pickedValue['schema']) {
    return pickedValue['schema'];
  }
  if (picked === 'text/plain') {
    return { type: 'string' };
  }
  return undefined;
}

function normalizeResponseCodes(responses: Record<string, unknown>): number[] {
  return Object.keys(responses)
    .filter((code) => /^\d{3}$/.test(code))
    .map((code) => Number(code))
    .filter((code) => Number.isFinite(code))
    .sort((a, b) => a - b);
}

function pickSuccessStatus(method: string, codes: number[]): number {
  const successCodes = codes.filter((code) => code >= 200 && code < 300);
  if (method === 'post' && successCodes.includes(201)) {
    return 201;
  }
  if (method === 'delete' && successCodes.includes(204)) {
    return 204;
  }
  if (successCodes.includes(200)) {
    return 200;
  }
  return successCodes[0] ?? (method === 'post' ? 201 : method === 'delete' ? 204 : 200);
}

function pickErrorStatus(codes: number[], kind: 'client' | 'server'): number {
  if (kind === 'client') {
    const fourxx = codes.filter((code) => code >= 400 && code < 500);
    if (fourxx.includes(400)) {
      return 400;
    }
    if (fourxx.includes(422)) {
      return 422;
    }
    return fourxx[0] ?? 400;
  }
  const fivexx = codes.filter((code) => code >= 500 && code < 600);
  if (fivexx.includes(500)) {
    return 500;
  }
  return fivexx[0] ?? 500;
}

function toPascalCase(input: string): string {
  return input
    .split('-')
    .filter(Boolean)
    .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
    .join('');
}

export function parseOpenAPI(spec: string): ParsedOpenApiDocument {
  try {
    const parsed = JSON.parse(spec) as Record<string, unknown>;
    const paths = asRecord(parsed['paths']);
    const components = asRecord(asRecord(parsed['components'])['schemas']);
    const endpoints: OpenApiEndpoint[] = [];
    const schemas: OpenApiSchemaModel[] = [];

    for (const [path, methodsRaw] of Object.entries(paths)) {
      const methods = asRecord(methodsRaw);
      for (const [method, definitionRaw] of Object.entries(methods)) {
        endpoints.push({
          path,
          method,
          definition: asRecord(definitionRaw),
          components,
        });
      }
    }

    for (const [name, schema] of Object.entries(components)) {
      schemas.push({ name, schema });
    }

    return { endpoints, schemas };
  } catch {
    return { endpoints: [], schemas: [] };
  }
}

export function generateValidationMiddleware(): CodeFile {
  return {
    path: 'src/middleware/validation.ts',
    content: `import { FastifyRequest, FastifyReply } from 'fastify';
import { z } from 'zod';

export const validationMiddleware = async (
  request: FastifyRequest,
  reply: FastifyReply
) => {
  // Validate request based on OpenAPI spec
  try {
    // Validation logic here
  } catch (error) {
    reply.code(400).send({ error: 'Validation failed' });
  }
};
`,
    purpose: 'Request validation middleware',
    tests: [],
  };
}

export function generateAuthMiddleware(): CodeFile {
  return {
    path: 'src/middleware/auth.ts',
    content: `import { FastifyRequest, FastifyReply } from 'fastify';

export const authMiddleware = async (
  request: FastifyRequest,
  reply: FastifyReply
) => {
  // Authentication logic
  const token = request.headers.authorization;
  if (!token) {
    reply.code(401).send({ error: 'Unauthorized' });
    return;
  }
  // Verify token
};
`,
    purpose: 'Authentication middleware',
    tests: [],
  };
}

export function generateServerSetup(framework: string): CodeFile {
  const setupCode = framework === 'fastify'
    ? `
import Fastify from 'fastify';
import cors from '@fastify/cors';

const server = Fastify({ logger: true });

server.register(cors);

// Register routes
// ...

const start = async () => {
  try {
    await server.listen({ port: 3000, host: '0.0.0.0' });
  } catch (err) {
    server.log.error(err);
    const { safeExit } = await import('../utils/safe-exit.js');
    safeExit(1);
  }
};

start();
`
    : `// Server setup for ${framework}`;

  return {
    path: 'src/server.ts',
    content: setupCode,
    purpose: 'Server initialization and setup',
    tests: [],
  };
}

export function buildSampleLiteral(
  schema: unknown,
  components: Record<string, unknown> = {},
  depth = 0,
): string {
  const schemaRecord = asRecord(schema);
  if (Object.keys(schemaRecord).length === 0 || depth > 5) {
    return '{}';
  }

  if (typeof schemaRecord['$ref'] === 'string') {
    const refName = schemaRecord['$ref'].split('/').pop();
    const target = refName ? components[refName] : undefined;
    if (target) {
      return buildSampleLiteral(target, components, depth + 1);
    }
    return '{}';
  }

  if (schemaRecord['default'] !== undefined) {
    return JSON.stringify(schemaRecord['default']);
  }

  if (Array.isArray(schemaRecord['enum']) && schemaRecord['enum'].length > 0) {
    return JSON.stringify(schemaRecord['enum'][0]);
  }

  const inferredType = typeof schemaRecord['type'] === 'string'
    ? schemaRecord['type']
    : (schemaRecord['properties'] ? 'object' : (schemaRecord['items'] ? 'array' : undefined));

  switch (inferredType) {
    case 'integer':
    case 'number':
      return '0';
    case 'boolean':
      return 'false';
    case 'string':
      return JSON.stringify('');
    case 'array':
      return '[]';
    case 'object': {
      const properties = asRecord(schemaRecord['properties']);
      const pairs = Object.entries(properties)
        .map(([key, value]) => `${JSON.stringify(key)}: ${buildSampleLiteral(value, components, depth + 1)}`)
        .join(', ');
      return `{ ${pairs} }`;
    }
    default:
      return '{}';
  }
}

export function generateRouteHandler(
  endpoint: OpenApiEndpoint,
  options: Pick<OpenApiGenerationOptions, 'includeContracts' | 'useOperationIdForFilenames'>,
): CodeFile {
  const safePathName = String(endpoint.path)
    .replace(/[^a-zA-Z0-9]/g, '-')
    .replace(/-+/g, '-')
    .replace(/^-|-$/g, '');
  const method = String(endpoint.method || 'get').toLowerCase();
  const operationId = typeof endpoint.definition['operationId'] === 'string'
    ? endpoint.definition['operationId']
    : undefined;
  const operationIdSafe = operationId
    ? operationId
      .replace(/[^a-zA-Z0-9]+/g, '-')
      .replace(/-+/g, '-')
      .replace(/^-|-$/g, '')
    : '';
  const fileSafe = options.useOperationIdForFilenames && operationIdSafe
    ? operationIdSafe.toLowerCase()
    : `${safePathName}-${method}`;
  const contractBase = operationIdSafe
    ? toPascalCase(operationIdSafe)
    : `${toPascalCase(safePathName)}${method.charAt(0).toUpperCase()}${method.slice(1)}`;

  const base = `// Route handler implementation for ${endpoint.method} ${endpoint.path}\n`;
  let content = base;

  if (options.includeContracts) {
    content += `import { z } from 'zod';\n`;
    content += `import { ${contractBase}Input, ${contractBase}Output } from '../contracts/schemas';\n`;
    content += `import { pre, post } from '../contracts/conditions';\n`;
    content += `\n// OperationId: ${operationId ?? 'N/A'}\n`;
    content += `export async function handler(input: unknown): Promise<unknown> {\n`;
    content += `  try {\n`;
    content += `    // Validate input and pre-condition (skeleton)\n`;
    content += `    ${contractBase}Input.parse(input);\n`;
    content += `    if (!pre(input)) return { status: 400, error: 'Precondition failed' };\n`;
    content += `    // TODO: actual implementation here\n`;

    const responses = asRecord(endpoint.definition['responses']);
    const responseCodes = normalizeResponseCodes(responses);
    const successStatus = pickSuccessStatus(method, responseCodes);
    const successResponse = asRecord(responses[String(successStatus)]);
    const successSchema = getResponseSchema(asRecord(successResponse['content']));
    const outputLiteral = buildSampleLiteral(successSchema, endpoint.components);
    content += `    const output: unknown = ${outputLiteral};\n`;
    content += `    if (!post(input, output)) return { status: 500, error: 'Postcondition failed' };\n`;
    content += `    ${contractBase}Output.parse(output);\n`;
    content += `    return { status: ${successStatus}, data: output };\n`;
    content += `  } catch (e) {\n`;

    const badStatus = pickErrorStatus(responseCodes, 'client');
    const serverStatus = pickErrorStatus(responseCodes, 'server');
    const badResponse = asRecord(responses[String(badStatus)]);
    const serverResponse = asRecord(responses[String(serverStatus)]);
    const badLiteral = buildSampleLiteral(getResponseSchema(asRecord(badResponse['content'])), endpoint.components);
    const serverLiteral = buildSampleLiteral(getResponseSchema(asRecord(serverResponse['content'])), endpoint.components);
    content += `    if (e instanceof z.ZodError) return { status: ${badStatus}, error: 'Validation error', details: e.errors, data: ${badLiteral} };\n`;
    content += `    return { status: ${serverStatus}, error: 'Unhandled error', data: ${serverLiteral} };\n`;
    content += '  }\n';
    content += '}\n';
  }

  return {
    path: `src/routes/${fileSafe}.ts`,
    content,
    purpose: `Handle ${endpoint.method} ${endpoint.path}`,
    tests: [],
  };
}

export function generateModel(schema: OpenApiSchemaModel, database?: string): CodeFile {
  return {
    path: `src/models/${schema.name}.ts`,
    content: '// Model implementation',
    purpose: `Model for ${schema.name}`,
    tests: [],
  };
}
