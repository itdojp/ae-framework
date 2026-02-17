import { describe, expect, it } from 'vitest';

import {
  buildSampleLiteral,
  generateAuthMiddleware,
  generateRouteHandler,
  generateServerSetup,
  generateValidationMiddleware,
  parseOpenAPI,
} from '../../../src/agents/code-generation-openapi';

describe('code-generation-openapi helpers', () => {
  it('parses OpenAPI spec into endpoints and schemas', () => {
    const spec = JSON.stringify({
      openapi: '3.0.0',
      paths: {
        '/users': {
          get: { operationId: 'listUsers' },
          post: { operationId: 'createUser' },
        },
      },
      components: {
        schemas: {
          User: { type: 'object', properties: { id: { type: 'integer' } } },
        },
      },
    });

    const parsed = parseOpenAPI(spec);
    expect(parsed.endpoints).toHaveLength(2);
    expect(parsed.schemas).toHaveLength(1);
    expect(parsed.endpoints[0]?.components).toHaveProperty('User');
  });

  it('generates contract-aware route handler with operationId filename', () => {
    const endpoint = {
      path: '/users',
      method: 'post',
      components: {
        User: {
          type: 'object',
          properties: { id: { type: 'integer' }, name: { type: 'string' } },
        },
      },
      definition: {
        operationId: 'create-user',
        responses: {
          201: {
            content: {
              'application/json': {
                schema: { $ref: '#/components/schemas/User' },
              },
            },
          },
          400: {
            content: {
              'application/json': {
                schema: { type: 'object', properties: { code: { type: 'string' } } },
              },
            },
          },
          500: {
            content: {
              'application/json': {
                schema: { type: 'object', properties: { code: { type: 'string' } } },
              },
            },
          },
        },
      },
    };

    const route = generateRouteHandler(endpoint, {
      includeContracts: true,
      useOperationIdForFilenames: true,
    });

    expect(route.path).toBe('src/routes/create-user.ts');
    expect(route.content).toContain('CreateUserInput.parse');
    expect(route.content).toContain('return { status: 201, data: output }');
  });

  it('resolves ref schema when building sample literal', () => {
    const literal = buildSampleLiteral(
      { $ref: '#/components/schemas/User' },
      {
        User: {
          type: 'object',
          properties: {
            id: { type: 'integer' },
            name: { type: 'string' },
          },
        },
      },
    );

    expect(literal).toContain('"id": 0');
    expect(literal).toContain('"name": ""');
  });

  it('returns stable middleware and setup skeletons', () => {
    expect(generateValidationMiddleware().path).toBe('src/middleware/validation.ts');
    expect(generateAuthMiddleware().path).toBe('src/middleware/auth.ts');
    expect(generateServerSetup('express').content).toContain('// Server setup for express');
  });
});
