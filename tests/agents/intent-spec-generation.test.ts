import { describe, it, expect } from 'vitest';
import { generateSpecificationTemplates } from '../../src/agents/intent-spec-generation';

describe('intent specification template generation', () => {
  it('generates gherkin scenarios from requirements', () => {
    const templates = generateSpecificationTemplates([
      { id: 'REQ-1', description: 'User can sign in' },
      { id: 'REQ-2', description: 'Admin can suspend account' },
    ]);

    expect(templates.gherkin).toHaveLength(2);
    expect(templates.gherkin[0]).toContain('Feature: User can sign in');
    expect(templates.gherkin[0]).toContain('Scenario: Implement REQ-1');
    expect(templates.gherkin[1]).toContain('Feature: Admin can suspend account');
  });

  it('returns openapi/asyncapi skeletons and graphql placeholder schema', () => {
    const templates = generateSpecificationTemplates([]);

    expect(templates.openapi).toMatchObject({
      openapi: '3.0.0',
      info: { title: 'Generated API', version: '1.0.0' },
      paths: {},
    });
    expect(templates.asyncapi).toMatchObject({
      asyncapi: '2.0.0',
      info: { title: 'Generated Async API', version: '1.0.0' },
      channels: {},
    });
    expect(templates.graphql).toContain('type Query');
    expect(templates.graphql).toContain('Placeholder GraphQL schema');
  });
});
