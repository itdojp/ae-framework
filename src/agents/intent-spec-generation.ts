export interface SpecificationRequirement {
  id: string;
  description: string;
}

export interface GeneratedSpecificationTemplates {
  gherkin: string[];
  openapi: Record<string, unknown>;
  asyncapi: Record<string, unknown>;
  graphql: string;
}

export function generateSpecificationTemplates(
  requirements: SpecificationRequirement[],
): GeneratedSpecificationTemplates {
  return {
    gherkin: generateGherkinScenarios(requirements),
    openapi: generateOpenAPISpec(),
    asyncapi: generateAsyncAPISpec(),
    graphql: generateGraphQLSchema(),
  };
}

function generateGherkinScenarios(requirements: SpecificationRequirement[]): string[] {
  return requirements.map(
    (req) =>
      `Feature: ${req.description}\n` +
      `  Scenario: Implement ${req.id}\n` +
      `    Given the system is ready\n` +
      `    When the requirement is implemented\n` +
      `    Then the system meets the requirement\n`,
  );
}

function generateOpenAPISpec(): Record<string, unknown> {
  return {
    openapi: '3.0.0',
    info: {
      title: 'Generated API',
      version: '1.0.0',
    },
    paths: {},
  };
}

function generateAsyncAPISpec(): Record<string, unknown> {
  return {
    asyncapi: '2.0.0',
    info: {
      title: 'Generated Async API',
      version: '1.0.0',
    },
    channels: {},
  };
}

function generateGraphQLSchema(): string {
  return `type Query {\n  # Generated from requirements\n}\n`;
}
