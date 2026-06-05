import { describe, expect, it } from 'vitest';

import { CodeGenerationAgent } from '../../../src/agents/code-generation-agent';

describe('CodeGenerationAgent generated output safety', () => {
  it('sanitizes test-derived describe and it text before generating implementation code', async () => {
    const agent = new CodeGenerationAgent();

    const generated = await agent.generateCodeFromTests({
      language: 'typescript',
      tests: [{
        path: 'tests/evil.test.ts',
        type: 'unit',
        content: `
describe('../evil'); import fs from "fs"', () => {
  it('return value */\\nconsole.log("comment injection")', () => {})
})
`,
      }],
    });

    expect(generated.files).toHaveLength(1);
    expect(generated.files[0]?.path).toBe('src/evil.ts');
    expect(generated.files[0]?.tests).toEqual(['tests/evil.test.ts']);
    expect(generated.files[0]?.content).toContain('export function evil');
    expect(generated.files[0]?.content).not.toContain('import fs');
    expect(generated.files[0]?.content).not.toContain('*/\n');
  });

  it('emits OpenAPI test skeletons under review artifacts with safe literals and paths', async () => {
    const agent = new CodeGenerationAgent();
    const spec = JSON.stringify({
      openapi: '3.0.0',
      paths: {
        '/orders\n../escape': {
          get: {
            operationId: "evil');\nimport fs from 'fs';/*",
            responses: {
              200: {
                content: {
                  'application/json': {
                    schema: { type: 'object' },
                  },
                },
              },
            },
          },
        },
      },
    });

    const files = await agent.generateTestsFromOpenAPI(spec, {
      useOperationIdForTestNames: true,
      includeSampleInput: true,
    });

    expect(files).toHaveLength(1);
    expect(files[0]?.path).toBe('artifacts/codex/generated-tests/evil-import-fs-from-fs.spec.ts');
    expect(files[0]?.content).toContain('describe("evil');
    expect(files[0]?.content).not.toContain("describe('");
    expect(files[0]?.content).not.toContain("evil');\nimport fs");
    expect(files[0]?.content.split('\n').filter((line) => line.startsWith('// OperationId:'))).toHaveLength(1);
  });
});
