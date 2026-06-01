import { describe, expect, it } from 'vitest';
import { TestGenerationAgent } from '../../../src/agents/test-generation-agent.js';
import { parseOrThrow, PropertyTestsArgsSchema } from '../../../src/mcp-server/schemas.js';

describe('MCP property-test generation safety', () => {
  it('rejects unsafe function and input identifiers at schema boundaries', () => {
    expect(() =>
      parseOrThrow(PropertyTestsArgsSchema, {
        functionName: 'calculateTotal',
        inputs: [{ name: 'value;process.exit()', type: 'number' }],
        invariants: ['returns non-negative values'],
      }),
    ).toThrow('safe TypeScript identifier');

    expect(() =>
      parseOrThrow(PropertyTestsArgsSchema, {
        functionName: 'return',
        inputs: [{ name: 'value', type: 'number' }],
        invariants: ['returns non-negative values'],
      }),
    ).toThrow('reserved TypeScript keyword');

    expect(() =>
      parseOrThrow(PropertyTestsArgsSchema, {
        functionName: 'calculateTotal',
        inputs: [{ name: 'arguments', type: 'number' }],
        invariants: ['returns non-negative values'],
      }),
    ).toThrow('reserved TypeScript keyword');

    expect(() =>
      parseOrThrow(PropertyTestsArgsSchema, {
        functionName: 'a'.repeat(81),
        inputs: [{ name: 'value', type: 'number' }],
        invariants: ['returns non-negative values'],
      }),
    ).toThrow('at most 80 characters');
  });

  it('serializes invariant titles and escapes comment terminators in generated code', async () => {
    const agent = new TestGenerationAgent();
    const tests = await agent.generatePropertyTests({
      function: 'calculateTotal',
      inputs: [
        {
          name: 'quantity',
          type: 'number',
          constraints: ['positive */ process.exit(1); /*'],
        },
      ],
      outputs: { type: 'number' },
      invariants: ['does not close string quotes \'" */ process.exit(1); /*'],
    });

    const code = tests[0]?.code ?? '';
    expect(code).toContain('property("does not close string quotes');
    expect(code).toContain('positive * / process.exit(1); /*');
    expect(code).toContain('does not close string quotes \'" * / process.exit(1); /*');
    expect(code).not.toContain("property('does not close");
    expect(code).not.toContain('filter(/* positive */ process.exit(1); /*');
    expect(code).not.toContain('return /* does not close string quotes \'" */ process.exit(1); /*');
  });

  it('fails closed in the agent if called directly with unsafe identifiers', async () => {
    const agent = new TestGenerationAgent();

    await expect(
      agent.generatePropertyTests({
        function: 'a'.repeat(81),
        inputs: [{ name: 'value', type: 'number' }],
        outputs: { type: 'number' },
        invariants: ['any value is accepted'],
      }),
    ).rejects.toThrow('Invalid property-test function name');
  });
});
