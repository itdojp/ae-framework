import { describe, expect, test } from 'vitest';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
import type { LLM } from '../../src/providers/index.js';
import { FormalAgent } from '../../src/agents/formal-agent.js';
import { IntentAgent } from '../../src/agents/intent-agent.js';
import { VerifyAgent } from '../../src/agents/verify-agent.js';
import { loadLLM } from '../../src/providers/index.js';

const repoRoot = process.cwd();
const pnpmCommand = process.platform === 'win32' ? 'pnpm.cmd' : 'pnpm';

const withoutProviderKeys = (): Record<string, string> => {
  const env = Object.fromEntries(
    Object.entries(process.env).filter((entry): entry is [string, string] => typeof entry[1] === 'string'),
  );

  env['ANTHROPIC_API_KEY'] = '';
  env['OPENAI_API_KEY'] = '';
  env['GEMINI_API_KEY'] = '';
  return env;
};

describe('Agent / MCP boundary smoke', () => {
  test('intent, formal, and verify agents expose stable minimal input/output shapes', async () => {
    const intentAgent = new IntentAgent();
    const intentRequest = IntentAgent.createSimpleRequest(
      'Users must reserve inventory without making on-hand stock negative.',
      {
        domain: 'inventory',
        analysisDepth: 'basic',
        outputFormat: 'structured',
      },
    );

    const intentResult = await intentAgent.analyzeIntent(intentRequest);

    expect(intentResult.requirements).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          id: expect.stringMatching(/^REQ-/),
          description: expect.stringContaining('reserve inventory'),
        }),
      ]),
    );
    expect(intentResult.primaryIntent).toContain('reserve inventory');
    expect(intentResult.traceability.length).toBeGreaterThan(0);

    const formalAgent = new FormalAgent({
      generateDiagrams: false,
      enableModelChecking: false,
    });

    const formalSpec = await formalAgent.generateFormalSpecification(
      'Inventory reservation must never make onHand negative.',
      'tla+',
      { includeDiagrams: false, generateProperties: true },
    );

    expect(formalSpec).toEqual(
      expect.objectContaining({
        id: expect.stringMatching(/^spec_/),
        type: 'tla+',
        title: expect.any(String),
        validation: expect.objectContaining({ status: 'valid' }),
      }),
    );
    expect(formalSpec.title.length).toBeGreaterThan(0);
    expect(formalSpec.content).toContain('MODULE');
    expect(formalSpec.metadata.properties).toEqual(expect.any(Array));

    const verifyAgent = new VerifyAgent({ enableContainers: false });
    const verificationResult = await verifyAgent.runFullVerification({
      codeFiles: [
        {
          path: 'src/sample.ts',
          content: 'export const reserved: number = 1;',
          language: 'typescript',
        },
      ],
      testFiles: [],
      verificationTypes: ['typechecking'],
      strictMode: true,
    });

    expect(verificationResult.passed).toBe(true);
    expect(verificationResult.results).toEqual([
      expect.objectContaining({
        type: 'typechecking',
        passed: true,
        details: { errors: [] },
      }),
    ]);
    expect(verificationResult.traceability.code).toEqual([
      expect.objectContaining({
        id: 'src/sample.ts',
        covered: true,
      }),
    ]);
  });

  test('provider loading falls back to the local echo provider when external API keys are unset', async () => {
    const previousEnv = {
      ANTHROPIC_API_KEY: process.env['ANTHROPIC_API_KEY'],
      OPENAI_API_KEY: process.env['OPENAI_API_KEY'],
      GEMINI_API_KEY: process.env['GEMINI_API_KEY'],
    };

    try {
      delete process.env['ANTHROPIC_API_KEY'];
      delete process.env['OPENAI_API_KEY'];
      delete process.env['GEMINI_API_KEY'];

      const llm: LLM = await loadLLM();
      const completion = await llm.complete({
        system: 'agent-smoke',
        prompt: 'Summarize local fallback behavior.',
      });

      expect(llm.name).toBe('echo');
      expect(completion).toBe('[echo] [system: agent-smoke] Summarize local fallback behavior.');
    } finally {
      for (const [key, value] of Object.entries(previousEnv)) {
        if (value === undefined) {
          delete process.env[key];
        } else {
          process.env[key] = value;
        }
      }
    }
  });

  test(
    'intent MCP stdio server supports initialize, tool listing, and a basic tool call',
    async () => {
      const transport = new StdioClientTransport({
        command: pnpmCommand,
        args: ['exec', 'tsx', 'src/mcp-server/intent-server.ts'],
        cwd: repoRoot,
        env: withoutProviderKeys(),
        stderr: 'pipe',
      });
      const client = new Client(
        { name: 'agent-mcp-smoke-client', version: '1.0.0' },
        { capabilities: {} },
      );

      try {
        await client.connect(transport);

        expect(client.getServerVersion()).toEqual(
          expect.objectContaining({
            name: 'intent-agent-server',
            version: '1.0.0',
          }),
        );
        expect(client.getServerCapabilities()).toEqual(
          expect.objectContaining({
            tools: expect.any(Object),
          }),
        );

        const tools = await client.listTools();
        expect(tools.tools.map((tool) => tool.name)).toEqual(
          expect.arrayContaining([
            'analyze_intent',
            'extract_from_natural_language',
            'create_user_stories',
          ]),
        );

        const result = await client.callTool({
          name: 'extract_from_natural_language',
          arguments: {
            text: 'Users must reserve inventory without making on-hand stock negative.',
          },
        });
        const firstContent = result.content[0];

        expect(firstContent?.type).toBe('text');
        const payload = JSON.parse(firstContent?.type === 'text' ? firstContent.text : '{}') as {
          extracted_requirements?: Array<{ id: string; description: string }>;
          count?: number;
        };

        expect(payload.count).toBeGreaterThan(0);
        expect(payload.extracted_requirements).toEqual(
          expect.arrayContaining([
            expect.objectContaining({
              id: expect.stringMatching(/^REQ-/),
              description: expect.stringContaining('reserve inventory'),
            }),
          ]),
        );
      } finally {
        await client.close().catch(() => undefined);
        await transport.close().catch(() => undefined);
      }
    },
    20_000,
  );
});
