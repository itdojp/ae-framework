#!/usr/bin/env node
/**
 * MCP Server: AE-Spec Synthesis Utilities
 * Exposes deterministic tools (compile, validate, codegen) that CodeX can call
 * while using its own LLM to draft and refine AE-Spec content.
 */
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { CallToolRequestSchema, ErrorCode, ListToolsRequestSchema, McpError } from '@modelcontextprotocol/sdk/types.js';
import { z } from 'zod';
import { resolve } from 'path';

async function start() {
  const server = new Server(
    { name: 'ae-framework-spec-synthesis', version: '1.0.0' },
    { capabilities: { tools: {} } }
  );

  const CompileArgs = z.object({
    inputPath: z.string(),
    outputPath: z.string().optional(),
    validate: z.boolean().optional(),
    relaxed: z.boolean().optional(),
  });

  const ValidateArgs = z.object({
    inputPath: z.string(),
    maxWarnings: z.number().int().nonnegative().optional(),
    relaxed: z.boolean().optional(),
  });

  const CodegenArgs = z.object({
    irPath: z.string().default('.ae/ae-ir.json'),
    targets: z.array(z.enum(['typescript', 'api', 'database', 'react'])).default(['typescript', 'api', 'database']),
    outDir: z.string().optional(),
  });

  server.setRequestHandler(ListToolsRequestSchema, async () => {
    return {
      tools: [
        {
          name: 'ae_spec_compile',
          description: 'Compile AE-Spec markdown to AE-IR JSON',
          inputSchema: {
            type: 'object',
            properties: {
              inputPath: { type: 'string' },
              outputPath: { type: 'string' },
              validate: { type: 'boolean' },
              relaxed: { type: 'boolean' },
            },
            required: ['inputPath'],
          },
        },
        {
          name: 'ae_spec_validate',
          description: 'Validate AE-Spec (compile + lint) and return issues summary',
          inputSchema: {
            type: 'object',
            properties: {
              inputPath: { type: 'string' },
              maxWarnings: { type: 'number' },
              relaxed: { type: 'boolean' },
            },
            required: ['inputPath'],
          },
        },
        {
          name: 'ae_spec_codegen',
          description: 'Generate code from AE-IR for selected targets',
          inputSchema: {
            type: 'object',
            properties: {
              irPath: { type: 'string' },
              targets: { type: 'array', items: { type: 'string', enum: ['typescript', 'api', 'database', 'react'] } },
              outDir: { type: 'string' },
            },
          },
        },
      ],
    };
  });

  server.setRequestHandler(CallToolRequestSchema, async (request) => {
    const { name, arguments: args } = request.params;
    try {
      switch (name) {
        case 'ae_spec_compile': {
          const parsed = CompileArgs.parse(args);
          const { AESpecCompiler } = await import('../..//packages/spec-compiler/src/index.js');
          const compiler = new AESpecCompiler();
          const prev = process.env['AE_SPEC_RELAXED'];
          if (parsed.relaxed) process.env['AE_SPEC_RELAXED'] = '1';
          try {
            const ir = await compiler.compile({
              inputPath: resolve(parsed.inputPath),
              ...(parsed.outputPath !== undefined ? { outputPath: resolve(parsed.outputPath) } : {}),
              ...(parsed.validate !== undefined ? { validate: parsed.validate } : {}),
            });
            const lint = await compiler.lint(ir);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(
                    {
                      outputPath: parsed.outputPath || null,
                      summary: {
                        errors: lint.summary.errors,
                        warnings: lint.summary.warnings,
                        infos: lint.summary.infos,
                      },
                      counts: {
                        entities: ir.domain.length,
                        apis: ir.api?.length ?? 0,
                        usecases: ir.usecases?.length ?? 0
                      },
                    },
                    null,
                    2
                  ),
                },
              ],
            };
          } finally {
            process.env['AE_SPEC_RELAXED'] = prev;
          }
        }

        case 'ae_spec_validate': {
          const parsed = ValidateArgs.parse(args);
          const { AESpecCompiler } = await import('../..//packages/spec-compiler/src/index.js');
          const compiler = new AESpecCompiler();
          const prev = process.env['AE_SPEC_RELAXED'];
          if (parsed.relaxed) process.env['AE_SPEC_RELAXED'] = '1';
          try {
            const ir = await compiler.compile({ inputPath: resolve(parsed.inputPath), validate: false });
            const lint = await compiler.lint(ir);
            const issues = lint.issues
              .slice(0, 50)
              .map((i: any) => ({ severity: i.severity, id: i.id, message: i.message, section: i.location?.section || 'root' }));
            const passed = lint.summary.errors === 0 && (parsed.maxWarnings == null || lint.summary.warnings <= parsed.maxWarnings);
            return { content: [{ type: 'text', text: JSON.stringify({ passed, summary: lint.summary, issues }, null, 2) }] };
          } finally {
            process.env['AE_SPEC_RELAXED'] = prev;
          }
        }

        case 'ae_spec_codegen': {
          const parsed = CodegenArgs.parse(args);
          const { readFileSync } = await import('fs');
          const irPath = resolve(parsed.irPath);
          type IRLike = { domain?: unknown[]; api?: unknown[] };
          const ir = JSON.parse(readFileSync(irPath, 'utf-8')) as unknown as IRLike;
          const { spawnSync } = await import('child_process');
          const outBase = parsed.outDir || 'generated';
          const run = (t: string, dir: string) =>
            spawnSync(process.execPath, ['dist/src/cli/index.js', 'codegen', 'generate', '-i', irPath, '-o', resolve(dir), '-t', t], { stdio: 'inherit' });
          const results: Record<string, string> = {};
          for (const t of parsed.targets) {
            const dir = `${outBase}/${t}`;
            run(t, dir);
            results[t] = dir;
          }
          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify({ outBase, results, counts: { entities: ir.domain?.length || 0, apis: ir.api?.length || 0 } }, null, 2),
              },
            ],
          };
        }

        default:
          throw new McpError(ErrorCode.MethodNotFound, `Unknown tool: ${name}`);
      }
    } catch (error) {
      if (error instanceof z.ZodError) {
        throw new McpError(ErrorCode.InvalidParams, `Invalid parameters: ${error.message}`);
      }
      throw error;
    }
  });

  const transport = new StdioServerTransport();
  await server.connect(transport);
}

start().catch((err) => {
  console.error('[mcp-spec] fatal:', err);
  process.exit(1);
});
