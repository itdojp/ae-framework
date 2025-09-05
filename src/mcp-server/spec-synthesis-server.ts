#!/usr/bin/env node
/**
 * MCP Server: AE-Spec Synthesis Utilities
 * Exposes deterministic tools (compile, validate, codegen) that CodeX can call
 * while using its own LLM to draft and refine AE-Spec content.
 */
import { NodeServer, Tool, CallToolRequestSchema } from '@modelcontextprotocol/sdk/server/node.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { z } from 'zod';
import { resolve } from 'path';
import { writeFileSync } from 'fs';

async function start() {
  const server = new NodeServer({
    name: 'ae-framework-spec-synthesis',
    version: '1.0.0',
  }, {
    capabilities: { tools: {} }
  });

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
    targets: z.array(z.enum(['typescript','api','database','react'])).default(['typescript','api','database']),
    outDir: z.string().optional(),
  });

  const compileTool: Tool = {
    name: 'ae_spec_compile',
    description: 'Compile AE-Spec markdown to AE-IR JSON',
    inputSchema: CompileArgs,
    async handler(args) {
      const { AESpecCompiler } = await import('../..//packages/spec-compiler/src/index.js');
      const compiler = new AESpecCompiler();
      const prev = process.env.AE_SPEC_RELAXED;
      if (args.relaxed) process.env.AE_SPEC_RELAXED = '1';
      try {
        const ir = await compiler.compile({ inputPath: resolve(args.inputPath), outputPath: args.outputPath ? resolve(args.outputPath) : undefined, validate: args.validate !== false });
        const lint = await compiler.lint(ir);
        return {
          content: [
            { type: 'text', text: JSON.stringify({
              outputPath: args.outputPath || null,
              summary: { errors: lint.summary.errors, warnings: lint.summary.warnings, infos: lint.summary.infos },
              counts: { entities: ir.domain.length, apis: ir.api.length, usecases: ir.usecases.length },
            }, null, 2) }
          ]
        };
      } finally {
        process.env.AE_SPEC_RELAXED = prev;
      }
    }
  };

  const validateTool: Tool = {
    name: 'ae_spec_validate',
    description: 'Validate AE-Spec (compile + lint) and return issues summary',
    inputSchema: ValidateArgs,
    async handler(args) {
      const { AESpecCompiler } = await import('../..//packages/spec-compiler/src/index.js');
      const compiler = new AESpecCompiler();
      const prev = process.env.AE_SPEC_RELAXED;
      if (args.relaxed) process.env.AE_SPEC_RELAXED = '1';
      try {
        const ir = await compiler.compile({ inputPath: resolve(args.inputPath), validate: false });
        const lint = await compiler.lint(ir);
        const issues = lint.issues.slice(0, 50).map(i => ({ severity: i.severity, id: i.id, message: i.message, section: i.location?.section || 'root' }));
        const passed = lint.summary.errors === 0 && (args.maxWarnings == null || lint.summary.warnings <= args.maxWarnings);
        return {
          content: [ { type: 'text', text: JSON.stringify({ passed, summary: lint.summary, issues }, null, 2) } ]
        };
      } finally {
        process.env.AE_SPEC_RELAXED = prev;
      }
    }
  };

  const codegenTool: Tool = {
    name: 'ae_spec_codegen',
    description: 'Generate code from AE-IR for selected targets',
    inputSchema: CodegenArgs,
    async handler(args) {
      const { AEIR } = await import('../..//packages/spec-compiler/src/types.js');
      const { readFileSync } = await import('fs');
      const irPath = resolve(args.irPath);
      type IRLike = { domain?: unknown[]; api?: unknown[] };
      const ir = JSON.parse(readFileSync(irPath, 'utf-8')) as unknown as IRLike;
      const { spawnSync } = await import('child_process');
      const outBase = args.outDir || 'generated';
      const run = (t: string, dir: string) => spawnSync(process.execPath, ['dist/src/cli/index.js','codegen','generate','-i', irPath, '-o', resolve(dir), '-t', t], { stdio: 'inherit' });
      const results: Record<string, string> = {};
      for (const t of args.targets) {
        const dir = `${outBase}/${t}`;
        run(t, dir);
        results[t] = dir;
      }
      return { content: [ { type: 'text', text: JSON.stringify({ outBase, results, counts: { entities: ir.domain?.length||0, apis: ir.api?.length||0 } }, null, 2) } ] };
    }
  };

  server.tool(compileTool);
  server.tool(validateTool);
  server.tool(codegenTool);

  const transport = new StdioServerTransport();
  await server.connect(transport);
}

start().catch(err => {
  console.error('[mcp-spec] fatal:', err);
  process.exit(1);
});
