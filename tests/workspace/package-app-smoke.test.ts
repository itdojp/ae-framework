import { randomUUID } from 'node:crypto';
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { describe, expect, it } from 'vitest';

import DefaultAESpecCompiler, { AESpecCompiler } from '../../packages/spec-compiler/src/index.js';
import { colors, designTokens, spacing } from '../../packages/design-tokens/src/index.ts';
import { tailwindTokens } from '../../packages/design-tokens/src/tailwind.ts';
import { Button } from '../../packages/ui/src/button.tsx';
import { Input } from '../../packages/ui/src/input.tsx';
import { Badge, badgeVariants } from '../../packages/ui/src/badge.tsx';
import {
  FLOW_SCHEMA_VERSION,
  adaptAgentBuilderFlow,
  parseFlow,
  simulateFlow,
} from '../../packages/agent-builder-adapter/src/index.js';
import {
  buildCoderPrompt,
  renderTlaModule,
  samplingProfiles as coderSamplingProfiles,
  type FormalPlan,
} from '../../packages/formalize-coder/src/index.js';
import {
  FORMAL_PLAN_SCHEMA_VERSION,
  buildPlannerPrompt,
  samplingProfiles as plannerSamplingProfiles,
} from '../../packages/formalize-planner/src/index.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '../..');

type PackageJson = {
  name?: string;
  scripts?: Record<string, string>;
  exports?: unknown;
};

const readJson = <T>(relativePath: string): T => {
  return JSON.parse(readFileSync(path.join(repoRoot, relativePath), 'utf8')) as T;
};

const readText = (relativePath: string) => readFileSync(path.join(repoRoot, relativePath), 'utf8');

const flattenKeys = (value: unknown, prefix = ''): string[] => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    return prefix ? [prefix] : [];
  }

  return Object.entries(value as Record<string, unknown>).flatMap(([key, child]) => {
    const nextPrefix = prefix ? `${prefix}.${key}` : key;
    return flattenKeys(child, nextPrefix);
  });
};

describe('workspace package and app smoke inventory', () => {
  it('exposes root and package scripts used by the workspace smoke lane', () => {
    const rootPackage = readJson<PackageJson>('package.json');

    expect(rootPackage.scripts).toMatchObject({
      'build:spec-compiler': expect.stringContaining('@ae-framework/spec-compiler'),
      'build:tokens': expect.stringContaining('@ae-framework/design-tokens'),
      'build:ui': expect.stringContaining('@ae-framework/ui'),
      'build:frontend': expect.stringContaining('@ae-framework/web'),
      'type-check:frontend': expect.stringContaining('@ae-framework/web'),
      'test:workspace:smoke': expect.stringContaining('vitest run tests/workspace'),
    });

    const expectedScripts: Array<[string, string[]]> = [
      ['packages/spec-compiler/package.json', ['build', 'test']],
      ['packages/design-tokens/package.json', ['build', 'clean']],
      ['packages/ui/package.json', ['build', 'type-check']],
      ['apps/web/package.json', ['build', 'type-check']],
      ['apps/storybook/package.json', ['build-storybook']],
    ];

    for (const [relativePath, scripts] of expectedScripts) {
      const packageJson = readJson<PackageJson>(relativePath);
      expect(packageJson.name, relativePath).toBeTruthy();
      for (const script of scripts) {
        expect(packageJson.scripts?.[script], `${relativePath}:${script}`).toBeTruthy();
      }
    }
  });
});

describe('workspace package source-level smoke tests', () => {
  it('compiles a minimal AE-Spec through the spec-compiler package entrypoint', async () => {
    expect(DefaultAESpecCompiler).toBe(AESpecCompiler);

    const tempRoot = path.join(
      repoRoot,
      'artifacts',
      `workspace-smoke-${process.pid}-${randomUUID()}`,
    );
    const specPath = path.join(tempRoot, 'minimal-spec.md');
    mkdirSync(tempRoot, { recursive: true });
    writeFileSync(
      specPath,
      `# WorkspaceSmokeSpec

## Domain

### Product
- **id** (string, required) - Product identifier
- **name** (string, required) - Product name

## Business Rules
- **INV-PRODUCT-001**: Product id must be present.

## Use Cases

### View Product
- User requests a product.
- System returns product details.
`,
      'utf8',
    );

    try {
      const compiler = new AESpecCompiler();
      const ir = await compiler.compile({ inputPath: specPath, validate: false });
      expect(ir.metadata.name).toBe('WorkspaceSmokeSpec');
      expect(ir.domain.map((entry) => entry.name)).toEqual(['Product']);
      expect(ir.invariants?.[0]?.severity).toBe('error');

      const lintReport = await compiler.lint(ir);
      expect(lintReport.summary.errors).toBe(0);
    } finally {
      rmSync(tempRoot, { recursive: true, force: true });
    }
  });

  it('keeps design token and Tailwind token exports aligned', () => {
    expect(designTokens.colors.primary[500]).toBe('#3b82f6');
    expect(colors.semantic.success).toBe('#10b981');
    expect(spacing[4]).toBe('1rem');
    expect(tailwindTokens.colors.primary).toEqual(colors.primary);
    expect(tailwindTokens.spacing).toEqual(spacing);
    expect(tailwindTokens.screens).toEqual(designTokens.breakpoints);
  });

  it('exposes UI component surfaces without requiring prebuilt package artifacts', () => {
    const uiIndex = readText('packages/ui/src/index.ts');
    const expectedExports = {
      Button: 'button',
      Input: 'input',
      Dialog: 'dialog',
      Textarea: 'textarea',
      Checkbox: 'checkbox',
      Select: 'select',
      Badge: 'badge',
    } as const;
    for (const [exportName, modulePath] of Object.entries(expectedExports)) {
      const exportPattern = new RegExp(
        String.raw`^export\s+\{[^}\n]*\b${exportName}\b[^}\n]*\}\s+from\s+['"]\./${modulePath}['"];?$`,
        'm',
      );
      expect(uiIndex, `packages/ui/src/index.ts should export ${exportName} from ./${modulePath}`).toMatch(
        exportPattern,
      );
    }

    expect(Button.displayName).toBe('Button');
    expect(Input.displayName).toBe('Input');
    expect(typeof Badge).toBe('function');
    expect(badgeVariants({ variant: 'success' })).toContain('emerald');
  });

  it('adapts, parses, and simulates a minimal agent-builder flow', () => {
    const adapted = adaptAgentBuilderFlow({
      meta: { name: 'workspace-smoke' },
      context: { correlation: { runId: 'workspace-smoke-run' } },
      nodes: [
        { name: 'intent', type: 'intent2formal', outputs: ['spec'] },
        { name: 'codegen', role: 'tests2code', inputs: ['spec'], outputs: ['code'] },
      ],
      edges: [{ source: 'intent', target: 'codegen' }],
    });

    const parsed = parseFlow(adapted, { enforceKnownKinds: true });
    expect(parsed.schemaVersion).toBe(FLOW_SCHEMA_VERSION);
    expect(parsed.nodes.map((node) => node.id)).toEqual(['intent', 'codegen']);
    expect(parsed.edges).toEqual([{ from: 'intent', to: 'codegen' }]);
    expect(parsed.correlation?.runId).toBe('workspace-smoke-run');

    const simulated = simulateFlow(parsed, {
      runId: 'workspace-smoke-run',
      startedAt: '2026-05-08T00:00:00.000Z',
    });
    expect(simulated.nodes.map((node) => node.status)).toEqual(['simulated', 'simulated']);
    expect(simulated.nodes.map((node) => node.order)).toEqual([1, 2]);
  });

  it('exposes formalize planner and coder prompt/render smoke behavior', () => {
    const plannerPrompt = buildPlannerPrompt({
      requirements: 'Inventory count must never become negative.',
      context: 'Use a small TLA+ skeleton.',
    });
    expect(plannerPrompt).toContain(`schemaVersion: ${FORMAL_PLAN_SCHEMA_VERSION}`);
    expect(plannerPrompt).toContain('Inventory count must never become negative.');
    expect(plannerSamplingProfiles.deterministic.temperature).toBe(0);

    const plan: FormalPlan = {
      schemaVersion: FORMAL_PLAN_SCHEMA_VERSION,
      metadata: { source: 'workspace-smoke', generatedAt: '2026-05-08T00:00:00.000Z' },
      variables: [{ name: 'inventory', type: 'Int' }],
      actions: [
        { name: 'Init', tla: 'inventory = 1' },
        { name: 'Reserve', tla: "inventory' = inventory - 1" },
      ],
      invariants: [{ name: 'NonNegative', tla: 'inventory >= 0' }],
    };

    const coderPrompt = buildCoderPrompt({ plan, moduleName: 'InventorySmoke' });
    const tlaModule = renderTlaModule(plan, { moduleName: 'InventorySmoke' });
    expect(coderPrompt).toContain('Module Name: InventorySmoke');
    expect(coderSamplingProfiles.deterministic.temperature).toBe(0);
    expect(tlaModule).toContain('MODULE InventorySmoke');
    expect(tlaModule).toContain('Init == inventory = 1');
    expect(tlaModule).toContain('Reserve ==');
    expect(tlaModule).toContain('NonNegative == inventory >= 0');
  });
});

describe('workspace frontend app and Storybook smoke inventory', () => {
  it('keeps web route entrypoints and locale message keys aligned', () => {
    for (const relativePath of [
      'apps/web/app/page.tsx',
      'apps/web/app/layout.tsx',
      'apps/web/components/ProductCard.tsx',
      'apps/web/components/ProductForm.tsx',
    ]) {
      expect(existsSync(path.join(repoRoot, relativePath)), relativePath).toBe(true);
    }

    const pageSource = readText('apps/web/app/page.tsx');
    expect(pageSource).toContain("useTranslations('HomePage')");
    expect(pageSource).toContain('export default function HomePage');

    const enMessages = readJson<Record<string, unknown>>('apps/web/messages/en.json');
    const jaMessages = readJson<Record<string, unknown>>('apps/web/messages/ja.json');
    expect(flattenKeys(jaMessages).sort()).toEqual(flattenKeys(enMessages).sort());
    expect(flattenKeys(enMessages)).toContain('HomePage.getStarted');
  });

  it('tracks Storybook story inventory without running a browser build', () => {
    const storiesDir = path.join(repoRoot, 'apps/storybook/stories');
    const storyFiles = readdirSync(storiesDir).filter((entry) => entry.endsWith('.stories.tsx')).sort();
    expect(storyFiles).toEqual([
      'Button.stories.tsx',
      'Dialog.stories.tsx',
      'Input.stories.tsx',
      'Product.stories.tsx',
    ]);

    for (const storyFile of storyFiles) {
      const source = readFileSync(path.join(storiesDir, storyFile), 'utf8');
      expect(source, `${storyFile} should declare default Storybook metadata`).toContain('export default');
      expect(source, `${storyFile} should set a Storybook title`).toContain('title:');
      expect(source, `${storyFile} should export at least one story`).toMatch(/export const \w+/);
    }
  });
});
