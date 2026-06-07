import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';

import { createCodegenCommand } from '../../src/cli/codegen-cli.js';

const testRoot = path.join(process.cwd(), 'artifacts', 'codegen-cli-policy-test');
const approvalScope = 'high-impact:codegen-materialize';
const relative = (value: string) => path.relative(process.cwd(), value).replace(/\\/g, '/');

const validAeir = {
  version: '1.0.0',
  metadata: {
    name: 'CodegenCliPolicyTest',
    created: '2026-06-07T00:00:00.000Z',
    updated: '2026-06-07T00:00:00.000Z',
  },
  glossary: [],
  domain: [
    {
      name: 'Product',
      fields: [
        { name: 'id', type: 'string', required: true },
        { name: 'name', type: 'string', required: true },
      ],
    },
  ],
  invariants: [],
  usecases: [],
  api: [],
};

const runCodegen = async (args: string[]) => {
  const command = createCodegenCommand();
  command.exitOverride();
  await command.parseAsync(args, { from: 'user' });
};

describe('codegen CLI materialization policy', () => {
  let logSpy: ReturnType<typeof vi.spyOn>;
  let errorSpy: ReturnType<typeof vi.spyOn>;
  let previousHighImpactEnv: Record<string, string | undefined>;

  const highImpactEnvNames = [
    'AE_UNTRUSTED_CHECKOUT',
    'AE_GUARD_UNTRUSTED_CHECKOUT',
    'AE_CI_UNTRUSTED_CHECKOUT',
    'CI',
    'GITHUB_ACTIONS',
    'GITHUB_EVENT_NAME',
    'GITHUB_REF_PROTECTED',
    'GITHUB_TOKEN',
    'GH_TOKEN',
    'NODE_AUTH_TOKEN',
    'NPM_TOKEN',
    'ACTIONS_ID_TOKEN_REQUEST_TOKEN',
    'ACTIONS_RUNTIME_TOKEN',
  ] as const;

  beforeEach(() => {
    previousHighImpactEnv = Object.fromEntries(
      highImpactEnvNames.map((name) => [name, process.env[name]]),
    );
    for (const name of highImpactEnvNames) {
      delete process.env[name];
    }
    process.env.CI = '0';
    process.env.GITHUB_ACTIONS = '0';
    process.env.GITHUB_EVENT_NAME = 'push';
    process.env.GITHUB_REF_PROTECTED = 'true';

    rmSync(testRoot, { recursive: true, force: true });
    mkdirSync(testRoot, { recursive: true });
    writeFileSync(path.join(testRoot, 'ae-ir.json'), JSON.stringify(validAeir, null, 2), 'utf8');
    logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    errorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    vi.restoreAllMocks();
    for (const name of highImpactEnvNames) {
      const value = previousHighImpactEnv[name];
      if (value === undefined) {
        delete process.env[name];
      } else {
        process.env[name] = value;
      }
    }
    rmSync(testRoot, { recursive: true, force: true });
  });

  it('TGT-014-F002: defaults generate to dry-run and does not materialize executable artifacts without --apply', async () => {
    const outputDir = path.join(testRoot, 'generated-dry-run');

    await runCodegen([
      'generate',
      '-i', relative(path.join(testRoot, 'ae-ir.json')),
      '-o', relative(outputDir),
      '-t', 'react',
    ]);

    expect(logSpy.mock.calls.flat().join('\n')).toContain('defaults to dry-run');
    expect(existsSync(path.join(outputDir, 'components', 'ProductForm.tsx'))).toBe(false);
    expect(existsSync(path.join(outputDir, '.codegen-manifest.json'))).toBe(false);
  });

  it('rejects requested materialization before explicit approval is supplied', async () => {
    const outputDir = path.join(testRoot, 'generated-unapproved');

    await runCodegen([
      'generate',
      '-i', relative(path.join(testRoot, 'ae-ir.json')),
      '-o', relative(outputDir),
      '-t', 'react',
      '--apply',
    ]);

    expect(errorSpy.mock.calls.flat().join('\n')).toContain(`requires explicit approval scope '${approvalScope}'`);
    expect(existsSync(path.join(outputDir, 'components', 'ProductForm.tsx'))).toBe(false);
    expect(existsSync(path.join(outputDir, '.codegen-manifest.json'))).toBe(false);
  });


  it('TGT-014-F002: forces approved materialization to dry-run from an untrusted checkout', async () => {
    const outputDir = path.join(testRoot, 'generated-untrusted');
    const previous = process.env.AE_UNTRUSTED_CHECKOUT;
    process.env.AE_UNTRUSTED_CHECKOUT = '1';

    try {
      await runCodegen([
        'generate',
        '-i', relative(path.join(testRoot, 'ae-ir.json')),
        '-o', relative(outputDir),
        '-t', 'react',
        '--apply',
        '--approval-scope', approvalScope,
      ]);
    } finally {
      if (previous === undefined) {
        delete process.env.AE_UNTRUSTED_CHECKOUT;
      } else {
        process.env.AE_UNTRUSTED_CHECKOUT = previous;
      }
    }

    expect(logSpy.mock.calls.flat().join('\n')).toContain('untrusted workspace/ref');
    expect(existsSync(path.join(outputDir, 'components', 'ProductForm.tsx'))).toBe(false);
    expect(existsSync(path.join(outputDir, '.codegen-manifest.json'))).toBe(false);
  });

  it('TGT-014-F002: materializes only after the trusted codegen approval scope is present', async () => {
    const outputDir = path.join(testRoot, 'generated-approved');

    await runCodegen([
      'generate',
      '-i', relative(path.join(testRoot, 'ae-ir.json')),
      '-o', relative(outputDir),
      '-t', 'react',
      '--apply',
      '--approval-scope', approvalScope,
    ]);

    const manifestPath = path.join(outputDir, '.codegen-manifest.json');
    const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));

    expect(existsSync(path.join(outputDir, 'components', 'ProductForm.tsx'))).toBe(true);
    expect(manifest.metadata.boundary).toMatchObject({
      kind: 'generated-code',
      source: 'ae-ir',
      materialized: true,
      approvalScope,
    });
  });
});
