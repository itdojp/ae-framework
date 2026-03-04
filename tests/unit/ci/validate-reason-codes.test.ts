import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import yaml from 'yaml';
import {
  collectEmitReasonCodes,
  runReasonCodeValidation,
  validateReasonCodesPolicy,
} from '../../../scripts/ci/validate-reason-codes.mjs';

describe('validate-reason-codes', () => {
  it('accepts current reason code registry and emitted mappings', () => {
    const result = validateReasonCodesPolicy('policy/reason-codes.yml');
    expect(result.violations).toHaveLength(0);
    expect(result.missingEmitCodes).toHaveLength(0);

    const emittedCodes = collectEmitReasonCodes();
    expect(emittedCodes.length).toBeGreaterThan(0);
    expect(result.registryCodes).toEqual(expect.arrayContaining(emittedCodes));
  });

  it('fails when an emitted reason code is missing from the registry', async () => {
    const workdir = await mkdtemp(join(tmpdir(), 'reason-codes-policy-'));
    try {
      const sourceRaw = await readFile('policy/reason-codes.yml', 'utf8');
      const source = yaml.parse(sourceRaw) as { codes?: Array<{ code?: string }> };
      source.codes = (source.codes ?? []).filter((entry) => String(entry?.code ?? '').trim() !== 'autopilot.unknown');

      const policyPath = join(workdir, 'reason-codes.yml');
      await writeFile(policyPath, yaml.stringify(source), 'utf8');

      const result = validateReasonCodesPolicy(policyPath);
      expect(result.violations.some((item) => item.type === 'missing_emitted_code')).toBe(true);
      expect(result.missingEmitCodes).toContain('autopilot.unknown');
    } finally {
      await rm(workdir, { recursive: true, force: true });
    }
  });

  it('detects invalid format and duplicate definitions', async () => {
    const workdir = await mkdtemp(join(tmpdir(), 'reason-codes-policy-invalid-'));
    try {
      const payload = {
        schemaVersion: '1.0.0',
        contractId: 'reason-code-registry.v1',
        codes: [
          {
            code: 'policy.required_labels_missing',
            title: 'valid',
            description: 'valid',
            ownerHint: 'human',
            category: 'policy',
          },
          {
            code: 'policy.required_labels_missing',
            title: 'duplicate',
            description: 'duplicate',
            ownerHint: 'human',
            category: 'policy',
          },
          {
            code: 'INVALID-CODE',
            title: '',
            description: '',
            ownerHint: 'robot',
            category: '',
          },
        ],
      };

      const policyPath = join(workdir, 'reason-codes.yml');
      await writeFile(policyPath, yaml.stringify(payload), 'utf8');

      const result = validateReasonCodesPolicy(policyPath);
      const violationTypes = result.violations.map((item) => item.type);
      expect(violationTypes).toContain('duplicate_code');
      expect(violationTypes).toContain('invalid_code_format');
      expect(violationTypes).toContain('missing_title');
      expect(violationTypes).toContain('missing_description');
      expect(violationTypes).toContain('invalid_owner_hint');
      expect(violationTypes).toContain('missing_category');
    } finally {
      await rm(workdir, { recursive: true, force: true });
    }
  });

  it('returns machine-readable output for --format=json', () => {
    const originalWrite = process.stdout.write;
    let output = '';
    process.stdout.write = ((chunk: unknown) => {
      output += String(chunk ?? '');
      return true;
    }) as typeof process.stdout.write;

    try {
      const result = runReasonCodeValidation([
        'node',
        'validate-reason-codes.mjs',
        '--policy=policy/reason-codes.yml',
        '--format=json',
      ]);
      expect(result.exitCode).toBe(0);
      const parsed = JSON.parse(output) as {
        exitCode: number;
        emittedCodes: string[];
      };
      expect(parsed.exitCode).toBe(0);
      expect(parsed.emittedCodes.length).toBeGreaterThan(0);
    } finally {
      process.stdout.write = originalWrite;
    }
  });
});
