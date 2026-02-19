import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  ALLOWED_SCHEMA_ID_PREFIXES,
  isExecutedAsMain,
  runSchemaIdPolicyCheck,
  scanSchemaIdPolicy,
} from '../../../scripts/ci/check-schema-id-policy.mjs';

function withTempRepo(fn: (repoDir: string) => void): void {
  const repoDir = mkdtempSync(path.join(tmpdir(), 'ae-schema-id-policy-'));
  mkdirSync(path.join(repoDir, 'schema'));
  try {
    fn(repoDir);
  } finally {
    rmSync(repoDir, { recursive: true, force: true });
  }
}

function writeSchema(repoDir: string, fileName: string, json: Record<string, unknown>): void {
  const filePath = path.join(repoDir, 'schema', fileName);
  writeFileSync(filePath, JSON.stringify(json, null, 2));
}

function captureStdout(fn: () => void): string {
  const originalWrite = process.stdout.write;
  let output = '';
  process.stdout.write = ((chunk: unknown, encoding?: unknown, callback?: unknown) => {
    if (typeof chunk === 'string') {
      output += chunk;
    } else if (chunk) {
      output += Buffer.from(chunk as Uint8Array).toString(typeof encoding === 'string' ? encoding : undefined);
    }
    if (typeof callback === 'function') {
      callback();
    }
    return true;
  }) as typeof process.stdout.write;
  try {
    fn();
  } finally {
    process.stdout.write = originalWrite;
  }
  return output;
}

describe('check-schema-id-policy', () => {
  it('accepts schema IDs with allowed prefixes and matching filenames', () => {
    withTempRepo((repoDir) => {
      writeSchema(repoDir, 'alpha.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: `${ALLOWED_SCHEMA_ID_PREFIXES[0]}alpha.schema.json`,
        type: 'object',
      });
      writeSchema(repoDir, 'beta.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: `${ALLOWED_SCHEMA_ID_PREFIXES[1]}beta.schema.json`,
        type: 'object',
      });

      const result = scanSchemaIdPolicy(repoDir);
      expect(result.scannedFiles).toBe(2);
      expect(result.compliantFiles).toBe(2);
      expect(result.violations).toHaveLength(0);
      expect(result.violationCounts).toEqual({});
    });
  });

  it('reports missing IDs, disallowed prefixes, and filename mismatches', () => {
    withTempRepo((repoDir) => {
      writeSchema(repoDir, 'missing-id.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        type: 'object',
      });
      writeSchema(repoDir, 'bad-prefix.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: 'https://github.com/itdojp/ae-framework/schema/bad-prefix.schema.json',
        type: 'object',
      });
      writeSchema(repoDir, 'mismatch.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: `${ALLOWED_SCHEMA_ID_PREFIXES[0]}other.schema.json`,
        type: 'object',
      });
      writeSchema(repoDir, 'bad-ref.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: `${ALLOWED_SCHEMA_ID_PREFIXES[0]}bad-ref.schema.json`,
        type: 'object',
        properties: {
          nested: {
            allOf: [
              {
                $ref: 'https://github.com/itdojp/ae-framework/schema/bad-ref-target.schema.json',
              },
            ],
          },
        },
      });

      const result = scanSchemaIdPolicy(repoDir);
      expect(result.scannedFiles).toBe(4);
      expect(result.compliantFiles).toBe(0);
      expect(result.violations).toHaveLength(4);
      expect(result.violationCounts).toEqual({
        filename_mismatch: 1,
        invalid_ref_url: 1,
        invalid_prefix: 1,
        missing_id: 1,
      });
      expect(result.violations.map((violation) => violation.type).sort()).toEqual([
        'filename_mismatch',
        'invalid_prefix',
        'invalid_ref_url',
        'missing_id',
      ]);
    });
  });

  it('emits machine-readable summary when --format=json is set', () => {
    withTempRepo((repoDir) => {
      writeSchema(repoDir, 'valid.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: `${ALLOWED_SCHEMA_ID_PREFIXES[0]}valid.schema.json`,
        type: 'object',
      });
      writeSchema(repoDir, 'missing.schema.json', {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        type: 'object',
      });

      const output = captureStdout(() => {
        const result = runSchemaIdPolicyCheck([
          'node',
          'check-schema-id-policy.mjs',
          `--root=${repoDir}`,
          '--format=json',
        ]);
        expect(result.exitCode).toBe(1);
      });
      const parsed = JSON.parse(output);
      expect(parsed.scannedFiles).toBe(2);
      expect(parsed.compliantFiles).toBe(1);
      expect(parsed.violations).toHaveLength(1);
      expect(parsed.violationCounts.missing_id).toBe(1);
      expect(parsed.exitCode).toBe(1);
    });
  });

  it('treats URL-escaped module path and argv path as the same file', () => {
    const metaUrl = 'file:///tmp/with%20space/check-schema-id-policy.mjs';
    const argvPath = '/tmp/with space/check-schema-id-policy.mjs';
    expect(isExecutedAsMain(metaUrl, argvPath)).toBe(true);
  });
});
