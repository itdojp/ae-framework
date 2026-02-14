import { mkdtempSync, rmSync, writeFileSync } from 'fs';
import { tmpdir } from 'os';
import { join } from 'path';
import { describe, expect, it } from 'vitest';
import { AESpecCompiler } from '../../../packages/spec-compiler/src/compiler.js';

describe('AESpecCompiler BIZ_001 regression', () => {
  it('extracts entity references from Business Rules and State Invariants', async () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'spec-compiler-biz001-'));
    const specPath = join(tempDir, 'spec.md');

    writeFileSync(
      specPath,
      `# CheckoutSpec

## Domain

### Order
- **id** (uuid, required) - Order ID
- **status** (string, required) - Current status

### Customer
- **id** (uuid, required) - Customer ID
- **email** (string, required) - Login email

## Business Rules
1. **BR-ORDER-001**: Order must always be linked to one Customer.

## State Invariants
- **INV-EMAIL-001**: Customer email must remain unique across all Customer records.
`,
      'utf-8',
    );

    const compiler = new AESpecCompiler();

    try {
      const ir = await compiler.compile({
        inputPath: specPath,
        validate: false,
      });

      const extractedEntities = new Set(
        (ir.invariants ?? []).flatMap((invariant) => invariant.entities ?? []),
      );

      expect(ir.invariants?.length).toBeGreaterThan(0);
      expect(extractedEntities).toEqual(new Set(['Order', 'Customer']));

      const lintResult = await compiler.lint(ir);
      const biz001Issues = lintResult.issues.filter((issue) => issue.id === 'BIZ_001');

      expect(biz001Issues).toHaveLength(0);
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
