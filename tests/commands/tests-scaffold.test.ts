import { afterEach, describe, it, expect } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'fs';
import os from 'os';
import path from 'path';
import {
  createScaffoldFiles,
  extractAcceptanceCriteria,
  testsScaffold,
} from '../../src/commands/tdd/scaffold.js';

const tempDirs: string[] = [];

function createTempDir(): string {
  const dir = mkdtempSync(path.join(os.tmpdir(), 'tests-scaffold-'));
  tempDirs.push(dir);
  return dir;
}

afterEach(() => {
  for (const dir of tempDirs) {
    rmSync(dir, { recursive: true, force: true });
  }
  tempDirs.length = 0;
});

describe('tests:scaffold helpers', () => {
  it('extracts acceptance criteria from Acceptance section bullets', () => {
    const markdown = [
      '# Spec',
      '',
      '## 3. Acceptance Criteria (AC)',
      '- AC-1: user can create order',
      '- AC-2: Given valid input When submit Then returns 201',
      '',
      '## 4. NFR',
      '- latency < 200ms',
      '',
    ].join('\n');

    const criteria = extractAcceptanceCriteria(markdown);
    expect(criteria).toEqual([
      'user can create order',
      'Given valid input When submit Then returns 201',
    ]);
  });

  it('creates scaffold file entries from extracted criteria', () => {
    const markdown = [
      '# Plan',
      '',
      '## Acceptance',
      '- AC-1: Given cart exists When checkout Then order is created',
      '- AC-2: payment error is shown',
    ].join('\n');

    const files = createScaffoldFiles(markdown, 'checkout-flow');
    const paths = files.map((f) => f.relativePath);

    expect(paths).toContain(path.join('bdd', 'checkout-flow.feature'));
    expect(paths).toContain('checkout-flow.acceptance.md');
    expect(paths).toContain(path.join('property', 'checkout-flow.property.test.ts'));
    expect(paths).toContain(path.join('contract', 'checkout-flow.contract.test.ts'));
    expect(paths).toContain(path.join('regression', 'checkout-flow.regression.test.ts'));

    const feature = files.find((f) => f.relativePath.endsWith('.feature'))?.content ?? '';
    expect(feature).toContain('Scenario: AC-1: Given cart exists When checkout Then order is created');
    expect(feature).toContain('Given cart exists');
    expect(feature).toContain('When checkout');
    expect(feature).toContain('Then order is created');

    const property = files.find((f) => f.relativePath.endsWith('.property.test.ts'))?.content ?? '';
    expect(property).toContain('NEXT: Replace this placeholder with meaningful properties.');

    const contract = files.find((f) => f.relativePath.endsWith('.contract.test.ts'))?.content ?? '';
    expect(contract).toContain("describe('contract:checkout-flow', () => {");

    const regression = files.find((f) => f.relativePath.endsWith('.regression.test.ts'))?.content ?? '';
    expect(regression).toContain("describe('regression:checkout-flow', () => {");
  });

  it('writes scaffold files to disk', () => {
    const tempDir = createTempDir();
    const inputPath = path.join(tempDir, 'sample.md');
    const outputDir = path.join(tempDir, 'out');
    writeFileSync(
      inputPath,
      ['# Spec', '', '## Acceptance', '- AC-1: user can login'].join('\n'),
      'utf8',
    );

    testsScaffold({
      input: inputPath,
      out: outputDir,
      specId: 'auth-login',
      property: true,
      overwrite: true,
    });

    const featurePath = path.join(outputDir, 'bdd', 'auth-login.feature');
    const mapPath = path.join(outputDir, 'auth-login.acceptance.md');
    const propertyPath = path.join(outputDir, 'property', 'auth-login.property.test.ts');
    const contractPath = path.join(outputDir, 'contract', 'auth-login.contract.test.ts');
    const regressionPath = path.join(outputDir, 'regression', 'auth-login.regression.test.ts');

    expect(readFileSync(featurePath, 'utf8')).toContain('Feature: auth-login');
    expect(readFileSync(mapPath, 'utf8')).toContain('AC-1');
    expect(readFileSync(propertyPath, 'utf8')).toContain('fast-check');
    expect(readFileSync(contractPath, 'utf8')).toContain('contract:auth-login');
    expect(readFileSync(regressionPath, 'utf8')).toContain('regression:auth-login');
  });

  it('does not fall back to global bullets when Acceptance heading exists', () => {
    const markdown = [
      '# Spec',
      '',
      '## Acceptance Criteria',
      '- AC-1:',
      '',
      '## NFR',
      '- latency < 200ms',
      '- AC-99: not an acceptance item',
    ].join('\n');

    expect(extractAcceptanceCriteria(markdown)).toEqual([]);
  });

  it('keeps nested Given/When/Then bullets inside one AC', () => {
    const markdown = [
      '# Spec',
      '',
      '## Acceptance',
      '- AC-1:',
      '  - Given user is logged in',
      '  - Given cart has items',
      '  - When checkout is submitted',
      '  - Then order is created',
      '- AC-2: payment error is shown',
    ].join('\n');

    expect(extractAcceptanceCriteria(markdown)).toEqual([
      'Given user is logged in Given cart has items When checkout is submitted Then order is created',
      'payment error is shown',
    ]);
  });

  it('preserves multiple Given clauses when splitting GWT', () => {
    const markdown = [
      '# Spec',
      '',
      '## Acceptance',
      '- AC-1: Given user is logged in Given cart has items When checkout Then order is created',
    ].join('\n');

    const files = createScaffoldFiles(markdown, 'checkout-flow', {
      property: false,
      contract: false,
      regression: false,
    });
    const feature = files.find((f) => f.relativePath.endsWith('.feature'))?.content ?? '';

    expect(feature).toContain('Given user is logged in Given cart has items');
    expect(feature).toContain('When checkout');
    expect(feature).toContain('Then order is created');
  });

  it('fails when no acceptance bullets are found', () => {
    expect(() => createScaffoldFiles('# Empty', 'empty')).toThrowError(
      /No acceptance criteria bullets found/,
    );
  });

  it('can skip contract and regression scaffold generation', () => {
    const markdown = [
      '# Spec',
      '',
      '## Acceptance',
      '- AC-1: user can login',
    ].join('\n');

    const files = createScaffoldFiles(markdown, 'auth-login', {
      contract: false,
      regression: false,
    });
    const paths = files.map((f) => f.relativePath);

    expect(paths).toContain(path.join('property', 'auth-login.property.test.ts'));
    expect(paths).not.toContain(path.join('contract', 'auth-login.contract.test.ts'));
    expect(paths).not.toContain(path.join('regression', 'auth-login.regression.test.ts'));
  });
});
