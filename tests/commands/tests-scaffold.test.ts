import { describe, it, expect } from 'vitest';
import { mkdtempSync, readFileSync, writeFileSync } from 'fs';
import os from 'os';
import path from 'path';
import {
  createScaffoldFiles,
  extractAcceptanceCriteria,
  testsScaffold,
} from '../../src/commands/tdd/scaffold.js';

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

    const files = createScaffoldFiles(markdown, 'checkout-flow', true);
    const paths = files.map((f) => f.relativePath);

    expect(paths).toContain(path.join('bdd', 'checkout-flow.feature'));
    expect(paths).toContain('checkout-flow.acceptance.md');
    expect(paths).toContain(path.join('property', 'checkout-flow.property.test.ts'));

    const feature = files.find((f) => f.relativePath.endsWith('.feature'))?.content ?? '';
    expect(feature).toContain('Scenario: AC-1: Given cart exists When checkout Then order is created');
    expect(feature).toContain('Given cart exists');
    expect(feature).toContain('When checkout');
    expect(feature).toContain('Then order is created');
  });

  it('writes scaffold files to disk', () => {
    const tempDir = mkdtempSync(path.join(os.tmpdir(), 'tests-scaffold-'));
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

    expect(readFileSync(featurePath, 'utf8')).toContain('Feature: auth-login');
    expect(readFileSync(mapPath, 'utf8')).toContain('AC-1');
    expect(readFileSync(propertyPath, 'utf8')).toContain('fast-check');
  });

  it('fails when no acceptance bullets are found', () => {
    expect(() => createScaffoldFiles('# Empty', 'empty')).toThrowError(
      /No acceptance criteria bullets found/,
    );
  });
});
