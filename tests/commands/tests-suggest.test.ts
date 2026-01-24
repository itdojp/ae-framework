import { describe, it, expect, vi } from 'vitest';
import { mkdtempSync, writeFileSync, readFileSync } from 'fs';
import os from 'os';
import path from 'path';
import {
  buildTestsSuggestOutput,
  resolveTestsTemplate,
  testsSuggest,
} from '../../src/commands/tdd/suggest.js';

describe('tests:suggest helpers', () => {
  it('builds output with intent header when provided', () => {
    const output = buildTestsSuggestOutput('TEMPLATE', 'Sample intent');
    expect(output).toContain('# Intent');
    expect(output).toContain('Sample intent');
    expect(output).toContain('TEMPLATE');
  });

  it('resolves built-in templates by name', () => {
    const templatePath = resolveTestsTemplate('http-api');
    expect(templatePath).toContain(path.join('templates', 'prompts'));
  });

  it('includes available templates and searched paths in error', () => {
    expect(() => resolveTestsTemplate('missing-template')).toThrowError(
      /Available templates:/,
    );
  });

  it('warns when both input and intent are provided', () => {
    const tempDir = mkdtempSync(path.join(os.tmpdir(), 'tests-suggest-'));
    const inputPath = path.join(tempDir, 'intent.txt');
    const outputPath = path.join(tempDir, 'prompt.md');
    writeFileSync(inputPath, 'From file', 'utf8');

    const warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});
    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    testsSuggest({
      template: 'http-api',
      input: inputPath,
      intent: 'Inline intent',
      output: outputPath,
    });

    expect(warnSpy).toHaveBeenCalled();
    const output = readFileSync(outputPath, 'utf8');
    expect(output).toContain('From file');

    warnSpy.mockRestore();
    logSpy.mockRestore();
  });
});
