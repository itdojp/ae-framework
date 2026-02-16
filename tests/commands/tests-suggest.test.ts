import { describe, it, expect, vi } from 'vitest';
import { mkdtempSync, writeFileSync, readFileSync } from 'fs';
import os from 'os';
import path from 'path';
import {
  applyTestsSuggestTemplateVariables,
  buildTestsSuggestOutput,
  resolveTestsTemplate,
  resolveTestsSuggestTemplateVariables,
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

  it('expands auth template placeholders from structured input text', () => {
    const template = [
      'intent={intent}',
      'auth={auth_type}',
      'roles={roles}',
      'resources={resources}',
    ].join('\n');
    const text = [
      'intent: Build access control tests',
      'auth_type: JWT',
      'roles: admin, auditor',
      'resources: /orders, /invoices',
    ].join('\n');

    const output = buildTestsSuggestOutput(template, text);
    expect(output).toContain('auth=JWT');
    expect(output).toContain('roles=admin, auditor');
    expect(output).toContain('resources=/orders, /invoices');
    expect(output).not.toContain('{intent}');
    expect(output).not.toContain('{auth_type}');
    expect(output).not.toContain('{roles}');
    expect(output).not.toContain('{resources}');
  });

  it('infers auth placeholders from free-form text when structured keys are missing', () => {
    const variables = resolveTestsSuggestTemplateVariables(
      'Use JWT and allow admin user to manage /products.',
    );

    expect(variables.auth_type).toBe('JWT');
    expect(variables.roles).toContain('admin');
    expect(variables.roles).toContain('user');
    expect(variables.resources).toContain('/products');
  });

  it('uses a single-line summary for {intent} in free-form multi-line input', () => {
    const variables = resolveTestsSuggestTemplateVariables(
      [
        '',
        'Enable JWT access control for order APIs',
        'Include admin and auditor permissions for /orders.',
      ].join('\n'),
    );

    expect(variables.intent).toBe('Enable JWT access control for order APIs');
    expect(variables.intent).not.toContain('\n');
  });

  it('keeps missing fields as fallback when structured hints are provided', () => {
    const variables = resolveTestsSuggestTemplateVariables(
      [
        'auth_type: JWT',
        'roles: admin',
      ].join('\n'),
    );

    expect(variables.intent).toBe('unspecified');
    expect(variables.auth_type).toBe('JWT');
    expect(variables.roles).toBe('admin');
    expect(variables.resources).toBe('unspecified');
  });

  it('fills missing placeholder values with fallback text', () => {
    const output = applyTestsSuggestTemplateVariables(
      'auth={auth_type} roles={roles} resources={resources} intent={intent}',
      {
        intent: 'unspecified',
        auth_type: 'unspecified',
        roles: 'unspecified',
        resources: 'unspecified',
      },
    );
    expect(output).toBe('auth=unspecified roles=unspecified resources=unspecified intent=unspecified');
  });
});
