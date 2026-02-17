import { describe, expect, it } from 'vitest';

import {
  capitalize,
  generateFunctionImplementation,
  getFileExtension,
  getSourceDirectory,
  getTestDirectory,
  getTestExtension,
} from '../../../src/agents/code-generation-language';

describe('code-generation-language helpers', () => {
  it('generates TypeScript implementation and keeps return-related behavior comments', () => {
    const code = generateFunctionImplementation(
      'buildReport',
      ['should return a response object', 'logs metrics'],
      'typescript',
    );

    expect(code).toContain('export function buildReport');
    expect(code).toContain('// should return a response object');
    expect(code).toContain('return {};');
  });

  it('generates Phoenix controller for elixir+phoenix', () => {
    const code = generateFunctionImplementation('create_order', ['validates input'], 'elixir', 'phoenix');

    expect(code).toContain('use MyAppWeb, :controller');
    expect(code).toContain('def create_order(conn, _params) do');
  });

  it('falls back to TypeScript for unknown language', () => {
    const code = generateFunctionImplementation('unknownLangFn', [], 'kotlin');
    expect(code).toContain('export function unknownLangFn');
  });

  it('resolves file/test extensions and directories', () => {
    expect(getFileExtension('python')).toBe('py');
    expect(getFileExtension('unknown')).toBe('ts');
    expect(getTestExtension('elixir')).toBe('_test.exs');
    expect(getTestExtension('rust')).toBe('rs');
    expect(getSourceDirectory('go')).toBe('.');
    expect(getTestDirectory('go')).toBe('.');
  });

  it('capitalizes first character only', () => {
    expect(capitalize('helloWorld')).toBe('HelloWorld');
  });
});
