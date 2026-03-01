import { describe, expect, it } from 'vitest';

import {
  generateContractsFromFormalSpec,
  parseFormalSpec,
} from '../../../src/agents/contracts-generator';

const byPath = (files: Array<{ path: string; content: string }>, suffix: string): string => {
  const match = files.find((file) => file.path.endsWith(suffix));
  if (!match) {
    throw new Error(`Missing generated file: ${suffix}`);
  }
  return match.content;
};

describe('contracts-generator', () => {
  it('generates schemas, conditions, and state transitions from explicit directives', () => {
    const spec = [
      '@input object',
      '@output number',
      '@pre input != null',
      '@post output != null',
      '@state Init|Validated|Done',
      '@transition Init -> Validated if input != null',
      '@transition Validated -> Done if output != null',
    ].join('\n');

    const parsed = parseFormalSpec(spec);
    expect(parsed.inputType).toBe('object');
    expect(parsed.outputType).toBe('number');
    expect(parsed.states).toEqual(['Init', 'Validated', 'Done']);
    expect(parsed.transitions).toHaveLength(2);
    expect(parsed.warnings).toHaveLength(0);

    const files = generateContractsFromFormalSpec(spec);
    const schemas = byPath(files, 'schemas.ts');
    const conditions = byPath(files, 'conditions.ts');
    const machine = byPath(files, 'machine.ts');

    expect(schemas).toContain('export const InputSchema = z.record(z.unknown())');
    expect(schemas).toContain('export const OutputSchema = z.number()');
    expect(conditions).toContain("import { InputSchema, OutputSchema } from './schemas'");
    expect(conditions).toContain('InputSchema.safeParse(input).success');
    expect(conditions).toContain('OutputSchema.safeParse(output).success');
    expect(machine).toContain("export type State = 'Init' | 'Validated' | 'Done'");
    expect(machine).toContain("Init: [{ to: 'Validated' as State");
  });

  it('falls back to heuristic extraction with explicit warnings when directives are missing', () => {
    const spec = [
      '---- MODULE Sample ----',
      'TypeOK == x \\in Nat',
      'Pre == input != null',
      'Post == output != null',
      'state \\in {"Init", "Done"}',
    ].join('\n');

    const parsed = parseFormalSpec(spec);
    expect(parsed.preconditions).toContain('input != null');
    expect(parsed.postconditions).toContain('output != null');
    expect(parsed.states).toContain('Init');
    expect(parsed.states).toContain('Done');
    expect(parsed.warnings.join('\n')).toContain('No explicit @input/@output/@pre/@post/@state directives');

    const files = generateContractsFromFormalSpec(spec);
    const schemas = byPath(files, 'schemas.ts');
    const conditions = byPath(files, 'conditions.ts');
    expect(schemas).toContain('export const InputSchema = z.unknown()');
    expect(schemas).toContain('export const OutputSchema = z.unknown()');
    expect(conditions).not.toContain('return true;');
  });

  it('keeps unsupported directives visible as generation warnings', () => {
    const spec = [
      '@input uuid',
      '@output object',
      '@state Init,Done',
    ].join('\n');

    const files = generateContractsFromFormalSpec(spec);
    const schemas = byPath(files, 'schemas.ts');
    const machine = byPath(files, 'machine.ts');

    expect(schemas).toContain('Unsupported @input type: uuid');
    expect(schemas).toContain('Input type could not be inferred; using z.unknown().');
    expect(machine).toContain("Init: [{ to: 'Done' as State, condition: \"default-sequence\" }]");
  });
});
