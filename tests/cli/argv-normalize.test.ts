import { describe, expect, it } from 'vitest';
import { normalizeProgramArgv } from '../../src/cli/argv-normalize.js';

describe('normalizeProgramArgv', () => {
  it('removes leading standalone separator for direct invocation', () => {
    const argv = [
      'node',
      'src/cli/index.ts',
      '--',
      'validate',
      '--traceability',
      '--sources',
      'spec/example-spec.md',
    ];

    expect(normalizeProgramArgv(argv, {})).toEqual([
      'node',
      'src/cli/index.ts',
      'validate',
      '--traceability',
      '--sources',
      'spec/example-spec.md',
    ]);
  });

  it('removes pnpm separator before options', () => {
    const argv = [
      'node',
      'src/cli/index.ts',
      'spec',
      'validate',
      '--',
      '-i',
      'spec/example-spec.md',
      '--output',
      '.ae/ae-ir.json',
    ];

    expect(
      normalizeProgramArgv(argv, { npm_lifecycle_event: 'spec:validate' }),
    ).toEqual([
      'node',
      'src/cli/index.ts',
      'spec',
      'validate',
      '-i',
      'spec/example-spec.md',
      '--output',
      '.ae/ae-ir.json',
    ]);
  });

  it('keeps argv unchanged when no separator exists', () => {
    const argv = [
      'node',
      'src/cli/index.ts',
      'spec',
      'validate',
      '-i',
      'spec/example-spec.md',
    ];

    expect(normalizeProgramArgv(argv)).toEqual(argv);
  });

  it('keeps argv unchanged for direct CLI invocation', () => {
    const argv = [
      'node',
      'src/cli/index.ts',
      'sm',
      'validate',
      '--',
      '-input.sm.json',
    ];

    expect(normalizeProgramArgv(argv, {})).toEqual(argv);
  });

  it('removes forwarded separator when invoked via package script', () => {
    const argv = [
      'node',
      'src/cli/index.ts',
      'quality',
      'run',
      '--',
      '--env=testing',
      '--gates=dod',
    ];

    expect(
      normalizeProgramArgv(argv, { npm_lifecycle_event: 'quality:run' }),
    ).toEqual([
      'node',
      'src/cli/index.ts',
      'quality',
      'run',
      '--env=testing',
      '--gates=dod',
    ]);
  });

  it('keeps argv unchanged when separator is not followed by options', () => {
    const argv = [
      'node',
      'src/cli/index.ts',
      'spec',
      'validate',
      '--',
      'literal-value',
    ];

    expect(normalizeProgramArgv(argv)).toEqual(argv);
  });
});
