import { describe, expect, it } from 'vitest';
import { parseArgs } from '../../examples/temporal-workflow-adapter/src/cli-options.js';

describe('Temporal Workflow adapter CLI options', () => {
  it('accepts the pnpm argument separator before documented options', () => {
    const options = parseArgs([
      'start',
      '--',
      '--workflow-id',
      'ae-assurance-restart-demo',
      '--scenario',
      'inventory-waiver',
      '--output-dir',
      'artifacts/temporal-restart-drill/inventory-waiver',
      '--restart-validation-status',
      'manual-pass',
      '--no-wait',
    ]);

    expect(options.command).toBe('start');
    expect(options.workflowId).toBe('ae-assurance-restart-demo');
    expect(options.scenario).toBe('inventory-waiver');
    expect(options.outputDir).toBe('artifacts/temporal-restart-drill/inventory-waiver');
    expect(options.restartValidationStatus).toBe('manual-pass');
    expect(options.prNumber).toBe(null);
    expect(options.wait).toBe(false);
  });

  it('preserves validation for options after the pnpm argument separator', () => {
    expect(() => parseArgs(['start', '--', '--pr-number', 'not-a-number'])).toThrow(
      '--pr-number requires a positive integer',
    );
  });
});
