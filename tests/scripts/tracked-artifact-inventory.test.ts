import { describe, expect, it } from 'vitest';

import {
  buildInventory,
  classifyArtifact,
  parseArgs,
  proposePlacement,
  renderMarkdown,
} from '../../scripts/maintenance/tracked-artifact-inventory.mjs';

describe('tracked-artifact-inventory', () => {
  it('accepts pnpm forwarded separator and validates required option values', () => {
    expect(parseArgs(['--', '--output-json', 'tmp/out.json', '--output-md', 'tmp/out.md'])).toEqual({
      outputJson: 'tmp/out.json',
      outputMd: 'tmp/out.md',
    });
    expect(() => parseArgs(['--output-json'])).toThrow('--output-json requires a value');
    expect(() => parseArgs(['--output-json', '--output-md'])).toThrow('--output-json requires a value');
  });

  it('classifies tracked artifacts by current taxonomy', () => {
    expect(classifyArtifact('artifacts/types/index.d.ts')).toBe('committed-contract');
    expect(classifyArtifact('artifacts/archive/2025/manual-verify.md')).toBe('archive');
    expect(classifyArtifact('artifacts/codex/2026-02-03/env.txt')).toBe('local-debug-archive');
    expect(classifyArtifact('artifacts/bench.json')).toBe('reference-snapshot');
    expect(classifyArtifact('artifacts/reference/benchmarks/bench.json')).toBe('reference-snapshot');
  });

  it('proposes normalized placement for root-level reference snapshots and keeps normalized paths stable', () => {
    expect(proposePlacement('artifacts/bench.json')).toEqual({
      action: 'move',
      target: 'artifacts/reference/benchmarks/bench.json',
      rationale: 'tracked benchmark baseline at root should move under reference snapshots',
    });
    expect(proposePlacement('artifacts/reference/benchmarks/bench.json')).toEqual({
      action: 'keep',
      target: 'artifacts/reference/benchmarks/bench.json',
      rationale: 'normalized reference snapshot',
    });
    expect(proposePlacement('artifacts/verify.md')).toEqual({
      action: 'move',
      target: 'artifacts/reference/verify/verify.md',
      rationale: 'tracked verification snapshot should move under reference snapshots',
    });
    expect(proposePlacement('artifacts/reference/verify/verify.md')).toEqual({
      action: 'keep',
      target: 'artifacts/reference/verify/verify.md',
      rationale: 'normalized reference snapshot',
    });
    expect(proposePlacement('artifacts/types-gate-ci-validation.md')).toEqual({
      action: 'move',
      target: 'artifacts/reference/types/types-gate-ci-validation.md',
      rationale: 'tracked type/reference snapshot should live under a typed reference namespace',
    });
    expect(proposePlacement('artifacts/reference/types/types-gate-ci-validation.md')).toEqual({
      action: 'keep',
      target: 'artifacts/reference/types/types-gate-ci-validation.md',
      rationale: 'normalized reference snapshot',
    });
    expect(proposePlacement('artifacts/types-hardening-validation.md')).toEqual({
      action: 'move',
      target: 'artifacts/reference/types/types-hardening-validation.md',
      rationale: 'tracked type/reference snapshot should live under a typed reference namespace',
    });
    expect(proposePlacement('artifacts/reference/types/types-hardening-validation.md')).toEqual({
      action: 'keep',
      target: 'artifacts/reference/types/types-hardening-validation.md',
      rationale: 'normalized reference snapshot',
    });
    expect(proposePlacement('artifacts/public-types.current.d.ts')).toEqual({
      action: 'keep',
      target: 'artifacts/public-types.current.d.ts',
      rationale: 'consumer-facing committed contract artifact',
    });
  });

  it('builds inventory summary and markdown output', () => {
    const report = buildInventory([
      'artifacts/reference/benchmarks/bench.json',
      'artifacts/archive/2025/manual-verify.md',
      'artifacts/types/index.d.ts',
      'artifacts/codex/2026-02-03/env.txt',
    ]);

    expect(report.summary).toMatchObject({
      total: 4,
      'reference-snapshot': 1,
      archive: 1,
      'committed-contract': 1,
      'local-debug-archive': 1,
      keepCount: 4,
    });
    expect(report.topLevelTracked).toEqual([]);

    const markdown = renderMarkdown(report);
    expect(markdown).toContain('# Tracked Artifact Inventory');
    expect(markdown).toContain('## Move candidates');
    expect(markdown).not.toContain('tracked benchmark baseline at root should move under reference snapshots');
  });
});
