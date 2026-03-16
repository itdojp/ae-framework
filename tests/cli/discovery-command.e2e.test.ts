import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const repoRoot = resolve('.');
const tsxBin = resolve('node_modules/.bin/tsx');
const cliEntry = resolve('src/cli/index.ts');

const runCli = (args: string[], cwd: string = repoRoot) => {
  const env = {
    ...process.env,
    VITEST: '',
    NODE_ENV: 'production',
    AE_TEST_NO_EXIT: '0',
  };
  return spawnSync(tsxBin, [cliEntry, ...args], {
    encoding: 'utf8',
    timeout: 60_000,
    env,
    cwd,
  });
};

describe('discovery command e2e', () => {
  it('validates discovery-pack inputs through the CLI namespace', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-discovery-validate-'));
    try {
      mkdirSync(join(dir, 'spec', 'discovery-pack', 'flows'), { recursive: true });
      mkdirSync(join(dir, 'spec', 'discovery-pack', 'sources'), { recursive: true });
      writeFileSync(join(dir, 'spec', 'discovery-pack', 'sources', 'interview.md'), '# note\n', 'utf8');
      writeFileSync(join(dir, 'spec', 'discovery-pack', 'flows', 'approval-as-is.mmd'), 'flowchart TD\n  A-->B\n', 'utf8');
      writeFileSync(
        join(dir, 'spec', 'discovery-pack', 'index.yaml'),
        [
          'version: 1',
          'profile: rdra-lite',
          'sources:',
          '  - id: SRC-1',
          '    kind: interview-note',
          '    path: spec/discovery-pack/sources/interview.md',
          'actors:',
          '  - id: ACTOR-1',
          '    status: approved',
          '    title: Operator',
          '    source_refs: [SRC-1]',
          '    traces_to: []',
          'external_systems: []',
          'goals:',
          '  - id: GOAL-1',
          '    status: approved',
          '    title: Avoid overselling',
          '    statement: Only approve feasible reservations.',
          '    source_refs: [SRC-1]',
          '    traces_to: []',
          'requirements:',
          '  - id: REQ-1',
          '    status: approved',
          '    title: Check stock',
          '    statement: Check stock before approval.',
          '    source_refs: [SRC-1]',
          '    traces_to: [GOAL-1]',
          'business_use_cases:',
          '  - id: BUC-1',
          '    status: approved',
          '    title: Approve reservation',
          '    statement: Operator approves a feasible reservation.',
          '    source_refs: [SRC-1]',
          '    traces_to: [REQ-1]',
          'flows:',
          '  - id: FLOW-1',
          '    status: approved',
          '    title: Approval flow',
          '    mermaid_path: spec/discovery-pack/flows/approval-as-is.mmd',
          '    source_refs: [SRC-1]',
          '    traces_to: [BUC-1]',
          'decisions: []',
          'assumptions: []',
          'open_questions: []',
          '',
        ].join('\n'),
        'utf8',
      );

      const result = runCli(['discovery', 'validate', '--sources', 'spec/discovery-pack/**/*.{yml,yaml,json}'], dir);
      expect(result.status).toBe(0);
      expect(result.stdout).toContain('[discovery-pack] validation passed');

      const report = JSON.parse(
        readFileSync(join(dir, 'artifacts', 'discovery-pack', 'discovery-pack-validate-report.json'), 'utf8'),
      );
      expect(report.status).toBe('pass');
      expect(report.summary.duplicateIds).toBe(0);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('shows help for discovery validate', () => {
    const result = runCli(['discovery', 'validate', '--help']);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Validate Discovery Pack inputs');
    expect(result.stdout).toContain('--strict-approved');
    expect(result.stdout).toContain('--fail-on <rule>');
  });
});
