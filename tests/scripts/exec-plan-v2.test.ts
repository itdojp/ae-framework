import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { join, resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';

import {
  main,
  parseArgs,
  renderExecPlanMarkdown,
  validateExecPlanV2Payload,
} from '../../scripts/exec-plan/validate-v2.mjs';

const schema = JSON.parse(readFileSync(resolve('schema/exec-plan.v2.schema.json'), 'utf8'));
const validFixturePaths = [
  'fixtures/exec-plan/baseline.exec-plan.v2.json',
  'fixtures/exec-plan/structured-assurance.exec-plan.v2.json',
  'fixtures/exec-plan/high-risk-selected-claims.exec-plan.v2.json',
  'fixtures/spec-kit/greenfield/expected/exec-plan.v2.json',
  'fixtures/spec-kit/brownfield/expected/exec-plan.v2.json',
];

function readJson(path: string) {
  return JSON.parse(readFileSync(resolve(path), 'utf8'));
}

describe('exec-plan/v2 contract', () => {
  it('accepts all valid fixtures through schema and semantic validation', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    for (const fixturePath of validFixturePaths) {
      const fixture = readJson(fixturePath);
      expect(validate(fixture), fixturePath).toBe(true);
      expect(validateExecPlanV2Payload(fixture, schema), fixturePath).toMatchObject({
        result: 'pass',
        semanticErrors: [],
        schemaErrors: [],
      });
    }
  });

  it('rejects intentionally invalid semantic references with actionable messages', () => {
    const fixture = readJson('fixtures/exec-plan/invalid.missing-evidence-ref.exec-plan.v2.json');
    const report = validateExecPlanV2Payload(fixture, schema);

    expect(report.result).toBe('fail');
    expect(report.schemaErrors).toEqual([]);
    expect(report.semanticErrors.join('\n')).toContain('taskGraph.nodes[0] (task.contract).evidenceRequirementRefs');
    expect(report.semanticErrors.join('\n')).toContain('unknown evidence requirement id: ev.missing-contract');
  });

  it('renders Markdown suitable for GitHub issue and PR bodies', () => {
    const fixture = readJson('fixtures/exec-plan/high-risk-selected-claims.exec-plan.v2.json');
    const markdown = renderExecPlanMarkdown(fixture);

    expect(markdown).toContain('# ExecPlan v2: High-risk selected-claims ExecPlan v2');
    expect(markdown).toContain('## Task graph');
    expect(markdown).toContain('## Evidence requirements');
    expect(markdown).toContain('`cmd.policy-gate`');
    expect(markdown).toContain('`artifact.policy-gate-summary`');
    expect(markdown).toContain('manual-approval-or-block');
  });

  it('renders Spec Kit references when a plan carries bridge context', () => {
    const fixture = readJson('fixtures/exec-plan/structured-assurance.exec-plan.v2.json');
    const markdown = renderExecPlanMarkdown(fixture);

    expect(markdown).toContain('### Spec Kit references');
    expect(markdown).toContain('spec-kit-spec');
    expect(markdown).toContain('fixtures/spec-kit/greenfield/specs/001-reservation-approval/spec.md');
  });

  it('keeps embedded validation commands pointed at the scenario fixture being reviewed', () => {
    for (const fixturePath of validFixturePaths) {
      const fixture = readJson(fixturePath);
      const commands = [
        ...fixture.verificationProfile.commands,
        ...fixture.taskGraph.nodes.flatMap((node: { commands?: unknown[] }) => node.commands ?? []),
      ].filter((command: { command?: string }) => command.command?.includes('exec-plan:v2:validate'));

      expect(commands.length, fixturePath).toBeGreaterThan(0);
      for (const command of commands) {
        expect(command.command, fixturePath).toContain(`--file ${fixturePath}`);
      }
    }
  });

  it('writes validation report JSON and rendered Markdown through the CLI', () => {
    const root = resolve('.codex-local/tmp');
    mkdirSync(root, { recursive: true });
    const sandbox = mkdtempSync(join(root, 'exec-plan-v2-'));
    try {
      const outputJson = join(sandbox, 'report.json');
      const outputMd = join(sandbox, 'plan.md');
      const exitCode = main([
        'node',
        'scripts/exec-plan/validate-v2.mjs',
        '--file',
        'fixtures/exec-plan/baseline.exec-plan.v2.json',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(exitCode).toBe(0);
      expect(existsSync(outputJson)).toBe(true);
      expect(existsSync(outputMd)).toBe(true);
      expect(readJson(outputJson)).toMatchObject({ result: 'pass', planId: 'reval3-003-baseline-fast-lane' });
      expect(readFileSync(outputMd, 'utf8')).toContain('## Verification profile');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('treats -- as the end of validator options', () => {
    const options = parseArgs([
      'node',
      'scripts/exec-plan/validate-v2.mjs',
      '--file',
      'fixtures/exec-plan/baseline.exec-plan.v2.json',
      '--',
      '--not-a-validator-option',
    ]);

    expect(options.inputPath).toBe('fixtures/exec-plan/baseline.exec-plan.v2.json');
  });

  it('skips the leading pnpm argument separator before validator options', () => {
    const options = parseArgs([
      'node',
      'scripts/exec-plan/validate-v2.mjs',
      '--',
      '--file',
      'fixtures/exec-plan/high-risk-selected-claims.exec-plan.v2.json',
    ]);

    expect(options.inputPath).toBe('fixtures/exec-plan/high-risk-selected-claims.exec-plan.v2.json');
  });
});
