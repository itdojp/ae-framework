import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = process.cwd();
const validateScript = resolve(repoRoot, 'scripts/discovery-pack/validate.mjs');
const schemaPath = resolve(repoRoot, 'schema/discovery-pack-v1.schema.json');

const VALID_DISCOVERY_PACK = `version: 1
profile: rdra-lite
sources:
  - id: SRC-1
    kind: interview-note
    path: spec/discovery-pack/sources/interview.md
actors:
  - id: ACTOR-1
    status: approved
    title: Operator
    source_refs: [SRC-1]
    traces_to: []
external_systems: []
goals:
  - id: GOAL-1
    status: approved
    title: Avoid overselling
    statement: Only approve feasible reservations.
    source_refs: [SRC-1]
    traces_to: []
requirements:
  - id: REQ-1
    status: approved
    title: Check stock
    statement: Check stock before approval.
    source_refs: [SRC-1]
    traces_to: [GOAL-1]
business_use_cases:
  - id: BUC-1
    status: approved
    title: Approve reservation
    statement: Operator approves a feasible reservation.
    source_refs: [SRC-1]
    traces_to: [REQ-1]
flows:
  - id: FLOW-1
    status: approved
    title: Approval flow
    mermaid_path: spec/discovery-pack/flows/approval-as-is.mmd
    source_refs: [SRC-1]
    traces_to: [BUC-1]
decisions: []
assumptions: []
open_questions: []
`;

describe('discovery-pack validate CLI', () => {
  let workdir: string;
  let reportDir: string;
  let sourceDir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'discovery-pack-validate-'));
    sourceDir = join(workdir, 'spec', 'discovery-pack');
    reportDir = join(workdir, 'artifacts', 'discovery-pack');
    await mkdir(join(sourceDir, 'flows'), { recursive: true });
    await mkdir(join(sourceDir, 'sources'), { recursive: true });
    await mkdir(reportDir, { recursive: true });
    await writeFile(join(sourceDir, 'sources', 'interview.md'), '# note\n', 'utf8');
    await writeFile(join(sourceDir, 'flows', 'approval-as-is.mmd'), 'flowchart TD\n  A-->B\n', 'utf8');
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  const runValidate = (args: string[] = []) =>
    spawnSync(
      process.execPath,
      [
        validateScript,
        '--sources',
        'spec/discovery-pack/**/*.{yml,yaml,json}',
        '--schema',
        schemaPath,
        '--output-dir',
        reportDir,
        ...args,
      ],
      {
        cwd: workdir,
        encoding: 'utf8',
      },
    );

  it('writes JSON and Markdown reports for a valid discovery pack', async () => {
    await writeFile(join(sourceDir, 'index.yaml'), VALID_DISCOVERY_PACK, 'utf8');

    const result = runValidate();
    expect(result.status).toBe(0);
    expect(result.stderr).toBe('');
    expect(existsSync(join(reportDir, 'discovery-pack-validate-report.json'))).toBe(true);
    expect(existsSync(join(reportDir, 'discovery-pack-validate-report.md'))).toBe(true);

    const report = JSON.parse(
      await readFile(join(reportDir, 'discovery-pack-validate-report.json'), 'utf8'),
    );
    expect(report.status).toBe('pass');
    expect(report.scannedFiles).toBe(1);
    expect(report.summary.unresolvedTraceRefs).toBe(0);
  });

  it('fails when fail-on blocking-open-questions matches', async () => {
    await writeFile(
      join(sourceDir, 'index.yaml'),
      VALID_DISCOVERY_PACK.replace(
        'open_questions: []',
        [
          'open_questions:',
          '  - id: OQ-1',
          '    status: reviewed',
          '    title: Pending approval path',
          '    question: Who owns the approval timeout policy?',
          '    blocking: true',
          '    source_refs: [SRC-1]',
          '    traces_to: [REQ-1]',
        ].join('\n'),
      ),
      'utf8',
    );

    const result = runValidate(['--fail-on', 'blocking-open-questions']);
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('fail-on condition matched: blocking-open-questions');

    const report = JSON.parse(
      await readFile(join(reportDir, 'discovery-pack-validate-report.json'), 'utf8'),
    );
    expect(report.summary.blockingOpenQuestions).toBe(1);
  });

  it('fails strict-approved when approved elements depend on reviewed targets', async () => {
    await writeFile(
      join(sourceDir, 'index.yaml'),
      VALID_DISCOVERY_PACK.replace('status: approved\n    title: Avoid overselling', 'status: reviewed\n    title: Avoid overselling'),
      'utf8',
    );

    const result = runValidate(['--strict-approved']);
    expect(result.status).toBe(1);

    const report = JSON.parse(
      await readFile(join(reportDir, 'discovery-pack-validate-report.json'), 'utf8'),
    );
    expect(report.summary.strictApprovedViolations).toBe(1);
  });

  it('escapes backslashes in markdown report cells', async () => {
    await writeFile(
      join(sourceDir, 'index.yaml'),
      VALID_DISCOVERY_PACK.replace('traces_to: [GOAL-1]', 'traces_to: [GOAL-1\\\\|trace]'),
      'utf8',
    );

    const result = runValidate();
    expect(result.status).toBe(1);

    const markdown = await readFile(join(reportDir, 'discovery-pack-validate-report.md'), 'utf8');
    expect(markdown).toMatch(/GOAL-1\\+\|trace/);
  });

  it('returns exit code 2 when no files match the provided sources', () => {
    const result = spawnSync(
      process.execPath,
      [
        validateScript,
        '--sources',
        'spec/discovery-pack/**/*.json',
        '--schema',
        schemaPath,
        '--output-dir',
        reportDir,
      ],
      {
        cwd: workdir,
        encoding: 'utf8',
      },
    );

    expect(result.status).toBe(2);
    expect(result.stderr).toContain('no discovery-pack files matched source patterns');
  });
});
