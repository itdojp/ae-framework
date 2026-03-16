import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync, readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';

import { testsScaffold } from '../../../src/commands/tdd/scaffold.js';

const repoRoot = process.cwd();
const compileScript = resolve(repoRoot, 'scripts/discovery-pack/compile.mjs');
const discoverySchemaPath = resolve(repoRoot, 'schema/discovery-pack-v1.schema.json');
const contextPackSchema = JSON.parse(
  readFileSync(resolve(repoRoot, 'schema/context-pack-v1.schema.json'), 'utf8'),
);

const DISCOVERY_PACK = `version: 1
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
external_systems:
  - id: EXT-ERP
    status: approved
    title: ERP
    source_refs: [SRC-1]
    traces_to: []
goals:
  - id: GOAL-1
    status: approved
    title: Avoid overselling
    statement: Approval should only proceed when stock can be reserved.
    source_refs: [SRC-1]
    traces_to: []
requirements:
  - id: REQ-1
    status: approved
    title: Check reservation feasibility
    statement: Approval must confirm reservation feasibility before final approval.
    source_refs: [SRC-1]
    traces_to: [GOAL-1]
  - id: REQ-2
    status: reviewed
    title: Show rejection reason
    statement: Operator should see a rejection reason code.
    source_refs: [SRC-1]
    traces_to: [GOAL-1]
business_use_cases:
  - id: BUC-1
    status: approved
    title: Approve reservation request
    statement: The operator confirms a request only when reservation is feasible.
    actor_ids: [ACTOR-1]
    primary_goal_ids: [GOAL-1]
    source_refs: [SRC-1]
    traces_to: [REQ-1]
flows:
  - id: FLOW-1
    status: approved
    title: Approval as-is
    mermaid_path: spec/discovery-pack/flows/approval-as-is.mmd
    kind: as-is
    source_refs: [SRC-1]
    traces_to: [BUC-1]
  - id: FLOW-2
    status: approved
    title: Approval to-be
    mermaid_path: spec/discovery-pack/flows/approval-to-be.mmd
    kind: to-be
    source_refs: [SRC-1]
    traces_to: [BUC-1]
decisions:
  - id: DEC-1
    status: approved
    title: ERP remains source of record
    statement: ERP stays the source of record for availability.
    outcome: accepted
    source_refs: [SRC-1]
    traces_to: [REQ-1]
assumptions:
  - id: ASM-1
    status: approved
    title: ERP latency stays acceptable
    statement: ERP checks complete within the current SLA.
    source_refs: [SRC-1]
    traces_to: [REQ-1]
open_questions:
  - id: OQ-1
    status: reviewed
    title: Rejection reason source
    question: Should rejection codes come from ERP or the approval service?
    blocking: true
    source_refs: [SRC-1]
    traces_to: [REQ-2]
`;

describe('discovery-pack compile CLI', () => {
  let workdir: string;
  let sourceDir: string;
  let outputDir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'discovery-pack-compile-'));
    sourceDir = join(workdir, 'spec', 'discovery-pack');
    outputDir = join(workdir, 'artifacts', 'discovery-pack');
    await mkdir(join(sourceDir, 'flows'), { recursive: true });
    await mkdir(join(sourceDir, 'sources'), { recursive: true });
    await mkdir(outputDir, { recursive: true });
    await writeFile(join(sourceDir, 'sources', 'interview.md'), '# note\n', 'utf8');
    await writeFile(join(sourceDir, 'flows', 'approval-as-is.mmd'), 'flowchart TD\n  A-->B\n', 'utf8');
    await writeFile(join(sourceDir, 'flows', 'approval-to-be.mmd'), 'flowchart TD\n  A-->B\n', 'utf8');
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  const runCompile = (args: string[] = []) =>
    spawnSync(
      process.execPath,
      [
        compileScript,
        '--target',
        'plan-spec',
        '--sources',
        'spec/discovery-pack/**/*.{yml,yaml,json}',
        '--schema',
        discoverySchemaPath,
        '--output-dir',
        outputDir,
        ...args,
      ],
      {
        cwd: workdir,
        encoding: 'utf8',
      },
    );

  it('generates plan-spec markdown consumable by tests:scaffold', async () => {
    await writeFile(join(sourceDir, 'index.yaml'), DISCOVERY_PACK, 'utf8');

    const result = runCompile();
    expect(result.status).toBe(0);
    expect(existsSync(join(outputDir, 'plan-to-spec-normalized.md'))).toBe(true);
    expect(existsSync(join(outputDir, 'discovery-pack-compile-report.json'))).toBe(true);

    const markdown = await readFile(join(outputDir, 'plan-to-spec-normalized.md'), 'utf8');
    expect(markdown).toContain('## 3. Acceptance Criteria (AC) / 受入基準');
    expect(markdown).toContain('AC-1');
    expect(markdown).toContain('Approval must confirm reservation feasibility before final approval.');
    expect(markdown).not.toContain('Operator should see a rejection reason code.');

    const scaffoldDir = join(workdir, 'tests', 'generated', 'spec-kit', 'approve-reservation');
    testsScaffold({
      input: join(outputDir, 'plan-to-spec-normalized.md'),
      out: scaffoldDir,
      specId: 'approve-reservation',
      overwrite: true,
    });
    expect(existsSync(join(scaffoldDir, 'bdd', 'approve-reservation.feature'))).toBe(true);

    const report = JSON.parse(
      await readFile(join(outputDir, 'discovery-pack-compile-report.json'), 'utf8'),
    );
    expect(report.target).toBe('plan-spec');
    expect(report.summary.excludedByStatusCount).toBeGreaterThan(0);
    expect(report.summary.selectedBySection.business_use_cases).toBe(1);
  });

  it('generates a context-pack scaffold with provenance and valid schema shape', async () => {
    await writeFile(join(sourceDir, 'index.yaml'), DISCOVERY_PACK, 'utf8');

    const result = spawnSync(
      process.execPath,
      [
        compileScript,
        '--target',
        'context-pack-scaffold',
        '--sources',
        'spec/discovery-pack/**/*.{yml,yaml,json}',
        '--schema',
        discoverySchemaPath,
        '--output-dir',
        outputDir,
      ],
      {
        cwd: workdir,
        encoding: 'utf8',
      },
    );

    expect(result.status).toBe(0);

    const scaffoldRaw = await readFile(join(outputDir, 'context-pack-scaffold.yaml'), 'utf8');
    const scaffold = yaml.parse(scaffoldRaw);
    expect(scaffold.generated_from.discovery_pack.source_file).toBe('spec/discovery-pack/index.yaml');
    expect(scaffold.generated_from.selected_ids.business_use_cases).toEqual(['BUC-1']);
    expect(scaffold.problem_statement.goals).toContain('Approval should only proceed when stock can be reserved.');
    expect(scaffold.diagrams.map((entry: { id: string }) => entry.id)).toContain('FLOW-2');
    expect(scaffold.diagrams.map((entry: { id: string }) => entry.id)).not.toContain('FLOW-1');

    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(contextPackSchema);
    expect(validate(scaffold)).toBe(true);
  });

  it('fails with exit code 2 when multiple discovery packs match compile sources', async () => {
    await writeFile(join(sourceDir, 'index.yaml'), DISCOVERY_PACK, 'utf8');
    await writeFile(join(sourceDir, 'second.yaml'), DISCOVERY_PACK.replace('BUC-1', 'BUC-2'), 'utf8');

    const result = runCompile();
    expect(result.status).toBe(2);
    expect(result.stderr).toContain('compile expects exactly one discovery-pack input');
  });
});
