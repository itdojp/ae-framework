import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

import {
  buildGeneratedFrontMatter,
  buildCatalogFromWorkflow,
  extractIssueCommands,
  extractLabelMetadata,
  extractPrCommands,
  main,
  parseGeneratedFrontMatter,
  parseArgs,
  splitWorkflowSections,
} from '../../../scripts/docs/check-agent-commands-doc-sync.mjs';

const SAMPLE_WORKFLOW = `
jobs:
  handle_pr:
    steps:
      - name: sample
        with:
          script: |
            switch (cmd) {
              case '/run-qa':
                await addLabels(['run-qa']);
                return;
              case '/coverage': {
                await addLabels([\`coverage:\${n}\`]);
                return;
              }
              case '/handoff': {
                await addLabels([\`handoff:agent-\${m.toLowerCase()}\`]);
                return;
              }
              default:
                return;
            }
  handle_issue:
    steps:
      - name: sample
        with:
          script: |
            if (body.startsWith('/start')) {
              await add(['status:in-progress']);
              return;
            }
            if (body.startsWith('/done')) {
              await add(['status:done']);
              return;
            }
            switch (cmd) {
              case '/block':
                await add(['status:blocked']);
                return;
              default:
                return;
            }
`;

describe('check-agent-commands-doc-sync', () => {
  const temporaryRoots: string[] = [];

  beforeEach(() => {
    vi.spyOn(process.stdout, 'write').mockImplementation(() => true);
    vi.spyOn(process.stderr, 'write').mockImplementation(() => true);
  });

  afterEach(() => {
    vi.useRealTimers();
    vi.restoreAllMocks();
    for (const root of temporaryRoots.splice(0)) {
      fs.rmSync(root, { recursive: true, force: true });
    }
  });

  function createFixture(lastVerified = '2026-07-26', writeDocument = true) {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'ae-agent-commands-sync-'));
    temporaryRoots.push(root);
    fs.mkdirSync(path.join(root, '.github/workflows'), { recursive: true });
    fs.mkdirSync(path.join(root, 'docs/agents'), { recursive: true });
    fs.writeFileSync(path.join(root, '.github/workflows/agent-commands.yml'), SAMPLE_WORKFLOW);
    if (writeDocument) {
      fs.writeFileSync(
        path.join(root, 'docs/agents/commands.md'),
        buildCatalogFromWorkflow(SAMPLE_WORKFLOW, { lastVerified }),
      );
    }
    return root;
  }

  function runFixture(root: string, ...args: string[]) {
    return main(['node', 'check-agent-commands-doc-sync.mjs', '--root', root, ...args]);
  }

  it('splits workflow sections', () => {
    const result = splitWorkflowSections(SAMPLE_WORKFLOW);
    expect(result.prSection).toContain("case '/run-qa'");
    expect(result.issueSection).toContain("body.startsWith('/start')");
  });

  it('extracts PR and issue commands', () => {
    const sections = splitWorkflowSections(SAMPLE_WORKFLOW);
    expect(extractPrCommands(sections.prSection)).toEqual(['/coverage', '/handoff', '/run-qa']);
    expect(extractIssueCommands(sections.issueSection)).toEqual(['/block', '/done', '/start']);
  });

  it('extracts static and dynamic label metadata', () => {
    const labels = extractLabelMetadata(SAMPLE_WORKFLOW);
    expect(labels.prLabels).toEqual(['run-qa']);
    expect(labels.issueLabels).toEqual(['status:blocked', 'status:done', 'status:in-progress']);
    expect(labels.dynamicLabels).toEqual(['coverage:<0-100>', 'handoff:agent-{a|b|c}']);
  });

  it('renders generated catalog content from workflow', () => {
    const catalog = buildCatalogFromWorkflow(SAMPLE_WORKFLOW, { lastVerified: '2026-07-26' });
    expect(catalog).toContain('docRole: derived');
    expect(catalog).toContain('.github/workflows/agent-commands.yml');
    expect(catalog).toContain("lastVerified: '2026-07-26'");
    expect(catalog).toContain('## PR向け Slash Commands');
    expect(catalog).toContain('`/run-qa`');
    expect(catalog).toContain('`status:in-progress`');
  });

  it('builds generated front matter with supplied verification date', () => {
    expect(buildGeneratedFrontMatter({ lastVerified: '2026-03-09' })).toContain("lastVerified: '2026-03-09'");
  });

  it('requires an explicit verification date in the rendering API', () => {
    expect(() => buildGeneratedFrontMatter({ lastVerified: undefined })).toThrow(
      'lastVerified must use YYYY-MM-DD format',
    );
  });

  it('parses exactly one valid lastVerified value from front matter', () => {
    const catalog = buildCatalogFromWorkflow(SAMPLE_WORKFLOW, { lastVerified: '2026-07-26' });
    expect(parseGeneratedFrontMatter(catalog)).toEqual({ lastVerified: '2026-07-26' });
  });

  it('parses CLI options', () => {
    const options = parseArgs([
      'node',
      'check-agent-commands-doc-sync.mjs',
      '--root',
      '/tmp/repo',
      '--workflow',
      'a.yml',
      '--output',
      'b.md',
      '--write',
      '--last-verified',
      '2026-07-26',
    ]);
    expect(options).toEqual({
      rootDir: path.resolve('/tmp/repo'),
      workflowPath: 'a.yml',
      outputPath: 'b.md',
      write: true,
      lastVerified: '2026-07-26',
    });
  });

  it('passes check on 2026-07-27 for a document verified on 2026-07-26', () => {
    const root = createFixture();
    vi.useFakeTimers();
    vi.setSystemTime(new Date('2026-07-27T12:00:00Z'));

    expect(runFixture(root)).toBe(0);
  });

  it('passes check on 2026-08-01 for a document verified on 2026-07-26', () => {
    const root = createFixture();
    vi.useFakeTimers();
    vi.setSystemTime(new Date('2026-08-01T12:00:00Z'));

    expect(runFixture(root)).toBe(0);
  });

  it('fails check when the workflow command catalog drifts', () => {
    const root = createFixture();
    const workflowPath = path.join(root, '.github/workflows/agent-commands.yml');
    fs.writeFileSync(workflowPath, SAMPLE_WORKFLOW.replace("case '/run-qa':", "case '/changed-command':"));

    expect(runFixture(root)).toBe(1);
  });

  it('fails check when the workflow label catalog drifts', () => {
    const root = createFixture();
    const workflowPath = path.join(root, '.github/workflows/agent-commands.yml');
    fs.writeFileSync(workflowPath, SAMPLE_WORKFLOW.replace("addLabels(['run-qa'])", "addLabels(['run-qa-new'])"));

    expect(runFixture(root)).toBe(1);
  });

  it('fails closed when lastVerified is missing', () => {
    const root = createFixture();
    const outputPath = path.join(root, 'docs/agents/commands.md');
    fs.writeFileSync(outputPath, fs.readFileSync(outputPath, 'utf8').replace(/lastVerified:.*\n/u, ''));

    expect(runFixture(root)).toBe(1);
    expect(process.stderr.write).toHaveBeenCalledWith(
      expect.stringContaining('front matter is missing lastVerified'),
    );
  });

  it('fails closed when lastVerified has an invalid date format', () => {
    const root = createFixture();
    const outputPath = path.join(root, 'docs/agents/commands.md');
    fs.writeFileSync(outputPath, fs.readFileSync(outputPath, 'utf8').replace('2026-07-26', '2026/07/26'));

    expect(runFixture(root)).toBe(1);
    expect(process.stderr.write).toHaveBeenCalledWith(
      expect.stringContaining('lastVerified must use YYYY-MM-DD format'),
    );
  });

  it('fails closed when lastVerified is not a real calendar date', () => {
    const root = createFixture();
    const outputPath = path.join(root, 'docs/agents/commands.md');
    fs.writeFileSync(outputPath, fs.readFileSync(outputPath, 'utf8').replace('2026-07-26', '2026-02-30'));

    expect(runFixture(root)).toBe(1);
    expect(process.stderr.write).toHaveBeenCalledWith(
      expect.stringContaining('lastVerified must be a valid calendar date'),
    );
  });

  it('fails closed when lastVerified is duplicated', () => {
    const root = createFixture();
    const outputPath = path.join(root, 'docs/agents/commands.md');
    fs.writeFileSync(
      outputPath,
      fs.readFileSync(outputPath, 'utf8').replace(
        "lastVerified: '2026-07-26'",
        "lastVerified: '2026-07-26'\nlastVerified: '2026-07-26'",
      ),
    );

    expect(runFixture(root)).toBe(1);
    expect(process.stderr.write).toHaveBeenCalledWith(
      expect.stringContaining('front matter contains duplicate lastVerified'),
    );
  });

  it('writes deterministic bytes with an explicit lastVerified date', () => {
    const root = createFixture('2026-07-26', false);

    expect(runFixture(root, '--write', '--last-verified', '2026-07-26')).toBe(0);
    expect(fs.readFileSync(path.join(root, 'docs/agents/commands.md'), 'utf8')).toBe(
      buildCatalogFromWorkflow(SAMPLE_WORKFLOW, { lastVerified: '2026-07-26' }),
    );
  });

  it('produces byte-identical output for consecutive writes with the same date', () => {
    const root = createFixture('2026-07-26', false);

    expect(runFixture(root, '--write', '--last-verified=2026-07-26')).toBe(0);
    const first = fs.readFileSync(path.join(root, 'docs/agents/commands.md'));
    expect(runFixture(root, '--write', '--last-verified=2026-07-26')).toBe(0);
    const second = fs.readFileSync(path.join(root, 'docs/agents/commands.md'));

    expect(second.equals(first)).toBe(true);
  });

  it('requires --last-verified for write mode', () => {
    const root = createFixture('2026-07-26', false);

    expect(runFixture(root, '--write')).toBe(1);
    expect(fs.existsSync(path.join(root, 'docs/agents/commands.md'))).toBe(false);
  });

  it('keeps the repository agent-command document valid under docs governance', () => {
    expect(main(['node', 'check-agent-commands-doc-sync.mjs', '--root', process.cwd()])).toBe(0);
  });
});
