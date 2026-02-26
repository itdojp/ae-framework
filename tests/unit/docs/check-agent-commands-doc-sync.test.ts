import { describe, expect, it } from 'vitest';

import {
  buildCatalogFromWorkflow,
  extractIssueCommands,
  extractLabelMetadata,
  extractPrCommands,
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
`;

describe('check-agent-commands-doc-sync', () => {
  it('splits workflow sections', () => {
    const result = splitWorkflowSections(SAMPLE_WORKFLOW);
    expect(result.prSection).toContain("case '/run-qa'");
    expect(result.issueSection).toContain("body.startsWith('/start')");
  });

  it('extracts PR and issue commands', () => {
    const sections = splitWorkflowSections(SAMPLE_WORKFLOW);
    expect(extractPrCommands(sections.prSection)).toEqual(['/coverage', '/handoff', '/run-qa']);
    expect(extractIssueCommands(sections.issueSection)).toEqual(['/done', '/start']);
  });

  it('extracts static and dynamic label metadata', () => {
    const labels = extractLabelMetadata(SAMPLE_WORKFLOW);
    expect(labels.prLabels).toEqual(['run-qa']);
    expect(labels.issueLabels).toEqual(['status:done', 'status:in-progress']);
    expect(labels.dynamicLabels).toEqual(['coverage:<0-100>', 'handoff:agent-{a|b|c}']);
  });

  it('renders generated catalog content from workflow', () => {
    const catalog = buildCatalogFromWorkflow(SAMPLE_WORKFLOW);
    expect(catalog).toContain('## PR向け Slash Commands');
    expect(catalog).toContain('`/run-qa`');
    expect(catalog).toContain('`status:in-progress`');
  });

  it('parses CLI options', () => {
    const options = parseArgs([
      'node',
      'check-agent-commands-doc-sync.mjs',
      '--workflow',
      'a.yml',
      '--output',
      'b.md',
      '--write',
    ]);
    expect(options).toEqual({
      workflowPath: 'a.yml',
      outputPath: 'b.md',
      write: true,
    });
  });
});
