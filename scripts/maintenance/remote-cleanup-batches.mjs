#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { LOW_RISK_PREFIXES } from './remote-branch-triage.mjs';

const DEFAULT_INPUT_JSON = 'tmp/maintenance/remote-branch-triage.json';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-batches';
const DEFAULT_EXAMPLE_LIMIT = 5;

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-batches.mjs [options]

Options:
  --input-json <path>    remote-branch-triage JSON path (default: ${DEFAULT_INPUT_JSON})
  --output-dir <path>    Output directory for batch review packs (default: ${DEFAULT_OUTPUT_DIR})
  --example-limit <n>    Example rows to surface in summary markdown (default: ${DEFAULT_EXAMPLE_LIMIT})
  --help                 Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    inputJson: DEFAULT_INPUT_JSON,
    outputDir: DEFAULT_OUTPUT_DIR,
    exampleLimit: DEFAULT_EXAMPLE_LIMIT,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--input-json') {
      options.inputJson = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--example-limit') {
      options.exampleLimit = Number(argv[++i]);
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.inputJson) throw new Error('--input-json is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  if (!Number.isInteger(options.exampleLimit) || options.exampleLimit < 1) {
    throw new Error('--example-limit must be a positive integer');
  }
  return options;
};

const shellQuote = (value) => `'${String(value).replace(/'/g, `'"'"'`)}'`;

const escapeCell = (value) =>
  String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');

const renderTable = (headers, rows) => {
  if (rows.length === 0) {
    return '- (none)\n';
  }
  const head = `| ${headers.join(' | ')} |\n| ${headers.map(() => '---').join(' | ')} |`;
  const body = rows.map((row) => `| ${row.map((cell) => escapeCell(cell)).join(' | ')} |`).join('\n');
  return `${head}\n${body}\n`;
};

const startsWithAnyPrefix = (value, prefixes) => prefixes.some((prefix) => value.startsWith(prefix));

const formatLatestPrLabel = (latestPr) => {
  if (!latestPr?.number) return '-';
  const state = String(latestPr.state || latestPr.status || '').trim();
  return state ? `#${latestPr.number} (${state})` : `#${latestPr.number}`;
};

const buildBatch = ({ id, title, description, criteria, items, sourceTriage, outputDir, fileStem }) => {
  const jsonPath = path.join(outputDir, `${fileStem}.json`);
  const mdPath = path.join(outputDir, `${fileStem}.md`);
  const txtPath = path.join(outputDir, `${fileStem}.branches.txt`);
  const commandsPath = path.join(outputDir, `${fileStem}.commands.sh`);

  const payload = {
    generatedAt: new Date().toISOString(),
    batch: {
      id,
      title,
      description,
      criteria,
    },
    sourceTriage,
    count: items.length,
    items,
  };

  const branchLines = items.map((item) => item.branch);
  const commandLines = items
    .map((item) => String(item.deleteCommand || '').trim())
    .filter(Boolean);

  return {
    payload,
    jsonPath,
    mdPath,
    txtPath,
    commandsPath,
    branchLines,
    commandLines,
  };
};

export const selectReviewBatches = (report, { outputDir }) => {
  const sourceTriage = {
    path: report?.sourceInventory?.path || '',
    generatedAt: report?.generatedAt || '',
    inventoryGeneratedAt: report?.sourceInventory?.generatedAt || '',
    base: report?.sourceInventory?.base || '',
    remote: report?.sourceInventory?.remote || '',
  };
  const remoteMerged = Array.isArray(report?.remoteMerged) ? report.remoteMerged : [];
  const remoteStale = Array.isArray(report?.remoteStale) ? report.remoteStale : [];

  const batchAItems = remoteMerged.map((item) => ({
    branch: item.branch,
    branchOid: item.branchOid || '',
    prState: item.prState || '',
    prMatchMode: item.prMatchMode || '',
    latestPr: item.latestPr || null,
    baseBranches: Array.isArray(item.baseBranches) ? item.baseBranches : [],
    approval: item.approval || 'required',
    deleteCommand: item.deleteCommand || `git push ${shellQuote(sourceTriage.remote || 'origin')} --delete ${shellQuote(item.branch)}`,
  }));

  const batchBItems = remoteStale
    .filter((item) => startsWithAnyPrefix(String(item.branch || ''), LOW_RISK_PREFIXES))
    .filter((item) => item.prState !== 'ambiguous')
    .map((item) => ({
      branch: item.branch,
      ageDays: item.ageDays,
      branchOid: item.branchOid || '',
      riskBand: item.riskBand || '',
      prState: item.prState || '',
      prMatchMode: item.prMatchMode || '',
      latestPr: item.latestPr || null,
      proposedAction: item.proposedAction || '',
      decision: item.decision || '',
      notes: item.notes || '',
      baseBranches: Array.isArray(item.baseBranches) ? item.baseBranches : [],
    }));

  const batchCItems = remoteStale
    .filter((item) => item.prState === 'ambiguous')
    .map((item) => ({
      branch: item.branch,
      ageDays: item.ageDays,
      branchOid: item.branchOid || '',
      riskBand: item.riskBand || '',
      prState: item.prState || '',
      prMatchMode: item.prMatchMode || '',
      latestPr: item.latestPr || null,
      proposedAction: item.proposedAction || '',
      decision: item.decision || '',
      notes: item.notes || '',
      baseBranches: Array.isArray(item.baseBranches) ? item.baseBranches : [],
    }));

  return {
    batchA: buildBatch({
      id: 'A',
      title: 'Merged remote branches',
      description: 'Delete-ready merged remote branches. Execute only after operator approval.',
      criteria: 'All rows from remoteMerged[*]',
      items: batchAItems,
      sourceTriage,
      outputDir,
      fileStem: 'batch-a-merged',
    }),
    batchB: buildBatch({
      id: 'B',
      title: 'Low-risk stale branches',
      description: 'Review low-risk stale branches and record keep/archive/delete decisions.',
      criteria: `remoteStale[*] where branch prefix is one of ${LOW_RISK_PREFIXES.join(', ')} and prState != ambiguous`,
      items: batchBItems,
      sourceTriage,
      outputDir,
      fileStem: 'batch-b-low-risk-stale',
    }),
    batchC: buildBatch({
      id: 'C',
      title: 'Ambiguous stale branches',
      description: 'Manual review required because historical PR linkage is ambiguous.',
      criteria: 'remoteStale[*] where prState == ambiguous',
      items: batchCItems,
      sourceTriage,
      outputDir,
      fileStem: 'batch-c-ambiguous-stale',
    }),
  };
};

const renderMergedMarkdown = (batch) => {
  const rows = batch.payload.items.map((item) => [
    `\`${item.branch}\``,
    item.branchOid || '-',
    formatLatestPrLabel(item.latestPr),
    item.prMatchMode,
    item.baseBranches.join(', ') || '-',
    item.prState,
    item.approval,
    item.deleteCommand,
  ]);
  return `# ${batch.payload.batch.id}) ${batch.payload.batch.title}\n\n- generatedAt: ${batch.payload.generatedAt}\n- criteria: ${batch.payload.batch.criteria}\n- count: ${batch.payload.count}\n- source triage: \`${batch.payload.sourceTriage.path}\`\n\n${renderTable(
    ['branch', 'branchOid', 'latestPr', 'match', 'bases', 'prState', 'approval', 'deleteCommand'],
    rows,
  )}\n`;
};

const renderStaleMarkdown = (batch) => {
  const rows = batch.payload.items.map((item) => [
    `\`${item.branch}\``,
    String(item.ageDays),
    item.branchOid || '-',
    item.riskBand,
    item.prState,
    item.prMatchMode,
    formatLatestPrLabel(item.latestPr),
    item.baseBranches.join(', ') || '-',
    item.proposedAction,
    item.decision || '(operator)',
    item.notes || '',
  ]);
  return `# ${batch.payload.batch.id}) ${batch.payload.batch.title}\n\n- generatedAt: ${batch.payload.generatedAt}\n- criteria: ${batch.payload.batch.criteria}\n- count: ${batch.payload.count}\n- source triage: \`${batch.payload.sourceTriage.path}\`\n\n${renderTable(
    ['branch', 'ageDays', 'branchOid', 'risk', 'prState', 'match', 'latestPr', 'bases', 'proposed', 'decision', 'notes'],
    rows,
  )}\n`;
};

const renderSummaryMarkdown = (report, batches, { exampleLimit }) => {
  const examples = (items) => items.slice(0, exampleLimit).map((item) => `\`${item.branch}\``).join(', ') || '(none)';

  return `# Remote Cleanup Batch Packs\n\n- generatedAt: ${new Date().toISOString()}\n- source triage: \`${report?.sourceInventory?.path || ''}\`\n- triage generatedAt: ${report?.generatedAt || ''}\n- base: \`${report?.sourceInventory?.base || ''}\`\n- remote: \`${report?.sourceInventory?.remote || ''}\`\n\n## Current triage counts\n\n- remote merged candidates: ${report?.summary?.remoteMergedCandidates || 0}\n- remote stale candidates: ${report?.summary?.remoteStaleCandidates || 0}\n- stale risk bands: ${JSON.stringify(report?.summary?.staleByRiskBand || {})}\n- stale PR states: ${JSON.stringify(report?.summary?.staleByPrState || {})}\n\n## Review packs\n\n- Batch A (merged): ${batches.batchA.payload.count}  
  examples: ${examples(batches.batchA.payload.items)}  
  files: \`${path.basename(batches.batchA.jsonPath)}\`, \`${path.basename(batches.batchA.mdPath)}\`, \`${path.basename(batches.batchA.txtPath)}\`, \`${path.basename(batches.batchA.commandsPath)}\`
- Batch B (low-risk stale): ${batches.batchB.payload.count}  
  examples: ${examples(batches.batchB.payload.items)}  
  files: \`${path.basename(batches.batchB.jsonPath)}\`, \`${path.basename(batches.batchB.mdPath)}\`, \`${path.basename(batches.batchB.txtPath)}\`
- Batch C (ambiguous stale): ${batches.batchC.payload.count}  
  examples: ${examples(batches.batchC.payload.items)}  
  files: \`${path.basename(batches.batchC.jsonPath)}\`, \`${path.basename(batches.batchC.mdPath)}\`, \`${path.basename(batches.batchC.txtPath)}\`
\n## Notes\n\n- Batch A may be empty when current inventory has no remote merged candidates.
- Batch B excludes \`prState=ambiguous\`; branch-name reuse risk is isolated into Batch C.
- No remote deletion is executed by this script. Execution remains gated by operator approval and \`branch-cleanup.mjs --apply\`.\n`;
};

const renderIssueComment = (report, batches) => `Batch refresh from \`${report?.sourceInventory?.path || ''}\`:
- Batch A (merged): ${batches.batchA.payload.count}
- Batch B (low-risk stale): ${batches.batchB.payload.count}
- Batch C (ambiguous stale): ${batches.batchC.payload.count}
- source base/remote: \`${report?.sourceInventory?.base || ''}\` / \`${report?.sourceInventory?.remote || ''}\`

Artifacts written under \`${path.dirname(batches.batchA.jsonPath)}\`:
- \`${path.basename(batches.batchA.mdPath)}\`
- \`${path.basename(batches.batchB.mdPath)}\`
- \`${path.basename(batches.batchC.mdPath)}\`
- \`${path.basename(path.join(path.dirname(batches.batchA.jsonPath), 'summary.md'))}\`

Notes:
- Batch A contains operator-ready delete commands only when remoteMerged candidates exist.
- Batch B is the review set for low-risk prefixes (${LOW_RISK_PREFIXES.join(', ')}), excluding ambiguous linkage.
- Batch C isolates \`prState=ambiguous\` rows for manual inspection before any archive/delete decision.
`;

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const inputJsonPath = path.resolve(options.inputJson);
  const outputDir = path.resolve(options.outputDir);
  const report = JSON.parse(fs.readFileSync(inputJsonPath, 'utf8'));
  const batches = selectReviewBatches(report, { outputDir });

  const summaryJsonPath = path.join(outputDir, 'summary.json');
  const summaryMdPath = path.join(outputDir, 'summary.md');
  const issueCommentPath = path.join(outputDir, 'issue-comment.md');

  for (const batch of Object.values(batches)) {
    const markdown = batch.payload.batch.id === 'A' ? renderMergedMarkdown(batch) : renderStaleMarkdown(batch);
    writeFile(batch.jsonPath, `${JSON.stringify(batch.payload, null, 2)}\n`);
    writeFile(batch.mdPath, markdown);
    writeFile(batch.txtPath, `${batch.branchLines.join('\n')}${batch.branchLines.length ? '\n' : ''}`);
    if (batch.payload.batch.id === 'A') {
      writeFile(batch.commandsPath, `${batch.commandLines.join('\n')}${batch.commandLines.length ? '\n' : ''}`);
    }
  }

  const summary = {
    generatedAt: new Date().toISOString(),
    sourceTriage: {
      path: inputJsonPath,
      generatedAt: report?.generatedAt || '',
      base: report?.sourceInventory?.base || '',
      remote: report?.sourceInventory?.remote || '',
    },
    triageSummary: report?.summary || {},
    batches: Object.fromEntries(
      Object.entries(batches).map(([key, batch]) => [
        key,
        {
          id: batch.payload.batch.id,
          title: batch.payload.batch.title,
          count: batch.payload.count,
          jsonPath: batch.jsonPath,
          mdPath: batch.mdPath,
          txtPath: batch.txtPath,
          commandsPath: batch.payload.batch.id === 'A' ? batch.commandsPath : '',
        },
      ]),
    ),
    issueCommentPath,
  };

  writeFile(summaryJsonPath, `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(summaryMdPath, renderSummaryMarkdown(report, batches, { exampleLimit: options.exampleLimit }));
  writeFile(issueCommentPath, renderIssueComment(report, batches));

  console.log(`[remote-cleanup-batches] wrote ${summaryJsonPath}`);
  console.log(`[remote-cleanup-batches] wrote ${summaryMdPath}`);
  console.log(
    `[remote-cleanup-batches] batchA=${batches.batchA.payload.count} batchB=${batches.batchB.payload.count} batchC=${batches.batchC.payload.count}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error(`[remote-cleanup-batches] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
