#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const DEFAULT_INPUT_JSON = 'tmp/maintenance/branch-inventory.json';
const DEFAULT_OUTPUT_JSON = 'tmp/maintenance/remote-branch-triage.json';
const DEFAULT_OUTPUT_MD = 'tmp/maintenance/remote-branch-triage.md';

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-branch-triage.mjs [options]

Options:
  --input-json <path>  Branch inventory JSON path (default: ${DEFAULT_INPUT_JSON})
  --output-json <path> Triage JSON output path (default: ${DEFAULT_OUTPUT_JSON})
  --output-md <path>   Triage Markdown output path (default: ${DEFAULT_OUTPUT_MD})
  --help               Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    inputJson: DEFAULT_INPUT_JSON,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
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
    if (arg === '--output-json') {
      options.outputJson = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = String(argv[++i] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.inputJson) throw new Error('--input-json is required');
  if (!options.outputJson) throw new Error('--output-json is required');
  if (!options.outputMd) throw new Error('--output-md is required');
  return options;
};

const escapeCell = (value) => String(value ?? '').replace(/\|/g, '\\|');

const renderTable = (headers, rows) => {
  if (rows.length === 0) {
    return '- (none)\n';
  }
  const head = `| ${headers.join(' | ')} |\n| ${headers.map(() => '---').join(' | ')} |`;
  const body = rows
    .map((row) => `| ${row.map((cell) => escapeCell(cell)).join(' | ')} |`)
    .join('\n');
  return `${head}\n${body}\n`;
};

export const buildTriageReport = (
  inventory,
  {
    generatedAt = new Date().toISOString(),
    inputJsonPath = DEFAULT_INPUT_JSON,
  } = {},
) => {
  const remoteMerged = (inventory?.candidates?.remoteMerged || []).map((branch) => ({
    branch,
    proposedAction: 'delete',
    approval: 'required',
    rationale: 'merged-to-base inventory candidate',
  }));

  const remoteStale = (inventory?.candidates?.remoteStaleByAge || []).map((item) => ({
    branch: item.branch,
    ageDays: item.ageDays,
    proposedAction: 'review',
    decision: '',
    notes: '',
  }));

  return {
    generatedAt,
    sourceInventory: {
      path: inputJsonPath,
      generatedAt: inventory?.generatedAt || '',
      base: inventory?.base || '',
      remote: inventory?.remote || '',
    },
    summary: {
      remoteMergedCandidates: remoteMerged.length,
      remoteStaleCandidates: remoteStale.length,
    },
    remoteMerged,
    remoteStale,
  };
};

export const renderMarkdown = (report, inputJsonPath) => {
  const mergedRows = report.remoteMerged.map((item) => [
    `\`${item.branch}\``,
    item.proposedAction,
    item.approval,
    item.rationale,
  ]);
  const staleRows = report.remoteStale.map((item) => [
    `\`${item.branch}\``,
    String(item.ageDays),
    item.proposedAction,
    item.decision || '(operator)',
    item.notes || '',
  ]);

  return `# Remote Branch Triage Worksheet

- generatedAt: ${report.generatedAt}
- source inventory: \`${inputJsonPath}\`
- inventory generatedAt: ${report.sourceInventory.generatedAt}
- base: \`${report.sourceInventory.base}\`
- remote: \`${report.sourceInventory.remote}\`

## Summary

- remote merged candidates: ${report.summary.remoteMergedCandidates}
- remote stale candidates: ${report.summary.remoteStaleCandidates}

## Remote merged candidates (delete after operator approval)

${renderTable(['branch', 'proposed', 'approval', 'rationale'], mergedRows)}
## Remote stale candidates (operator triage required)

${renderTable(['branch', 'ageDays', 'proposed', 'decision', 'notes'], staleRows)}
## Approval checklist

- [ ] \`pnpm run maintenance:branch:inventory\` を再実行して最新 inventory を確認した
- [ ] remote merged candidates の削除対象を確認した
- [ ] remote stale candidates に keep / archive / delete を記録した
- [ ] remote delete 実行前に operator approval を取得した

## Suggested commands

\`\`\`bash
# Refresh source inventory
pnpm run maintenance:branch:inventory

# Render triage worksheet
pnpm run maintenance:branch:triage:render

# Remote delete (operator approval required)
node scripts/maintenance/branch-cleanup.mjs --scope remote --max 100 --apply
\`\`\`
`;
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const inputJsonPath = path.resolve(options.inputJson);
  const outputJsonPath = path.resolve(options.outputJson);
  const outputMdPath = path.resolve(options.outputMd);

  const inventory = JSON.parse(fs.readFileSync(inputJsonPath, 'utf8'));
  const report = buildTriageReport(inventory, {
    inputJsonPath: options.inputJson,
  });
  const markdown = renderMarkdown(report, options.inputJson);

  fs.mkdirSync(path.dirname(outputJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(outputMdPath), { recursive: true });
  fs.writeFileSync(outputJsonPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  fs.writeFileSync(outputMdPath, markdown, 'utf8');

  console.log(`[remote-branch-triage] wrote ${outputJsonPath}`);
  console.log(`[remote-branch-triage] wrote ${outputMdPath}`);
  console.log(
    `[remote-branch-triage] merged=${report.summary.remoteMergedCandidates} stale=${report.summary.remoteStaleCandidates}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error(`[remote-branch-triage] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
