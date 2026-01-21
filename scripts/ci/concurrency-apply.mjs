#!/usr/bin/env node
import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const args = new Set(process.argv.slice(2));
const apply = args.has('--apply');
const workflowsDir = join(process.cwd(), '.github', 'workflows');

const listYamlFiles = () =>
  readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));

const hasConcurrency = (lines) =>
  lines.some((line) => !line.trimStart().startsWith('#') && /^\s*concurrency\s*:/.test(line));

const findOnBlock = (lines) => {
  const start = lines.findIndex((line) => /^on\s*:/.test(line));
  if (start === -1) return null;
  let end = lines.length;
  for (let i = start + 1; i < lines.length; i += 1) {
    if (/^\S/.test(lines[i])) {
      end = i;
      break;
    }
  }
  return { start, end };
};

const blockHas = (lines, start, end, pattern) =>
  lines.slice(start, end).some((line) => pattern.test(line));

const summarize = { updated: [], skipped: [], unchanged: [] };

try {
  const files = listYamlFiles();
  for (const name of files) {
    const path = join(workflowsDir, name);
    const contents = readFileSync(path, 'utf8');
    const lines = contents.split('\n');

    if (hasConcurrency(lines)) {
      summarize.unchanged.push(name);
      continue;
    }

    const onBlock = findOnBlock(lines);
    if (!onBlock) {
      summarize.skipped.push({ name, reason: 'on block not found' });
      continue;
    }

    const { start, end } = onBlock;
    const hasWorkflowCall = blockHas(lines, start, end, /^\s*workflow_call\s*:/);
    const hasOtherTriggers = blockHas(
      lines,
      start,
      end,
      /^\s*(push|pull_request|schedule|workflow_dispatch|workflow_run|release)\s*:/
    );
    if (hasWorkflowCall && !hasOtherTriggers) {
      summarize.skipped.push({ name, reason: 'workflow_call only' });
      continue;
    }

    const hasPullRequest = blockHas(lines, start, end, /^\s*pull_request\s*:/);
    const hasRelease = blockHas(lines, start, end, /^\s*release\s*:/);
    const hasTags = blockHas(lines, start, end, /^\s*tags\s*:/);

    const group = hasPullRequest
      ? '${{ github.workflow }}-${{ github.event.pull_request.number || github.ref }}'
      : '${{ github.workflow }}-${{ github.ref }}';
    const cancelInProgress = hasRelease || hasTags ? 'false' : 'true';

    const block = [
      'concurrency:',
      `  group: ${group}`,
      `  cancel-in-progress: ${cancelInProgress}`,
      '',
    ];

    const updated = [...lines.slice(0, end), ...block, ...lines.slice(end)];
    if (apply) {
      writeFileSync(path, updated.join('\n'));
    }
    summarize.updated.push(name);
  }

  const report = (label, items) => {
    if (items.length === 0) return;
    console.log(`${label}:`);
    for (const item of items) {
      if (typeof item === 'string') {
        console.log(`- ${item}`);
      } else {
        console.log(`- ${item.name} (${item.reason})`);
      }
    }
  };

  console.log(apply ? 'Applied concurrency updates.' : 'Dry run (no changes).');
  report('Updated', summarize.updated);
  report('Skipped', summarize.skipped);
  report('Unchanged', summarize.unchanged);

  if (!apply && summarize.updated.length > 0) {
    process.exitCode = 1;
  }
} catch (error) {
  console.error(`[concurrency-apply] failed: ${error instanceof Error ? error.message : error}`);
  process.exit(1);
}
