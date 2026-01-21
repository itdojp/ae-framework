#!/usr/bin/env node
import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const args = new Set(process.argv.slice(2));
const apply = args.has('--apply');
const workflowsDir = join(process.cwd(), '.github', 'workflows');

const listYamlFiles = () =>
  readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));

const hasConcurrency = (lines) =>
  lines.some((line) => !line.trimStart().startsWith('#') && /^concurrency\s*:/.test(line));

const findOnBlock = (lines) => {
  // GitHub Actions requires `on` to be a top-level key.
  const start = lines.findIndex((line) => /^on\s*:/.test(line));
  if (start === -1) return null;
  let end = lines.length;
  let hasContent = false;
  for (let i = start + 1; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trimStart();
    if (trimmed === '' || trimmed.startsWith('#')) {
      continue;
    }
    if (/^\S/.test(line)) {
      end = hasContent ? i : start + 1;
      break;
    }
    hasContent = true;
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
    const eol = contents.includes('\r\n') ? '\r\n' : '\n';
    const lines = contents.split(/\r?\n/);

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
    const inlineOn = lines[start].match(/^on\s*:\s*(.+)$/);
    const inlineTriggers = new Set();
    if (inlineOn && inlineOn[1]) {
      const inline = inlineOn[1].trim();
      if (inline.startsWith('[') && inline.endsWith(']')) {
        for (const raw of inline.slice(1, -1).split(',')) {
          const token = raw.trim();
          if (token) inlineTriggers.add(token);
        }
      } else {
        inlineTriggers.add(inline);
      }
    }

    const hasWorkflowCall = inlineTriggers.has('workflow_call') ||
      blockHas(lines, start, end, /^\s*workflow_call\s*:/);
    const hasOtherTriggers =
      inlineTriggers.size > (hasWorkflowCall ? 1 : 0) ||
      blockHas(
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

    const group =
      "${{ github.workflow }}-${{ github.event_name == 'pull_request' && github.event.pull_request.number || github.ref }}";
    const cancelInProgress = !hasPullRequest && (hasRelease || hasTags) ? 'false' : 'true';

    const block = ['concurrency:', `  group: ${group}`, `  cancel-in-progress: ${cancelInProgress}`];

    const jobsIndex = lines.findIndex((line, index) => index >= end && /^jobs\s*:/.test(line));
    const insertIndex = jobsIndex === -1 ? end : jobsIndex;
    const needsSpacer = lines[insertIndex] && lines[insertIndex].trim() !== '';
    const updated = [
      ...lines.slice(0, insertIndex),
      ...block,
      ...(needsSpacer ? [''] : []),
      ...lines.slice(insertIndex),
    ];
    if (apply) {
      writeFileSync(path, updated.join(eol));
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

  // In CI, running without --apply acts as a check: fail if updates would be applied.
  if (!apply && summarize.updated.length > 0) {
    process.exitCode = 1;
  }
} catch (error) {
  console.error(`[concurrency-apply] failed: ${error instanceof Error ? error.message : error}`);
  process.exit(1);
}
