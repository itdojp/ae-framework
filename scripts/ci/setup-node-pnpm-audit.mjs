#!/usr/bin/env node
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const workflowsDir = join(process.cwd(), '.github', 'workflows');
const setupAction = './.github/actions/setup-node-pnpm';

try {
  const escapeForRegex = (value) => value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const usesPattern = new RegExp(
    String.raw`^[ \t]*uses:\s*(["'])?${escapeForRegex(setupAction)}\1?`,
    'm'
  );
  const reusableWorkflows = ['./.github/workflows/ci-core.yml', './.github/workflows/flake-stability.yml'];
  const reusablePattern = new RegExp(
    String.raw`^[ \t]*uses:\s*(["'])?(?:${reusableWorkflows.map(escapeForRegex).join('|')})\1?`,
    'm'
  );
  const pnpmPattern = /\bpnpm\b/m;
  const nodePattern = /\bnode\s+\S/m;
  // Workflows that intentionally use setup-node (not setup-node-pnpm)
  // for node-only operations without pnpm dependencies.
  const nodeOnlyAllowlist = new Set(['cedar-quality-gates.yml']);
  /**
   * Extracts shell command content from all `run:` blocks in a workflow YAML file.
   *
   * This performs a lightweight, line-based parse of the YAML:
   * - Matches lines containing a `run:` key (optionally prefixed with `- `).
   * - If the `run:` value is inline (e.g. `run: echo hello`), the trimmed value
   *   is captured directly.
   * - If the `run:` value uses a block scalar indicator (`|` or `>`), the
   *   subsequent indented lines are collected until the indentation returns to
   *   the level of the `run:` key or less. The collected lines are joined with
   *   `\n` and added as a single block.
   *
   * Note: This is intentionally a minimal parser tailored to GitHub Actions
   * workflows and does not aim to be a full YAML parser.
   *
   * @param {string} contents - The full contents of a workflow YAML file.
   * @returns {string} A single string containing all extracted run block contents.
   */
  const extractRunBlocks = (contents) => {
    const lines = contents.split('\n');
    const blocks = [];
    for (let i = 0; i < lines.length; i += 1) {
      const line = lines[i];
      const match = line.match(/^([ \t]*)(?:- )?run:\s*(.*)$/);
      if (!match) continue;
      const baseIndent = match[1].length;
      const tail = match[2];
      const trimmedTail = tail ? tail.trim() : '';
      if (trimmedTail && !trimmedTail.startsWith('|') && !trimmedTail.startsWith('>')) {
        blocks.push(trimmedTail);
        continue;
      }
      const blockLines = [];
      for (let j = i + 1; j < lines.length; j += 1) {
        const next = lines[j];
        if (next.trim() === '') {
          blockLines.push('');
          continue;
        }
        const indent = next.match(/^[ \t]*/)[0].length;
        if (indent <= baseIndent) {
          i = j - 1;
          break;
        }
        blockLines.push(next.trimStart());
        if (j === lines.length - 1) {
          i = j;
        }
      }
      if (blockLines.length > 0) blocks.push(blockLines.join('\n'));
    }
    return blocks.join('\n');
  };
  const files = readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));
  const missing = [];
  const reviewOnly = [];
  const nodeOnlyAllowed = [];
  for (const name of files) {
    const path = join(workflowsDir, name);
    const contents = readFileSync(path, 'utf8');
    if (usesPattern.test(contents) || reusablePattern.test(contents)) continue;
    const runBlocks = extractRunBlocks(contents);
    const hasPnpm = pnpmPattern.test(runBlocks);
    const hasNode = nodePattern.test(runBlocks);
    if (nodeOnlyAllowlist.has(name)) {
      if (hasPnpm) {
        missing.push(name);
        continue;
      }
      if (hasNode) {
        nodeOnlyAllowed.push(name);
        continue;
      }
    }
    if (hasPnpm || hasNode) {
      missing.push(name);
      continue;
    }
    reviewOnly.push(name);
  }

  missing.sort();
  reviewOnly.sort();
  nodeOnlyAllowed.sort();
  if (missing.length === 0 && reviewOnly.length === 0 && nodeOnlyAllowed.length === 0) {
    console.log('All workflows use setup-node-pnpm or do not need pnpm/node.');
    process.exit(0);
  }

  if (missing.length > 0) {
    console.log('Workflows missing setup-node-pnpm (pnpm/node detected):');
    for (const name of missing) {
      console.log(`- ${name}`);
    }
  }
  if (reviewOnly.length > 0) {
    console.log('Workflows without pnpm/node usage (review if needed):');
    for (const name of reviewOnly) {
      console.log(`- ${name}`);
    }
  }
  if (nodeOnlyAllowed.length > 0) {
    console.log('Workflows allowed to use setup-node (node-only allowlist):');
    for (const name of nodeOnlyAllowed) {
      console.log(`- ${name}`);
    }
  }
  process.exit(missing.length > 0 ? 1 : 0);
} catch (error) {
  console.error(`Failed to audit setup-node-pnpm usage in "${workflowsDir}":`);
  console.error(error instanceof Error ? error.message : error);
  process.exit(1);
}
