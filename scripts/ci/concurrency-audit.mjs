#!/usr/bin/env node
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const workflowsDir = join(process.cwd(), '.github', 'workflows');

try {
  const files = readdirSync(workflowsDir).filter((name) => name.endsWith('.yml') || name.endsWith('.yaml'));
  const missing = [];
  const skipped = [];
  const concurrencyPattern = /^\s*concurrency:/m;

  const findOnBlock = (lines) => {
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

  const isWorkflowCallOnly = (lines) => {
    const onBlock = findOnBlock(lines);
    if (!onBlock) return false;
    const { start, end } = onBlock;

    const inlineOn = lines[start].match(/^on\s*:\s*(.+)$/);
    const inlineTriggers = new Set();
    if (inlineOn && inlineOn[1]) {
      const stripQuotes = (value) => value.replace(/^['"]+|['"]+$/g, '');
      const inline = inlineOn[1].trim();
      if (inline.startsWith('[') && inline.endsWith(']')) {
        for (const raw of inline.slice(1, -1).split(',')) {
          const token = raw.trim();
          if (token) inlineTriggers.add(stripQuotes(token));
        }
      } else {
        inlineTriggers.add(stripQuotes(inline));
      }
    }

    const hasWorkflowCall = inlineTriggers.has('workflow_call') ||
      blockHas(lines, start, end, /^\s*workflow_call\s*:/);

    const onIndentMatch = lines[start].match(/^(\s*)on\s*:/);
    const onIndent = onIndentMatch ? onIndentMatch[1] : '';
    const childIndent = `${onIndent}  `;
    let hasOtherBlockTriggers = false;
    for (let i = start + 1; i < end; i++) {
      const line = lines[i];
      if (/^\s*$/.test(line)) continue;
      const trimmed = line.trimStart();
      if (trimmed.startsWith('#')) continue;
      const match = line.match(/^(\s*)([A-Za-z_][\w-]*)\s*:/);
      if (!match) continue;
      const indent = match[1];
      const key = match[2];
      if (indent === childIndent && key !== 'workflow_call') {
        hasOtherBlockTriggers = true;
        break;
      }
    }

    const hasOtherTriggers =
      inlineTriggers.size > (hasWorkflowCall ? 1 : 0) || hasOtherBlockTriggers;
    return hasWorkflowCall && !hasOtherTriggers;
  };

  for (const name of files) {
    const path = join(workflowsDir, name);
    const contents = readFileSync(path, 'utf8');
    if (!concurrencyPattern.test(contents)) {
      const lines = contents.split(/\r?\n/);
      if (isWorkflowCallOnly(lines)) {
        skipped.push(name);
        continue;
      }
      missing.push(name);
    }
  }

  missing.sort();
  skipped.sort();
  if (missing.length === 0) {
    console.log('All workflows define concurrency.');
    if (skipped.length > 0) {
      console.log('Skipped workflow_call-only workflows:');
      for (const name of skipped) {
        console.log(`- ${name}`);
      }
    }
    process.exit(0);
  }

  console.log('Workflows missing concurrency:');
  for (const name of missing) {
    console.log(`- ${name}`);
  }
  if (skipped.length > 0) {
    console.log('Skipped workflow_call-only workflows:');
    for (const name of skipped) {
      console.log(`- ${name}`);
    }
  }
  process.exitCode = 1;
} catch (error) {
  console.error(`Failed to audit workflow concurrency in directory "${workflowsDir}":`);
  console.error(error instanceof Error ? error.message : error);
  process.exit(1);
}
