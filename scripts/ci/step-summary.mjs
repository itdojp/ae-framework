#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function ensureSummaryPath() {
  const target = process.env.GITHUB_STEP_SUMMARY;
  if (!target) return null;
  const dir = path.dirname(target);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
  return target;
}

export function appendSection(title, lines = []) {
  const summaryPath = ensureSummaryPath();
  if (!summaryPath) return;
  const content = [`## ${title}`, ...lines].join('\n') + '\n';
  fs.appendFileSync(summaryPath, content);
}

export function formatKeyValue(entries) {
  return entries.map(([key, value]) => `- ${key}: ${value}`);
}

export function bulletList(items) {
  return items.map((item) => `- ${item}`);
}
