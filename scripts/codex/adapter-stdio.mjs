#!/usr/bin/env node
// CodeX stdio adapter: JSON-in/JSON-out bridge to CodeX Task Adapter
// Usage:
//   echo '{"description":"Generate UI","subagent_type":"ui","context":{}}' | node scripts/codex/adapter-stdio.mjs

import fs from 'fs';
import path from 'path';

function readAllStdin() {
  return new Promise((resolve, reject) => {
    let data = '';
    process.stdin.setEncoding('utf8');
    process.stdin.on('data', chunk => (data += chunk));
    process.stdin.on('end', () => resolve(data));
    process.stdin.on('error', reject);
  });
}

async function loadAdapter() {
  const candidates = [
    path.resolve('dist/src/agents/codex-task-adapter.js'),
    path.resolve('dist/agents/codex-task-adapter.js'),
  ];
  for (const p of candidates) {
    if (fs.existsSync(p)) {
      return await import(p);
    }
  }
  throw new Error('Adapter not found. Build first: pnpm run build');
}

function writeJSON(obj) {
  process.stdout.write(JSON.stringify(obj) + '\n');
}

function writeError(message, code = 1) {
  writeJSON({ error: true, message });
  process.exit(code);
}

async function main() {
  const raw = await readAllStdin();
  if (!raw.trim()) {
    writeError('No input provided on stdin');
    return;
  }
  let req;
  try {
    req = JSON.parse(raw);
  } catch (e) {
    writeError(`Invalid JSON: ${e.message}`);
    return;
  }

  try {
    const { createCodexTaskAdapter } = await loadAdapter();
    const adapter = createCodexTaskAdapter();
    const res = await adapter.handleTask(req);
    writeJSON(res);
    if (res.shouldBlockProgress) process.exit(2);
  } catch (e) {
    writeError(`Adapter error: ${e.message || String(e)}`);
  }
}

main();

