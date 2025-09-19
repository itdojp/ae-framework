#!/usr/bin/env node
// Dump meta fields from JSON files under reports/ and artifacts/
import fs from 'node:fs';
import path from 'node:path';

const roots = ['reports', 'artifacts'];

function* walk(dir) {
  try {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, entry.name);
      if (entry.isDirectory()) yield* walk(p);
      else if (entry.isFile() && entry.name.endsWith('.json')) yield p;
    }
  } catch {}
}

function dumpMeta(file) {
  try {
    const j = JSON.parse(fs.readFileSync(file, 'utf8'));
    const meta = j?.metadata || j?.meta || null;
    if (!meta) return null;
    return {
      file,
      keys: Object.keys(meta),
      sample: Object.fromEntries(Object.entries(meta).slice(0, 5)),
    };
  } catch {
    return null;
  }
}

for (const root of roots) {
  for (const file of walk(root)) {
    const info = dumpMeta(file);
    if (info) {
      console.log(JSON.stringify(info));
    }
  }
}

