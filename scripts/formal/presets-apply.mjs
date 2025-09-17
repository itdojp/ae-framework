#!/usr/bin/env node
// Formal presets apply (non-blocking): reads presets/formal/*.json and .ae/ae-ir.json, emits a summary.
import fs from 'node:fs';
import path from 'node:path';

const irPath = process.env.AE_IR_PATH || '.ae/ae-ir.json';
const presetsDir = process.env.FORMAL_PRESETS_DIR || 'presets/formal';
const outFile = 'artifacts/formal/presets-summary.json';

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return null; } }

const ir = readJson(irPath);
let presets = [];
try {
  if (fs.existsSync(presetsDir)) {
    const files = fs.readdirSync(presetsDir).filter(f => f.endsWith('.json'));
    presets = files.map(f => ({ file: path.join(presetsDir, f), json: readJson(path.join(presetsDir, f)) })).filter(x => !!x.json);
  }
} catch {}

const applied = [];
for (const p of presets) {
  const name = p.json?.name || path.basename(p.file);
  const kind = p.json?.kind || 'tla';
  const count = Array.isArray(p.json?.rules) ? p.json.rules.length : 0;
  applied.push({ name, kind, file: p.file, rules: count });
}

const summary = {
  ok: true,
  irPresent: !!ir,
  presetsDir: presetsDir,
  presetsCount: presets.length,
  applied,
  timestamp: new Date().toISOString()
};

fs.mkdirSync(path.dirname(outFile), { recursive: true });
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`✓ Formal presets summary: ${outFile} (presets=${presets.length})`);
process.exit(0);

