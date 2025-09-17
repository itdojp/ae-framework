#!/usr/bin/env node
// Generate minimal replay fixtures from AE-IR domainEvents (non-blocking)
import fs from 'node:fs';
import path from 'node:path';

const irPath = process.env.AE_IR_PATH || '.ae/ae-ir.json';
const outFile = 'artifacts/domain/replay-fixtures.sample.json';
fs.mkdirSync(path.dirname(outFile), { recursive: true });

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return null; } }
const ir = readJson(irPath);
if (!ir) {
  fs.writeFileSync(outFile, JSON.stringify({ ok:false, reason:'ae-ir-missing' }, null, 2));
  console.log('⚠️ AE-IR not found. Wrote placeholder replay fixture.');
  process.exit(0);
}

const events = Array.isArray(ir.domainEvents) ? ir.domainEvents : [];
const items = events.slice(0, 20).map((e, idx) => ({
  id: `ev-${idx+1}`,
  name: e.name || 'Event',
  payload: e.payload || {},
  occursOn: e.occursOn || new Date().toISOString()
}));

const fixture = {
  traceId: `gen-${Date.now()}`,
  totalEvents: items.length,
  events: items
};

fs.writeFileSync(outFile, JSON.stringify(fixture, null, 2));
console.log(`✓ Generated replay fixture: ${outFile} (events=${items.length})`);
process.exit(0);

