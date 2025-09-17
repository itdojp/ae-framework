#!/usr/bin/env node
// Generate minimal contracts summary from AE-IR domainEntities and api (non-blocking)
import fs from 'node:fs';
import path from 'node:path';

const irPath = process.env.AE_IR_PATH || '.ae/ae-ir.json';
const outFile = 'artifacts/contracts/contracts-summary.json';
fs.mkdirSync(path.dirname(outFile), { recursive: true });

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return null; } }
const ir = readJson(irPath);
if (!ir) {
  fs.writeFileSync(outFile, JSON.stringify({ ok:false, reason:'ae-ir-missing' }, null, 2));
  console.log('⚠️ AE-IR not found. Wrote placeholder contracts summary.');
  process.exit(0);
}

const domain = Array.isArray(ir.domain) ? ir.domain : [];
const api = Array.isArray(ir.api) ? ir.api : [];

const entities = domain.map(d => ({ name: d.name, fields: Array.isArray(d.fields)? d.fields.map(f=>({name:f.name,type:f.type,required:!!f.required})) : [] }));
const endpoints = api.map(a => ({ method: a.method, path: a.path, hasRequest: !!a.request, hasResponse: !!a.response }));

const summary = {
  ok: true,
  entitiesCount: entities.length,
  endpointsCount: endpoints.length,
  entities,
  endpoints,
  timestamp: new Date().toISOString()
};

fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`✓ Generated contracts summary: ${outFile} (entities=${entities.length}, endpoints=${endpoints.length})`);
process.exit(0);

