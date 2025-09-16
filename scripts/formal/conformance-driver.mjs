#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
function writeJson(p,obj){ fs.mkdirSync(path.dirname(p),{recursive:true}); fs.writeFileSync(p, JSON.stringify(obj,null,2)); }

const tracePath = process.env.CONFORMANCE_TRACE || 'artifacts/domain/replay.summary.json';
const specSummary = process.env.CONFORMANCE_SPEC || 'hermetic-reports/formal/tla-summary.json';
const out = process.env.CONFORMANCE_OUTPUT || 'hermetic-reports/formal/conformance-summary.json';

const trace = readJson(tracePath) || {};
const spec = readJson(specSummary) || {};

const summary = {
  ok: true,
  traceId: trace.traceId || null,
  events: trace.totalEvents || 0,
  violatedInvariants: trace.violatedInvariants || [],
  spec: spec.result || 'n/a',
  timestamp: new Date().toISOString()
};

summary.ok = (summary.violatedInvariants?.length ?? 0) === 0;

writeJson(out, summary);
console.log(`conformance summary written: ${out} ok=${summary.ok}`);
process.exit(0);

