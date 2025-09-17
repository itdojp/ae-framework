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

const t0 = Date.now();
const violated = Array.isArray(trace.violatedInvariants) ? trace.violatedInvariants : [];
const ok = violated.length === 0;
const summary = {
  tool: 'conformance-driver',
  ran: true,
  ok,
  timeMs: Date.now() - t0,
  errors: violated.map(v => (typeof v === 'string' ? v : JSON.stringify(v))).slice(0, 20),
  traceId: trace.traceId || null,
  events: Number(trace.totalEvents || 0),
  violatedInvariants: violated,
  spec: spec.result || 'n/a',
  timestamp: new Date().toISOString()
};

writeJson(out, summary);
console.log(`conformance summary written: ${out} ok=${summary.ok}`);
process.exit(0);
