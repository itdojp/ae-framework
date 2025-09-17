#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
function writeJson(p,obj){ fs.mkdirSync(path.dirname(p),{recursive:true}); fs.writeFileSync(p, JSON.stringify(obj,null,2)); }

const tracePath = process.env.CONFORMANCE_TRACE || 'artifacts/domain/replay.summary.json';
const specSummary = process.env.CONFORMANCE_SPEC || 'hermetic-reports/formal/tla-summary.json';
const runtimeHooksPath = process.env.RUNTIME_HOOKS || process.env.CONFORMANCE_RUNTIME_HOOKS || 'hermetic-reports/runtime/hooks.json';
const out = process.env.CONFORMANCE_OUTPUT || 'hermetic-reports/formal/conformance-summary.json';

const trace = readJson(tracePath) || {};
const spec = readJson(specSummary) || {};
const hooks = readJson(runtimeHooksPath) || undefined;

const t0 = Date.now();
const violated = Array.isArray(trace.violatedInvariants) ? trace.violatedInvariants : [];
const ok = violated.length === 0;
// Compare runtime hooks with replay summary if both present (best-effort)
let hooksInfo = null;
try {
  if (hooks) {
    const events = Array.isArray(hooks) ? hooks : (Array.isArray(hooks.events) ? hooks.events : []);
    const hooksTraceId = hooks.traceId || (events[0]?.traceId) || null;
    const replayTraceId = trace.traceId || null;
    const eventNames = Array.isArray(events) ? Array.from(new Set(events.map(e => e && e.event))) : [];
    hooksInfo = {
      present: true,
      path: runtimeHooksPath,
      count: Array.isArray(events) ? events.length : 0,
      uniqueEvents: eventNames.filter(Boolean),
      traceId: hooksTraceId,
      matchesReplayTraceId: !!(hooksTraceId && replayTraceId && hooksTraceId === replayTraceId)
    };
  }
} catch {}

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
  timestamp: new Date().toISOString(),
  runtimeHooks: hooksInfo
};

writeJson(out, summary);
console.log(`conformance summary written: ${out} ok=${summary.ok}`);
process.exit(0);
