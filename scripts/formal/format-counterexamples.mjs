#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }

const SOURCE_CANDIDATES = [
  {
    label: 'hermetic-formal-aggregate',
    path: 'artifacts/hermetic-reports/formal/summary.json',
    kind: 'aggregate'
  },
  {
    label: 'formal-aggregate',
    path: 'artifacts/formal/formal-aggregate.json',
    kind: 'aggregate'
  },
  {
    label: 'legacy-formal-summary',
    path: 'formal/summary.json',
    kind: 'legacy'
  }
];

const FALLBACK_AGGREGATE_TOOL_KEYS = [
  'tlc',
  'conformance',
  'smt',
  'alloy',
  'tla',
  'apalache',
  'kani',
  'spin',
  'csp',
  'lean',
  'model'
];

function asArray(value) {
  return Array.isArray(value) ? value : [];
}

function collectFromContainer(container) {
  if (!container || typeof container !== 'object') return [];
  const items = [];
  items.push(...asArray(container.counterexamples));
  if (container.counterexample && typeof container.counterexample === 'object') {
    items.push(container.counterexample);
  }
  if (container.details && typeof container.details === 'object') {
    items.push(...asArray(container.details.counterexamples));
  }
  if (container.raw && typeof container.raw === 'object') {
    items.push(...asArray(container.raw.counterexamples));
  }
  return items;
}

function collectCounterexamples(payload, kind) {
  if (!payload || typeof payload !== 'object') return [];
  if (kind === 'legacy') return collectFromContainer(payload);

  const items = [];
  items.push(...collectFromContainer(payload));

  if (Array.isArray(payload.results)) {
    for (const result of payload.results) {
      items.push(...collectFromContainer(result));
    }
  }

  if (kind === 'aggregate') {
    for (const key of aggregateToolKeys(payload)) {
      items.push(...collectFromContainer(payload[key]));
    }
  }

  return items;
}

function objectKeys(value) {
  return value && typeof value === 'object' && !Array.isArray(value) ? Object.keys(value) : [];
}

function aggregateToolKeys(payload) {
  const keys = [
    ...objectKeys(payload.present),
    ...objectKeys(payload.info?.present),
    ...FALLBACK_AGGREGATE_TOOL_KEYS
  ];
  return [...new Set(keys)].filter((key) => payload[key] && typeof payload[key] === 'object');
}

function selectCounterexampleSource() {
  for (const candidate of SOURCE_CANDIDATES) {
    const payload = readJson(candidate.path);
    if (!payload) continue;
    const counterexamples = collectCounterexamples(payload, candidate.kind);
    if (counterexamples.length > 0) {
      return { ...candidate, counterexamples };
    }
  }
  return undefined;
}

function firstString(...values) {
  for (const value of values) {
    if (typeof value === 'string' && value.trim().length > 0) return value;
  }
  return undefined;
}

function propertyOf(ce) {
  if (!ce || typeof ce !== 'object') return undefined;
  return firstString(
    ce.property,
    ce.json?.then?.violated,
    ce.violated?.message,
    ce.violated?.name,
    ce.name
  );
}

function jsonOf(ce) {
  if (!ce || typeof ce !== 'object') return undefined;
  return ce.json && typeof ce.json === 'object' ? ce.json : ce;
}

function formatTraceAction(action) {
  if (typeof action === 'string') return action;
  if (action === undefined || action === null) return undefined;
  return JSON.stringify(action);
}

function violationKind(ce) {
  const raw = typeof ce?.violated?.kind === 'string' ? ce.violated.kind.toLowerCase() : 'property';
  if (raw === 'unknown') return 'property';
  return raw;
}

function traceToGWT(ce) {
  if (!ce || typeof ce !== 'object' || !Array.isArray(ce.trace) || ce.trace.length === 0) return '';
  const firstState = ce.trace.find((step) => step && typeof step === 'object' && step.state !== undefined)?.state;
  const actions = ce.trace
    .map((step) => formatTraceAction(step?.action))
    .filter((action) => typeof action === 'string' && action.trim().length > 0);
  const property = propertyOf(ce);
  const given = firstState !== undefined ? `Given ${JSON.stringify(firstState)}` : '';
  const when = actions.length > 0 ? `\nWhen ${actions.join(' -> ')}` : '';
  const then = property ? `\nThen ${violationKind(ce)} "${property}" fails` : '';
  return `${given}${when}${then}`.trim();
}

function toGWT(ce){
  if (!ce) return '';
  if (typeof ce.gwt === 'string' && ce.gwt.trim().length > 0) return ce.gwt.trim();
  const traceGwt = traceToGWT(ce);
  if (traceGwt) return traceGwt;
  const given = ce.json?.given ? `Given ${JSON.stringify(ce.json.given)}` : '';
  const when = ce.json?.when ? `\nWhen ${JSON.stringify(ce.json.when)}` : '';
  const property = propertyOf(ce);
  const then = ce.json?.then?.violated ? `\nThen invariant \"${ce.json.then.violated}\" fails` : (property ? `\nThen property \"${property}\" fails` : '');
  return `${given}${when}${then}`.trim();
}

const source = selectCounterexampleSource();
if (!source) {
  console.log('No formal counterexamples found');
  process.exit(0);
}
const lines=[]; const items=[];
for (const ce of source.counterexamples){
  const gwt = toGWT(ce);
  if (gwt) lines.push(gwt);
  items.push({ property: propertyOf(ce), gwt, json: jsonOf(ce) });
}
fs.mkdirSync(path.dirname('artifacts/formal/gwt.txt'), { recursive: true });
fs.writeFileSync('artifacts/formal/gwt.txt', lines.join('\n\n'));
fs.writeFileSync('artifacts/formal/gwt.summary.json', JSON.stringify({ source: source.path, items }, null, 2));
console.log(`✓ Wrote artifacts/formal/gwt.txt and artifacts/formal/gwt.summary.json from ${source.label}`);
