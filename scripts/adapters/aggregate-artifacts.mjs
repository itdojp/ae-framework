#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function safeRead(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
function glob(dir){ try { return fs.readdirSync(dir).map(f=>path.join(dir,f)); } catch { return []; } }

const adaptersDir = 'artifacts';
const adapterSummaries = glob(adaptersDir)
  .filter(d => fs.statSync(d).isDirectory())
  .map(d => path.join(d,'summary.json'))
  .filter(p => fs.existsSync(p))
  .map(safeRead).filter(Boolean);

const formal = safeRead('formal/summary.json');
const props = safeRead('artifacts/properties/summary.json');
const ltlSuggestions = safeRead('artifacts/properties/ltl-suggestions.json');
const propDesign = safeRead('artifacts/properties/design.json');
const bdd = safeRead('artifacts/bdd/scenarios.json');
const combined = { adapters: adapterSummaries, formal, properties: props, propertyDesign: propDesign, bdd, ltlSuggestions };
fs.mkdirSync(path.dirname('artifacts/summary/combined.json'), { recursive: true });
fs.writeFileSync('artifacts/summary/combined.json', JSON.stringify(combined, null, 2));
console.log('✓ Wrote artifacts/summary/combined.json');
