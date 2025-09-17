#!/usr/bin/env node
// BDD -> LTL property suggestions (report-only)
import fs from 'node:fs';
import path from 'node:path';

function globFeatures(root='features'){
  try {
    const entries = fs.readdirSync(root, { withFileTypes: true });
    const files = [];
    for (const e of entries){
      const p = path.join(root, e.name);
      if (e.isDirectory()) files.push(...globFeatures(p));
      else if (e.isFile() && p.endsWith('.feature')) files.push(p);
    }
    return files;
  } catch {
    return [];
  }
}

function read(p){ try { return fs.readFileSync(p,'utf8'); } catch { return ''; } }
function writeJson(p,obj){ fs.mkdirSync(path.dirname(p),{recursive:true}); fs.writeFileSync(p, JSON.stringify(obj,null,2)); }

function parseScenarioLines(content){
  const lines = content.split(/\r?\n/).map(l=>l.trim());
  const scenarios = [];
  let current = null;
  let featureTitle = '';
  for (const l of lines){
    if (l.toLowerCase().startsWith('feature:')) {
      featureTitle = l.slice(8).trim();
      continue;
    }
    if (/^scenario:/i.test(l)){
      if (current) scenarios.push(current);
      current = { title: l.replace(/^[Ss]cenario:\s*/, ''), given: [], when: [], then: [] };
      continue;
    }
    if (!current) continue;
    if (/^given\b/i.test(l)) current.given.push(l.replace(/^given\s*/i,''));
    else if (/^when\b/i.test(l)) current.when.push(l.replace(/^when\s*/i,''));
    else if (/^then\b/i.test(l)) current.then.push(l.replace(/^then\s*/i,''));
    else if (/^and\b/i.test(l)) {
      // Attach AND to the last non-empty section (then > when > given)
      const text = l.replace(/^and\s*/i,'');
      if (current.then.length) current.then.push(text);
      else if (current.when.length) current.when.push(text);
      else if (current.given.length) current.given.push(text);
    }
  }
  if (current) scenarios.push(current);
  return { featureTitle, scenarios };
}

function suggestLTL(s){
  // Very coarse templates from GWT:
  // For each When -> Then, propose: G( when -> F then )
  const props = [];
  for (const w of (s.when.length ? s.when : ['condition'])){
    for (const t of (s.then.length ? s.then : ['expected'])){
      const ltl = `G( (${w}) -> F(${t}) )`;
      props.push({ when: w, then: t, ltl });
    }
  }
  return props;
}

const featureFiles = globFeatures('specs/bdd');
const fallbackFiles = featureFiles.length ? [] : globFeatures('features');
const files = featureFiles.length ? featureFiles : fallbackFiles;

let allScenarios = [];
let title = '';
for (const f of files){
  const { featureTitle, scenarios } = parseScenarioLines(read(f));
  if (!title && featureTitle) title = featureTitle;
  for (const s of scenarios){
    const suggestions = suggestLTL(s);
    allScenarios.push({ file: f, title: s.title, given: s.given, when: s.when, then: s.then, suggestions });
  }
}

// Write BDD scenarios summary for PR summary aggregation (criteriaCount/title best-effort)
const bddOut = { title: title || (files[0] ? path.basename(files[0]) : 'Feature'), criteriaCount: allScenarios.length };
writeJson('artifacts/bdd/scenarios.json', bddOut);

// Write suggestions in a dedicated file
writeJson('artifacts/properties/ltl-suggestions.json', { count: allScenarios.reduce((acc, s)=> acc + (s.suggestions?.length||0), 0), items: allScenarios });

console.log(`BDD→LTL suggestions: scenarios=${allScenarios.length}, files=${files.length}`);
process.exit(0);

