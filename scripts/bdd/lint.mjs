#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function listFeatureFiles(dir='features'){ try { return fs.readdirSync(dir).filter(f=>f.endsWith('.feature')).map(f=>path.join(dir,f)); } catch { return []; } }
function read(p){ try { return fs.readFileSync(p,'utf-8'); } catch { return ''; } }

// Simple heuristic: When lines should mention an Aggregate Root (InventoryItem)
const ROOTS = [/\bInventoryItem\b/];

function lintContent(content, file){
  const lines=content.split(/\r?\n/);
  const violations=[];
  for (let i=0;i<lines.length;i++){
    const l=lines[i].trim();
    if (/^When\b/i.test(l)){
      const ok = ROOTS.some(r=>r.test(l)) && !/\bset to\b/i.test(l);
      if (!ok) violations.push({ file, line: i+1, message: 'When must use Aggregate Root command and avoid direct state mutation', text: l });
    }
  }
  return violations;
}

function writeJson(p,obj){ fs.mkdirSync(path.dirname(p),{recursive:true}); fs.writeFileSync(p, JSON.stringify(obj,null,2)); }

const files=listFeatureFiles();
if (files.length===0){ console.log('No .feature files found; skipping BDD lint'); process.exit(0); }
let all=[];
for (const f of files){ all = all.concat(lintContent(read(f), f)); }
writeJson('artifacts/bdd/lint.summary.json', { violations: all });
console.log(`BDD lint: ${all.length} violation(s)`);
process.exit(all.length?1:0);
