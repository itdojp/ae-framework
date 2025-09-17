#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function listFeatureFiles(dir='features'){ try { return fs.readdirSync(dir).filter(f=>f.endsWith('.feature')).map(f=>path.join(dir,f)); } catch { return []; } }
function read(p){ try { return fs.readFileSync(p,'utf-8'); } catch { return ''; } }

// Simple heuristic roots; overridable via env BDD_ROOTS (comma-separated)
const ROOTS = (() => {
  const env = process.env.BDD_ROOTS;
  if (env && env.trim()) {
    return env.split(',').map(s=>s.trim()).filter(Boolean).map(n=>new RegExp(`\\b${n.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b`));
  }
  return [/\bInventoryItem\b/];
})();
const STRICT = !!(process.env.BDD_LINT_STRICT && process.env.BDD_LINT_STRICT !== '0' && process.env.BDD_LINT_STRICT.toLowerCase() !== 'false');

function lintContent(content, file){
  const lines=content.split(/\r?\n/);
  const violations=[];
  for (let i=0;i<lines.length;i++){
    const l=lines[i].trim();
    if (/^When\b/i.test(l)){
      const ok = ROOTS.some(r=>r.test(l)) && !/\bset to\b/i.test(l);
      if (!ok) violations.push({ file, line: i+1, message: 'When must use Aggregate Root command and avoid direct state mutation', text: l });
      if (STRICT && /\bshould\b/i.test(l)) {
        violations.push({ file, line: i+1, message: 'When should not contain modal verbs like "should" (use declarative command)', text: l });
      }
    }
    if (STRICT && /^Then\b/i.test(l)){
      if (/\bdatabase|sql|table|insert|update\b/i.test(l)){
        violations.push({ file, line: i+1, message: 'Then should not mention persistence concerns directly (behavioral outcome expected)', text: l });
      }
    }
    if (STRICT && /^Given\b/i.test(l)){
      if (/\bclick|button|ui|page|css|selector\b/i.test(l)){
        violations.push({ file, line: i+1, message: 'Given should avoid UI-specific terms (focus on domain state)', text: l });
      }
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
