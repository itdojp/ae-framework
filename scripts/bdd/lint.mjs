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
      if (STRICT && /\bclick|button|ui|page|css|selector\b/i.test(l)){
        violations.push({ file, line: i+1, message: 'When should avoid UI-specific terms (use domain command)', text: l });
      }
    }
    if (STRICT && /^Then\b/i.test(l)){
      if (/\bdatabase|sql|table|insert|update\b/i.test(l)){
        violations.push({ file, line: i+1, message: 'Then should not mention persistence concerns directly (behavioral outcome expected)', text: l });
      }
      const andCount = (l.match(/\bAnd\b/gi) || []).length;
      if (andCount >= 2) {
        violations.push({ file, line: i+1, message: 'Then has too many conjunctions (prefer small, focused expectations)', text: l });
      }
      // "and then" repeated (STRICT)
      const andThenCount = (l.match(/\band\s+then\b/gi) || []).length;
      if (andThenCount >= 2) {
        violations.push({ file, line: i+1, message: 'Avoid repeated "and then"; prefer separate steps', text: l });
      }
    }
    if (STRICT && /^Given\b/i.test(l)){
      if (/\bclick|button|ui|page|css|selector\b/i.test(l)){
        violations.push({ file, line: i+1, message: 'Given should avoid UI-specific terms (focus on domain state)', text: l });
      }
    }
    // Ambiguous words (STRICT): "maybe/approximately/around/roughly/about"
    if (STRICT && /(\bmaybe\b|\bapproximately\b|\baround\b|\broughly\b|\babout\b)/i.test(l)){
      violations.push({ file, line: i+1, message: 'Ambiguous wording detected (prefer precise, testable phrasing)', text: l });
    }
    // Ambiguous tails (STRICT): etc./and so on/...
    if (STRICT && /(\betc\.?\b|and\s+so\s+on|\.\.\.)/i.test(l)){
      violations.push({ file, line: i+1, message: 'Avoid ambiguous tails like "etc."/"and so on"/"..."', text: l });
    }
    // Double negatives (STRICT): simple patterns（"not only ... but also" は除外）
    if (STRICT) {
      const dn = /(\bnot\b\s+.*\bnot\b|can't\s+not|cannot\s+not|don't\s+not|never\s+not)/i.test(l);
      const whitelist = /\bnot\s+only\b[\s\S]*\bbut\s+(also\b)?/i.test(l);
      if (dn && !whitelist) {
        violations.push({ file, line: i+1, message: 'Double negative detected (prefer direct, positive phrasing)', text: l });
      }
    }
    // Intensifiers (STRICT): very/so/really/extremely (warn for overuse)
    if (STRICT && /(\bvery\b|\breally\b|\bextremely\b|\bso\b\s+(?!that)\b\w+)/i.test(l)){
      violations.push({ file, line: i+1, message: 'Intensifier detected (prefer precise, measurable criteria over very/so/really)', text: l });
    }
    // Repeated intensifiers (STRICT): really very / very very / so so
    if (STRICT && /(really\s+very|very\s+very|\bso\b\s+\bso\b)/i.test(l)){
      violations.push({ file, line: i+1, message: 'Repeated intensifier detected (avoid "really very"/"very very"/"so so")', text: l });
    }
    // "should be" pattern (STRICT): prefer declarative outcomes
    if (STRICT && /\bshould\s+be\b/i.test(l)){
      violations.push({ file, line: i+1, message: 'Prefer declarative outcomes over "should be" phrasing', text: l });
    }
    // "should be able to" (STRICT): prefer capability as acceptance criteria
    if (STRICT && /\bshould\s+be\s+able\s+to\b/i.test(l)){
      violations.push({ file, line: i+1, message: 'Prefer concrete, testable capability over "should be able to"', text: l });
    }
    // Passive voice (STRICT): "is/are/was/were <verb>ed by"（false positive を避けるため by を必須に）
    if (STRICT && /(\bis\b|\bare\b|\bwas\b|\bwere\b)\s+\w+ed\s+by\b/i.test(l)){
      violations.push({ file, line: i+1, message: 'Passive voice detected (prefer active voice in steps)', text: l });
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
