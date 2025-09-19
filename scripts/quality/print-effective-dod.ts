#!/usr/bin/env -S node

/**
 * Print Composite Definition of Done (DoD) preview (report-only).
 * - Sources: policy/quality.json, .ae/ae-ir.json (optional dod), ae.config.*
 * - Merge: strictest per RFC (policy > AE-IR > ae.config precedence fallback)
 * - Phase 0: logging only; does not change any gating.
 */

import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

type Enforcement = 'off' | 'warn' | 'strict';
const enforcementRank: Record<Enforcement, number> = { off: 0, warn: 1, strict: 2 };

function strictestEnforcement(values: (Enforcement | undefined)[]): Enforcement | undefined {
  const present = values.filter(Boolean) as Enforcement[];
  if (!present.length) return undefined;
  return present.sort((a, b) => enforcementRank[b] - enforcementRank[a])[0];
}

// Higher is stricter (e.g., coverage minimums)
function strictestHigher(values: Array<number | undefined>): number | undefined {
  const nums = values.filter((v): v is number => typeof v === 'number' && isFinite(v));
  return nums.length ? Math.max(...nums) : undefined;
}

// Lower is stricter (e.g., max allowed issues)
function strictestLower(values: Array<number | undefined>): number | undefined {
  const nums = values.filter((v): v is number => typeof v === 'number' && isFinite(v));
  return nums.length ? Math.min(...nums) : undefined;
}

function deepClone<T>(obj: T): T {
  return obj == null ? obj : JSON.parse(JSON.stringify(obj));
}

function setByPath(obj: any, dottedPath: string, value: any) {
  const keys = dottedPath.split('.');
  let cur = obj;
  for (let i = 0; i < keys.length - 1; i++) {
    const k = keys[i];
    if (typeof cur[k] !== 'object' || cur[k] === null) cur[k] = {};
    cur = cur[k];
  }
  cur[keys[keys.length - 1]] = value;
}

function applyOverrides(quality: any, overrides: Record<string, any> | undefined) {
  if (!overrides) return quality;
  const out = deepClone(quality);
  for (const [k, v] of Object.entries(overrides)) setByPath(out, k, v);
  return out;
}

function readJSON(file: string): any | null {
  try {
    if (fs.existsSync(file)) return JSON.parse(fs.readFileSync(file, 'utf-8'));
  } catch {
    // ignore
  }
  return null;
}

async function loadRepoConfig(): Promise<any | null> {
  const cwd = process.cwd();
  const candidates = ['ae.config.ts', 'ae.config.js', 'ae.config.json'];
  for (const filename of candidates) {
    const full = path.join(cwd, filename);
    if (!fs.existsSync(full)) continue;
    try {
      if (filename.endsWith('.json')) {
        return readJSON(full);
      } else if (filename.endsWith('.js')) {
        // ESM dynamic import
        const mod = await import(pathToFileURL(full).href);
        return mod.default ?? mod;
      } else {
        // .ts — run under tsx so dynamic import should work
        const mod = await import(pathToFileURL(full).href);
        return mod.default ?? mod;
      }
    } catch {
      // ignore and try next
    }
  }
  return null;
}

type Coverage = { lines?: number; branches?: number; functions?: number; statements?: number };

type SourceCov = {
  enforcement?: Enforcement;
  thresholds?: Coverage;
  source: 'policy' | 'aeir' | 'repo';
};

function fmtCoverage(cov?: Coverage): string {
  if (!cov) return 'n/a';
  const keys: (keyof Coverage)[] = ['lines', 'branches', 'functions', 'statements'];
  return keys
    .map(k => (cov[k] !== undefined ? `${k}:${(cov[k] as number)}` : null))
    .filter(Boolean)
    .join(', ');
}

async function main() {
  const mode = (process.argv.find(a => a.startsWith('--mode='))?.split('=')[1] || 'ci') as 'ci' | 'dev';

  // 1) Policy
  const policy = readJSON('policy/quality.json');
  const baseQuality = policy?.quality ?? {};
  const envOverrides = mode === 'ci' ? policy?.environments?.ci?.overrides : policy?.environments?.development?.overrides;
  const pQuality = applyOverrides(baseQuality, envOverrides);
  const policyCov: SourceCov = {
    source: 'policy',
    enforcement: pQuality?.coverage?.enforcement,
    thresholds: pQuality?.coverage?.thresholds,
  };

  // 2) AE-IR (optional)
  const aeir = readJSON('.ae/ae-ir.json');
  const aeirDod = aeir?.dod ?? null;
  const aeirCov: SourceCov | null = aeirDod
    ? {
        source: 'aeir',
        enforcement: aeirDod?.coverage?.enforcement ?? aeirDod?.enforcement,
        thresholds: aeirDod?.coverage?.thresholds,
      }
    : null;

  // 3) Repo config (optional, least precedence on fallback)
  const repoCfg = await loadRepoConfig();
  const repoCov: SourceCov | null = repoCfg?.qa?.coverageThreshold
    ? { source: 'repo', thresholds: deepClone(repoCfg.qa.coverageThreshold) }
    : null;

  // Strictest merge for coverage
  const candidates: SourceCov[] = [policyCov, aeirCov || undefined, repoCov || undefined].filter(Boolean) as SourceCov[];
  const eff: Coverage = {
    lines: strictestHigher(candidates.map(c => c.thresholds?.lines)),
    branches: strictestHigher(candidates.map(c => c.thresholds?.branches)),
    functions: strictestHigher(candidates.map(c => c.thresholds?.functions)),
    statements: strictestHigher(candidates.map(c => c.thresholds?.statements)),
  };
  const effEnf = strictestEnforcement(candidates.map(c => c.enforcement));

  // Fallback precedence if all undefined
  function fallback<T>(vals: (T | undefined)[], fb?: T): T | undefined {
    for (const v of vals) if (v !== undefined) return v;
    return fb;
  }
  const fbOrder = [policyCov, aeirCov || undefined, repoCov || undefined].filter(Boolean) as SourceCov[];
  eff.lines = fallback([eff.lines, policyCov.thresholds?.lines, aeirCov?.thresholds?.lines, repoCov?.thresholds?.lines]);
  eff.branches = fallback([eff.branches, policyCov.thresholds?.branches, aeirCov?.thresholds?.branches, repoCov?.thresholds?.branches]);
  eff.functions = fallback([eff.functions, policyCov.thresholds?.functions, aeirCov?.thresholds?.functions, repoCov?.thresholds?.functions]);
  eff.statements = fallback([eff.statements, policyCov.thresholds?.statements, aeirCov?.thresholds?.statements, repoCov?.thresholds?.statements]);

  const header = '— Composite DoD (preview; strictest merge, report-only) —';
  console.log(header);
  console.log(`Sources: policy > AE-IR > ae.config (fallback precedence)`);
  console.log(`Mode: ${mode}`);
  console.log('');
  console.log('Coverage (derived)');
  console.log(`- policy      : ${fmtCoverage(policyCov.thresholds)}${policyCov.enforcement ? `; enforcement=${policyCov.enforcement}` : ''}`);
  console.log(`- AE-IR (dod) : ${aeirCov ? fmtCoverage(aeirCov.thresholds) : 'n/a'}${aeirCov?.enforcement ? `; enforcement=${aeirCov.enforcement}` : ''}`);
  console.log(`- ae.config   : ${repoCov ? fmtCoverage(repoCov.thresholds) : 'n/a'}`);
  console.log('');
  console.log('Coverage (effective — strictest per metric)');
  console.log(`- lines      ≥ ${eff.lines ?? 'n/a'}`);
  console.log(`- branches   ≥ ${eff.branches ?? 'n/a'}`);
  console.log(`- functions  ≥ ${eff.functions ?? 'n/a'}`);
  console.log(`- statements ≥ ${eff.statements ?? 'n/a'}`);
  console.log(`- enforcement: ${effEnf ?? 'n/a'}`);
  console.log('');
  console.log('Note: This is a Phase 0 preview for visibility only.');
  console.log('      Gating behavior remains unchanged.');
}

main().catch(err => {
  console.error('Failed to print Composite DoD preview:', err);
  process.exit(0); // non-blocking by design
});

