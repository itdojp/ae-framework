#!/usr/bin/env node

/**
 * CodeX × ae-framework Playbook (Phase-2: minimal)
 *
 * Phases (minimal):
 *  1) setup    : corepack enable && pnpm i && pnpm build
 *  2) qa-light : pnpm run test:fast && (node dist/src/cli/index.js qa --light | fallback tsx)
 *  3) spec     : compile AE-Spec to IR (if spec file is present)
 *  4) sim      : (reserved, skipped if simulator script missing)
 *
 * Output: artifacts/ae/<phase>/*.log, artifacts/ae/context.json
 * Options: --resume, --skip=<comma list> (e.g., setup,qa,spec,sim)
 */

import { promises as fs } from 'fs';
import path from 'path';
import { spawn } from 'child_process';

const CWD = process.cwd();
const ART_ROOT = path.join(CWD, 'artifacts', 'ae');
const CONTEXT_FILE = path.join(ART_ROOT, 'context.json');

function parseArgs(argv) {
  const args = { resume: false, skip: new Set(), enableFormal: false, formalTimeoutMs: 0 };
  for (const a of argv.slice(2)) {
    if (a === '--resume') args.resume = true;
    else if (a.startsWith('--skip=')) {
      const parts = a.split('=')[1]?.split(',').map(s => s.trim()).filter(Boolean) || [];
      parts.forEach(p => args.skip.add(p));
    } else if (a === '--enable-formal') {
      args.enableFormal = true; // reserved (Phase-3)
    } else if (a.startsWith('--formal-timeout=')) {
      const v = Number(a.split('=')[1]);
      if (Number.isFinite(v) && v >= 0) args.formalTimeoutMs = v;
    }
  }
  return args;
}

async function ensureDir(dir) { await fs.mkdir(dir, { recursive: true }); }

async function writeJson(file, obj) {
  await ensureDir(path.dirname(file));
  await fs.writeFile(file, JSON.stringify(obj, null, 2));
}

function sh(cmd, args, opts) {
  return new Promise((resolve) => {
    const child = spawn(cmd, args, { cwd: CWD, env: process.env, shell: false });
    let out = '';
    let err = '';
    child.stdout?.on('data', d => { const s = d.toString(); out += s; opts?.onStdout?.(s); });
    child.stderr?.on('data', d => { const s = d.toString(); err += s; opts?.onStderr?.(s); });
    child.on('close', (code) => resolve({ code, stdout: out, stderr: err }));
    child.on('error', (e) => resolve({ code: 1, stdout: out, stderr: String(e?.message || e) }));
  });
}

async function teeTo(file, runner) {
  await ensureDir(path.dirname(file));
  let log = '';
  const append = async (s) => { log += s; };
  const res = await runner({ onStdout: append, onStderr: append });
  await fs.writeFile(file, log);
  return res;
}

async function loadContext() {
  try { return JSON.parse(await fs.readFile(CONTEXT_FILE, 'utf8')); } catch { return { phases: {} }; }
}

async function savePhase(context, name, data) {
  context.phases[name] = { ...data, timestamp: new Date().toISOString() };
  await writeJson(CONTEXT_FILE, context);
}

async function discoverSpec() {
  const candidates = [];
  const specDir = path.join(CWD, 'specs');
  try {
    const entries = await fs.readdir(specDir, { withFileTypes: true });
    for (const e of entries) {
      if (!e.isFile()) continue;
      if (/\.(ya?ml|md)$/i.test(e.name)) candidates.push(path.join('specs', e.name));
    }
  } catch { /* ignore */ }
  // fallback common path
  const fallback = ['specs/app.yaml', 'spec/app.yaml', 'spec/app.yml'];
  for (const f of fallback) {
    try { await fs.access(path.join(CWD, f)); candidates.unshift(f); break; } catch {}
  }
  return candidates[0] || null;
}

async function runSetup(context) {
  const dir = path.join(ART_ROOT, 'setup');
  await ensureDir(dir);
  const log = path.join(dir, 'build.log');
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', 'corepack enable && pnpm i && pnpm build'], hooks));
  await savePhase(context, 'setup', { code: res.code, log });
  return res.code === 0;
}

async function runQALight(context) {
  const dir = path.join(ART_ROOT, 'qa');
  await ensureDir(dir);
  const log = path.join(dir, 'qa-light.log');
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', 'pnpm -s run test:fast && (node dist/src/cli/index.js qa --light || pnpm -s tsx src/cli/qa-cli.ts --light)'], hooks));
  await savePhase(context, 'qa', { code: res.code, log });
  return res.code === 0;
}

async function runSpecCompile(context) {
  const specIn = await discoverSpec();
  if (!specIn) {
    await savePhase(context, 'spec', { code: 0, skipped: true, reason: 'no spec input found' });
    return true;
  }
  const dir = path.join(ART_ROOT, 'spec');
  await ensureDir(dir);
  const out = path.join(dir, 'ir.json');
  const log = path.join(dir, 'spec-compile.log');
  const cmd = `node dist/src/cli/index.js spec compile -i ${specIn} -o ${path.relative(CWD, out)} || pnpm -s ae-framework spec compile -i ${specIn} -o ${path.relative(CWD, out)} || pnpm -s tsx src/cli/index.ts spec compile -i ${specIn} -o ${path.relative(CWD, out)}`;
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', cmd], hooks));
  const ok = res.code === 0;
  await savePhase(context, 'spec', { code: res.code, log, output: ok ? out : null, input: specIn });
  return ok;
}

async function runSimulation(context) {
  const ir = path.join(ART_ROOT, 'spec', 'ir.json');
  try { await fs.access(ir); } catch {
    await savePhase(context, 'sim', { code: 0, skipped: true, reason: 'no IR found' });
    return true;
  }
  const script = path.join('scripts', 'simulation', 'deterministic-runner.mjs');
  try { await fs.access(path.join(CWD, script)); } catch {
    await savePhase(context, 'sim', { code: 0, skipped: true, reason: 'deterministic-runner not present' });
    return true;
  }
  const dir = path.join(ART_ROOT, 'sim');
  await ensureDir(dir);
  const out = path.join(dir, 'sim.json');
  const log = path.join(dir, 'sim.log');
  const cmd = `node ${script} --in ${path.relative(CWD, ir)} --out ${path.relative(CWD, out)}`;
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', cmd], hooks));
  const ok = res.code === 0;
  await savePhase(context, 'sim', { code: res.code, log, output: ok ? out : null });
  return ok;
}

async function runFormal(context, opts = {}) {
  const dir = path.join(ART_ROOT, 'formal');
  await ensureDir(dir);
  const log = path.join(dir, 'formal.log');
  const timeoutMs = Number(opts.timeoutMs || 0);
  const hasTla = await fs
    .access(path.join(CWD, 'scripts', 'formal', 'verify-tla.mjs'))
    .then(() => true)
    .catch(() => false);
  const hasApalache = await fs
    .access(path.join(CWD, 'scripts', 'formal', 'verify-apalache.mjs'))
    .then(() => true)
    .catch(() => false);

  if (!hasTla && !hasApalache) {
    await savePhase(context, 'formal', { code: 0, skipped: true, reason: 'no formal runners present' });
    return true;
  }

  const cmds = [];
  if (hasTla) {
    const argTimeout = timeoutMs > 0 ? ` --timeout=${timeoutMs}` : '';
    cmds.push(`node scripts/formal/verify-tla.mjs${argTimeout} || true`);
  }
  if (hasApalache) {
    const argTimeout = timeoutMs > 0 ? ` --timeout=${timeoutMs}` : '';
    cmds.push(`node scripts/formal/verify-apalache.mjs${argTimeout} || true`);
  }

  const cmd = cmds.join(' && ');
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', cmd], hooks));

  // Collect known outputs (if generated)
  const hr = path.join(CWD, 'hermetic-reports', 'formal');
  const summary = {};
  const files = [
    { key: 'tlaSummary', file: path.join(hr, 'tla-summary.json') },
    { key: 'apalacheSummary', file: path.join(hr, 'apalache-summary.json') },
    { key: 'apalacheLog', file: path.join(hr, 'apalache-output.txt') },
  ];
  for (const f of files) {
    try { await fs.access(f.file); summary[f.key] = path.relative(CWD, f.file); } catch {}
  }

  await savePhase(context, 'formal', { code: 0, log, ...summary });
  return true;
}

async function main() {
  const args = parseArgs(process.argv);
  await ensureDir(ART_ROOT);
  const context = args.resume ? await loadContext() : { phases: {} };

  const shouldSkip = (name) => args.skip.has(name) || args.skip.has('*');

  if (!shouldSkip('setup')) {
    const ok = await runSetup(context);
    if (!ok) { console.error('Setup failed.'); process.exit(1); }
  } else {
    await savePhase(context, 'setup', { code: 0, skipped: true });
  }

  if (!shouldSkip('qa')) {
    const ok = await runQALight(context);
    if (!ok) { console.error('QA (light) failed.'); process.exit(1); }
  } else {
    await savePhase(context, 'qa', { code: 0, skipped: true });
  }

  if (!shouldSkip('spec')) {
    await runSpecCompile(context); // non-fatal (skips when no spec)
  } else {
    await savePhase(context, 'spec', { code: 0, skipped: true });
  }

  if (!shouldSkip('sim')) {
    await runSimulation(context); // non-fatal
  } else {
    await savePhase(context, 'sim', { code: 0, skipped: true });
  }

  // Phase-3: Formal (opt-in, non-blocking)
  if (args.enableFormal && !shouldSkip('formal')) {
    await runFormal(context, { timeoutMs: args.formalTimeoutMs });
  } else {
    await savePhase(context, 'formal', { code: 0, skipped: true });
  }

  // Phase-4: Coverage/Adapters (report-only detection)
  if (!shouldSkip('coverage')) {
    await detectCoverage(context);
  } else {
    await savePhase(context, 'coverage', { code: 0, skipped: true });
  }
  if (!shouldSkip('adapters')) {
    await detectAdapters(context);
  } else {
    await savePhase(context, 'adapters', { code: 0, skipped: true });
  }

  console.log(`\n✔ Playbook completed. Context: ${path.relative(CWD, CONTEXT_FILE)}`);
}

async function detectCoverage(context) {
  const candidates = [
    path.join(CWD, 'coverage', 'coverage-summary.json'),
    path.join(CWD, 'artifacts', 'coverage', 'coverage-summary.json'),
  ];
  let found = null;
  for (const f of candidates) { try { await fs.access(f); found = f; break; } catch {} }
  const dir = path.join(ART_ROOT, 'coverage');
  await ensureDir(dir);
  const note = found ? { coverageSummary: path.relative(CWD, found) } : { note: 'coverage summary not found' };
  await savePhase(context, 'coverage', { code: 0, ...note });
  return true;
}

function adapterIdFromPath(rel) {
  const l = rel.toLowerCase();
  if (l.includes('lighthouse')) return 'lighthouse';
  if (l.includes('axe')) return 'axe';
  if (l.includes('jest')) return 'jest';
  if (l.includes('vitest')) return 'vitest';
  return null;
}

export function validateAdapterJson(relPath, json) {
  const warns = [];
  const base = (relPath || '').toString();
  const adapter = (json && typeof json.adapter === 'string') ? json.adapter.toLowerCase() : null;
  const guessed = adapterIdFromPath(base);
  const label = adapter || guessed || 'unknown';
  // status check
  const status = json?.status;
  const allowed = ['ok','warn','warning','error'];
  if (status !== undefined && !allowed.includes(String(status).toLowerCase())) {
    warns.push({ file: base, message: `invalid status: ${status}` });
  }
  // summary presence
  if (!(typeof json?.summary === 'string' && json.summary.trim().length)) {
    warns.push({ file: base, message: 'missing summary' });
  }
  // adapter kind checks (minimal)
  switch (label) {
    case 'lighthouse':
      // Expect at least a details array or a performance metric-like field in summary
      if (!Array.isArray(json?.details) && !/lighthouse|perf|performance/i.test(String(json?.summary||''))) {
        warns.push({ file: base, message: 'lighthouse: missing details or performance hint' });
      }
      break;
    case 'axe':
      // Expect violations info in summary or details
      if (!/axe|a11y|accessib/i.test(String(json?.summary||'')) && !Array.isArray(json?.violations)) {
        warns.push({ file: base, message: 'axe: missing violations or a11y hint' });
      }
      break;
    case 'jest':
    case 'vitest':
      // Expect passed/failed counts hint in summary
      if (!/(pass|fail|tests?)/i.test(String(json?.summary||''))) {
        warns.push({ file: base, message: `${label}: summary lacks pass/fail hint` });
      }
      break;
    default:
      if (!adapter && !guessed) {
        warns.push({ file: base, message: 'unknown adapter (no adapter field and cannot guess from path)' });
      }
  }
  return warns;
}

async function detectAdapters(context) {
  const dir = path.join(ART_ROOT, 'adapters');
  await ensureDir(dir);
  const roots = [path.join(CWD, 'artifacts', 'adapters'), path.join(CWD, 'artifacts', 'lighthouse')];
  const hits = [];
  const warnings = [];
  async function walk(root, depth = 0) {
    if (depth > 3) return; // limit depth
    let entries = [];
    try { entries = await fs.readdir(root, { withFileTypes: true }); } catch { return; }
    for (const e of entries) {
      const p = path.join(root, e.name);
      if (e.isDirectory()) { await walk(p, depth + 1); continue; }
      if (!e.isFile()) continue;
      if (p.endsWith('summary.json') || /\b(a11y|perf|lh)\.json$/i.test(p)) {
        hits.push(path.relative(CWD, p));
      }
    }
  }
  for (const r of roots) await walk(r, 0);
  // de-dup
  const uniq = Array.from(new Set(hits));
  // Light shape validation (warning only)
  for (const rel of uniq) {
    const abs = path.join(CWD, rel);
    try {
      const txt = await fs.readFile(abs, 'utf-8');
      const json = JSON.parse(txt);
      if (typeof json !== 'object' || json === null) { warnings.push({ file: rel, message: 'not an object' }); continue; }
      // Base checks + per-adapter minimal schema
      const baseWarns = validateAdapterJson(rel, json);
      for (const w of baseWarns) warnings.push(w);
    } catch (e) {
      warnings.push({ file: rel, message: `json parse failed: ${String(e && e.message || e)}` });
    }
  }
  // Persist validation (report-only)
  await writeJson(path.join(dir, 'adapters-validation.json'), { count: uniq.length, warnings });
  await savePhase(context, 'adapters', { code: 0, reports: uniq, warnings: warnings.length });
  return true;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch((e) => { console.error(e?.stack || e); process.exit(1); });
}
