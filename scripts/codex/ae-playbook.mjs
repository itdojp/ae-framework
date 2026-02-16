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
  const args = {
    resume: false,
    skip: new Set(),
    enableFormal: false,
    formalTimeoutMs: 0,
    heartbeatMs: 30_000,
  };
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
    } else if (a.startsWith('--heartbeat-ms=')) {
      const v = Number(a.split('=')[1]);
      if (Number.isFinite(v) && v >= 0) args.heartbeatMs = Math.floor(v);
    }
  }
  return args;
}

async function ensureDir(dir) { await fs.mkdir(dir, { recursive: true }); }

async function writeJson(file, obj) {
  await ensureDir(path.dirname(file));
  await fs.writeFile(file, JSON.stringify(obj, null, 2));
}

export function formatDuration(ms) {
  const safeMs = Math.max(0, Number(ms) || 0);
  if (safeMs < 1000) return `${safeMs}ms`;
  const totalSec = Math.floor(safeMs / 1000);
  const min = Math.floor(totalSec / 60);
  const sec = totalSec % 60;
  return min > 0 ? `${min}m${sec}s` : `${totalSec}s`;
}

export function formatHeartbeatLine(phaseName, elapsedMs) {
  return `[ae-playbook] [${phaseName}] heartbeat elapsed=${formatDuration(elapsedMs)}\n`;
}

function phaseLog(phaseName, message) {
  process.stdout.write(`[ae-playbook] [${phaseName}] ${message}\n`);
}

function createDefaultContext() {
  return { phases: {} };
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

export async function teeTo(file, runner, options = {}) {
  await ensureDir(path.dirname(file));
  let log = '';
  const phaseName = (options.phaseName || 'run').toString();
  const heartbeatMs = Number.isFinite(options.heartbeatMs) ? Math.max(0, Math.floor(options.heartbeatMs)) : 30_000;
  const stdoutWriter = typeof options.stdoutWriter === 'function' ? options.stdoutWriter : (s) => process.stdout.write(s);
  const stderrWriter = typeof options.stderrWriter === 'function' ? options.stderrWriter : (s) => process.stderr.write(s);
  const streamStdout = options.streamStdout !== false;
  const streamStderr = options.streamStderr !== false;
  const startedAt = Date.now();

  const onStdout = (s) => {
    log += s;
    if (streamStdout) stdoutWriter(s);
  };
  const onStderr = (s) => {
    log += s;
    if (streamStderr) stderrWriter(s);
  };

  let heartbeat = null;
  if (heartbeatMs > 0) {
    heartbeat = setInterval(() => {
      stdoutWriter(formatHeartbeatLine(phaseName, Date.now() - startedAt));
    }, heartbeatMs);
    heartbeat.unref?.();
  }

  let res;
  try {
    res = await runner({ onStdout, onStderr });
  } finally {
    if (heartbeat) clearInterval(heartbeat);
  }
  await fs.writeFile(file, log);
  return res;
}

function migrateContext(raw) {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
    throw new Error('context.json must be an object');
  }
  const context = { ...raw };
  if (!context.phases || typeof context.phases !== 'object' || Array.isArray(context.phases)) {
    context.phases = {};
  }
  return context;
}

async function loadContext() {
  try {
    const text = await fs.readFile(CONTEXT_FILE, 'utf8');
    return migrateContext(JSON.parse(text));
  } catch (error) {
    if (error?.code === 'ENOENT') {
      return createDefaultContext();
    }
    if (error instanceof SyntaxError) {
      throw new Error(`context.json is invalid JSON: ${error.message}`);
    }
    if (error instanceof Error) {
      throw new Error(`context.json could not be loaded: ${error.message}`);
    }
    throw error;
  }
}

async function savePhase(context, name, data) {
  if (!context.phases || typeof context.phases !== 'object' || Array.isArray(context.phases)) {
    context.phases = {};
  }
  context.phases[name] = { ...data, timestamp: new Date().toISOString() };
  await writeJson(CONTEXT_FILE, context);
}

async function discoverSpec() {
  const candidates = [];
  const specRoots = ['spec', 'specs'];
  for (const root of specRoots) {
    const specDir = path.join(CWD, root);
    try {
      const entries = await fs.readdir(specDir, { withFileTypes: true });
      for (const e of entries) {
        if (!e.isFile()) continue;
        if (/\.(ya?ml|md)$/i.test(e.name)) candidates.push(path.join(root, e.name));
      }
    } catch { /* ignore */ }
  }
  // fallback common path
  const fallback = ['spec/app.yaml', 'spec/app.yml', 'specs/app.yaml', 'specs/app.yml'];
  for (const f of fallback) {
    try { await fs.access(path.join(CWD, f)); candidates.unshift(f); break; } catch {}
  }
  return candidates[0] || null;
}

async function runSetup(context, opts = {}) {
  const dir = path.join(ART_ROOT, 'setup');
  await ensureDir(dir);
  const log = path.join(dir, 'build.log');
  const startedAt = Date.now();
  phaseLog('setup', 'start');
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', 'corepack enable && pnpm i && pnpm build'], hooks), {
    phaseName: 'setup',
    heartbeatMs: opts.heartbeatMs,
  });
  phaseLog('setup', `done code=${res.code} elapsed=${formatDuration(Date.now() - startedAt)}`);
  await savePhase(context, 'setup', { code: res.code, log });
  return res.code === 0;
}

async function runQALight(context, opts = {}) {
  const dir = path.join(ART_ROOT, 'qa');
  await ensureDir(dir);
  const log = path.join(dir, 'qa-light.log');
  const startedAt = Date.now();
  phaseLog('qa', 'start');
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', 'pnpm -s run test:fast && (node dist/src/cli/index.js qa --light || pnpm -s tsx src/cli/qa-cli.ts --light)'], hooks), {
    phaseName: 'qa',
    heartbeatMs: opts.heartbeatMs,
  });
  phaseLog('qa', `done code=${res.code} elapsed=${formatDuration(Date.now() - startedAt)}`);
  await savePhase(context, 'qa', { code: res.code, log });
  return res.code === 0;
}

async function runSpecCompile(context, opts = {}) {
  const specIn = await discoverSpec();
  if (!specIn) {
    phaseLog('spec', 'skip reason=no spec input found');
    await savePhase(context, 'spec', { code: 0, skipped: true, reason: 'no spec input found' });
    return true;
  }
  const dir = path.join(ART_ROOT, 'spec');
  await ensureDir(dir);
  const out = path.join(dir, 'ir.json');
  const log = path.join(dir, 'spec-compile.log');
  phaseLog('spec', `start input=${specIn}`);
  const startedAt = Date.now();
  const cmd = `node dist/src/cli/index.js spec compile -i ${specIn} -o ${path.relative(CWD, out)} || pnpm -s ae-framework spec compile -i ${specIn} -o ${path.relative(CWD, out)} || pnpm -s tsx src/cli/index.ts spec compile -i ${specIn} -o ${path.relative(CWD, out)}`;
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', cmd], hooks), {
    phaseName: 'spec',
    heartbeatMs: opts.heartbeatMs,
  });
  const ok = res.code === 0;
  phaseLog('spec', `done code=${res.code} elapsed=${formatDuration(Date.now() - startedAt)}`);
  await savePhase(context, 'spec', { code: res.code, log, output: ok ? out : null, input: specIn });
  return ok;
}

async function runSimulation(context, opts = {}) {
  const ir = path.join(ART_ROOT, 'spec', 'ir.json');
  try { await fs.access(ir); } catch {
    phaseLog('sim', 'skip reason=no IR found');
    await savePhase(context, 'sim', { code: 0, skipped: true, reason: 'no IR found' });
    return true;
  }
  const script = path.join('scripts', 'simulation', 'deterministic-runner.mjs');
  try { await fs.access(path.join(CWD, script)); } catch {
    phaseLog('sim', 'skip reason=deterministic-runner not present');
    await savePhase(context, 'sim', { code: 0, skipped: true, reason: 'deterministic-runner not present' });
    return true;
  }
  const dir = path.join(ART_ROOT, 'sim');
  await ensureDir(dir);
  const out = path.join(dir, 'sim.json');
  const log = path.join(dir, 'sim.log');
  phaseLog('sim', `start input=${path.relative(CWD, ir)}`);
  const startedAt = Date.now();
  const cmd = `node ${script} --in ${path.relative(CWD, ir)} --out ${path.relative(CWD, out)}`;
  const res = await teeTo(log, (hooks) => sh('bash', ['-lc', cmd], hooks), {
    phaseName: 'sim',
    heartbeatMs: opts.heartbeatMs,
  });
  const ok = res.code === 0;
  phaseLog('sim', `done code=${res.code} elapsed=${formatDuration(Date.now() - startedAt)}`);
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
    phaseLog('formal', 'skip reason=no formal runners present');
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
  phaseLog('formal', 'start');
  const startedAt = Date.now();
  await teeTo(log, (hooks) => sh('bash', ['-lc', cmd], hooks), {
    phaseName: 'formal',
    heartbeatMs: opts.heartbeatMs,
  });
  phaseLog('formal', `done code=0 elapsed=${formatDuration(Date.now() - startedAt)}`);

  // Collect known outputs (if generated)
  const hr = path.join(CWD, 'artifacts/hermetic-reports', 'formal');
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
  try {
    const args = parseArgs(process.argv);
    await ensureDir(ART_ROOT);
    const context = args.resume ? await loadContext() : createDefaultContext();
    phaseLog('playbook', `start resume=${String(args.resume)} heartbeatMs=${args.heartbeatMs}`);

    const shouldSkip = (name) => args.skip.has(name) || args.skip.has('*');

    if (!shouldSkip('setup')) {
      const ok = await runSetup(context, { heartbeatMs: args.heartbeatMs });
      if (!ok) { console.error('Setup failed.'); process.exit(1); }
    } else {
      phaseLog('setup', 'skip requested');
      await savePhase(context, 'setup', { code: 0, skipped: true });
    }

    if (!shouldSkip('qa')) {
      const ok = await runQALight(context, { heartbeatMs: args.heartbeatMs });
      if (!ok) { console.error('QA (light) failed.'); process.exit(1); }
    } else {
      phaseLog('qa', 'skip requested');
      await savePhase(context, 'qa', { code: 0, skipped: true });
    }

    if (!shouldSkip('spec')) {
      await runSpecCompile(context, { heartbeatMs: args.heartbeatMs }); // non-fatal (skips when no spec)
    } else {
      phaseLog('spec', 'skip requested');
      await savePhase(context, 'spec', { code: 0, skipped: true });
    }

    if (!shouldSkip('sim')) {
      await runSimulation(context, { heartbeatMs: args.heartbeatMs }); // non-fatal
    } else {
      phaseLog('sim', 'skip requested');
      await savePhase(context, 'sim', { code: 0, skipped: true });
    }

    // Phase-3: Formal (opt-in, non-blocking)
    if (args.enableFormal && !shouldSkip('formal')) {
      await runFormal(context, { timeoutMs: args.formalTimeoutMs, heartbeatMs: args.heartbeatMs });
    } else {
      phaseLog('formal', args.enableFormal ? 'skip requested' : 'skip disabled');
      await savePhase(context, 'formal', { code: 0, skipped: true });
    }

    // Phase-4: Coverage/Adapters (report-only detection)
    if (!shouldSkip('coverage')) {
      phaseLog('coverage', 'start');
      await detectCoverage(context);
      phaseLog('coverage', 'done code=0');
    } else {
      phaseLog('coverage', 'skip requested');
      await savePhase(context, 'coverage', { code: 0, skipped: true });
    }
    if (!shouldSkip('adapters')) {
      phaseLog('adapters', 'start');
      await detectAdapters(context);
      phaseLog('adapters', 'done code=0');
    } else {
      phaseLog('adapters', 'skip requested');
      await savePhase(context, 'adapters', { code: 0, skipped: true });
    }

    console.log(`\n✔ Playbook completed. Context: ${path.relative(CWD, CONTEXT_FILE)}`);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error(`Playbook failed: ${message}`);
    process.exit(2);
  }
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
