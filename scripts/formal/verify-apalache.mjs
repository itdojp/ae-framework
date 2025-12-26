#!/usr/bin/env node
// Lightweight Apalache runner (stub/minimal):
// - Detects apalache CLI presence (apalache-mc or apalache)
// - Optionally runs a quick check when available
// - Always writes a summary JSON (non-blocking)
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { computeOkFromOutput } from './heuristics.mjs';

function parseArgs(argv){
  const args = { _: [] };
  for (let i=2;i<argv.length;i++){
    const a = argv[i];
    if (a==='-h' || a==='--help') args.help = true;
    else if (a==='--file' && argv[i+1]) { args.file = argv[++i]; }
    else if (a.startsWith('--file=')) { args.file = a.slice(7); }
    else if (a==='--timeout' && argv[i+1]) { args.timeout = Number(argv[++i]); }
    else if (a.startsWith('--timeout=')) { args.timeout = Number(a.slice(10)); }
    else { args._.push(a); }
  }
  return args;
}

function commandExists(cmd){
  const result = spawnSync(cmd, [], { stdio: 'ignore' });
  if (result.error && result.error.code === 'ENOENT') {
    return false;
  }
  return true;
}

function runCommand(cmd, cmdArgs){
  const result = spawnSync(cmd, cmdArgs, { encoding: 'utf8' });
  if (result.error) {
    if (result.error.code === 'ENOENT') {
      return { available: false, success: false, status: null, signal: null, output: '' };
    }
    return {
      available: true,
      success: false,
      status: result.status ?? null,
      signal: result.signal ?? null,
      output: result.error.message ?? '',
    };
  }
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  return {
    available: true,
    success: result.status === 0,
    status: result.status ?? null,
    signal: result.signal ?? null,
    output: `${stdout}${stderr}`,
  };
}

function resolveCommandPath(cmd){
  if (!commandExists('which')) return '';
  const result = runCommand('which', [cmd]);
  if (!result.available || !result.success) return '';
  return result.output.trim().split(/\r?\n/)[0] || '';
}

const args = parseArgs(process.argv);
if (args.help){
  console.log('Usage: node scripts/formal/verify-apalache.mjs [--file spec/tla/DomainSpec.tla]');
  process.exit(0);
}

const repoRoot = path.resolve(process.cwd());
const file = args.file || process.env.APALACHE_FILE || path.join('spec','tla','DomainSpec.tla');
const absFile = path.resolve(repoRoot, file);
const outDir = path.join(repoRoot, 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'apalache-summary.json');
const outLog = path.join(outDir, 'apalache-output.txt');
fs.mkdirSync(outDir, { recursive: true });

const haveApalacheMc = commandExists('apalache-mc');
const haveApalache = haveApalacheMc || commandExists('apalache');
const haveTimeout = commandExists('timeout');
const apalacheCmd = haveApalacheMc ? 'apalache-mc' : (haveApalache ? 'apalache' : '');
let status;
let ran = false;
let output = '';
let version = '';
let toolPath = '';
let timeMs = 0;

if (!fs.existsSync(absFile)){
  status = 'file_not_found';
  output = `TLA file not found: ${absFile}\nSee docs/quality/formal-runbook.md (Reproduce Locally).`;
} else if (!haveApalache){
  status = 'tool_not_available';
  output = 'Apalache CLI not found. Install apalache or ensure apalache-mc is on PATH. See docs/quality/formal-tools-setup.md';
} else {
  // Minimal "typecheck" like run; apalache-mc supports: apalache-mc check <Spec>
  const baseCmd = { cmd: apalacheCmd, args: ['check', absFile] };
  const useTimeout = Boolean(args.timeout && Number.isFinite(args.timeout) && args.timeout > 0 && haveTimeout);
  const timeoutSecs = useTimeout ? Math.max(1, Math.floor(Number(args.timeout)/1000)) : 0;
  const runSpec = useTimeout
    ? { cmd: 'timeout', args: [`${timeoutSecs}s`, baseCmd.cmd, ...baseCmd.args] }
    : baseCmd;
  const t0 = Date.now();
  const res = runCommand(runSpec.cmd, runSpec.args);
  timeMs = Date.now() - t0;
  if (!res.available) {
    status = 'tool_not_available';
    output = 'Apalache CLI not found. Install apalache or ensure apalache-mc is on PATH. See docs/quality/formal-tools-setup.md';
  } else {
    output = res.output;
    ran = true;
    // Detect timeout exit (GNU timeout returns 124)
    if (useTimeout && (res.status === 124 || /timeout:/.test(output))) {
      status = 'timeout';
    } else {
      status = 'ran';
    }
  }
  // Try to get version string
  const versionRes = runCommand(apalacheCmd, ['version']);
  version = versionRes.output.trim().split(/\r?\n/)[0] || '';
  toolPath = resolveCommandPath(apalacheCmd);
}

// Tuning via env (defaults keep current behavior)
const ERRORS_LIMIT = Number(process.env.APALACHE_ERRORS_LIMIT || '5');
const ERROR_LINE_CLAMP = Number(process.env.APALACHE_ERROR_LINE_CLAMP || '200');
const SNIPPET_BEFORE = Number(process.env.APALACHE_SNIPPET_BEFORE || '2');
const SNIPPET_AFTER = Number(process.env.APALACHE_SNIPPET_AFTER || '2');
const OUTPUT_CLAMP = Number(process.env.APALACHE_OUTPUT_CLAMP || '4000');

function extractErrors(out){
  const lines = (out || '').split(/\r?\n/);
  const key = /error|violat|counterexample|fail|unsatisfied|unsat\b|dead\s*lock|dead\s*end/i;
  const picked = [];
  for (const l of lines) { if (key.test(l)) picked.push(l.trim()); if (picked.length>=ERRORS_LIMIT) break; }
  // Trim very long lines for readability in aggregate comments
  return picked.map(l => l.length > ERROR_LINE_CLAMP ? (l.slice(0, ERROR_LINE_CLAMP) + '…') : l);
}
function countErrors(out){
  const lines = (out || '').split(/\r?\n/);
  const key = /error|violat|counterexample|fail|unsatisfied|unsat\b|dead\s*lock|dead\s*end/i;
  let n = 0; for (const l of lines) if (key.test(l)) n++;
  return n;
}
function extractErrorSnippet(out, before=SNIPPET_BEFORE, after=SNIPPET_AFTER){
  const lines = (out || '').split(/\r?\n/);
  const key = /error|violat|counterexample|fail|unsatisfied|unsat\b|dead\s*lock|dead\s*end/i;
  for (let i=0;i<lines.length;i++){
    if (key.test(lines[i])){
      const start = Math.max(0, i-before);
      const end = Math.min(lines.length, i+after+1);
      return {
        index: i,
        start,
        end,
        before,
        after,
        lines: lines.slice(start, end).map(s=>s.trim())
      };
    }
  }
  return null;
}

// Persist raw output for artifact consumers
try { fs.writeFileSync(outLog, output, 'utf-8'); } catch {}

// computeOkFromOutput imported from heuristics.mjs

const summary = {
  tool: 'apalache',
  file: path.relative(repoRoot, absFile),
  detected: haveApalache,
  ran,
  status,
  version: version || null,
  ok: ran ? (computeOkFromOutput(output)) : null,
  hints: ran ? ( /success|ok|no\s+(?:errors|counterexamples?)/i.test(output) ? 'success-indicators-found' : null ) : null,
  timeMs: timeMs || null,
  toolPath: toolPath || null,
  run: (process.env.GITHUB_SERVER_URL && process.env.GITHUB_REPOSITORY && process.env.GITHUB_RUN_ID)
    ? `${process.env.GITHUB_SERVER_URL}/${process.env.GITHUB_REPOSITORY}/actions/runs/${process.env.GITHUB_RUN_ID}`
    : null,
  timestamp: new Date().toISOString(),
  errors: ran ? extractErrors(output) : [],
  errorCount: ran ? countErrors(output) : 0,
  errorSnippet: ran ? extractErrorSnippet(output) : null,
  // capped raw output preview (full log saved to outputFile)
  output: output ? String(output).slice(0, OUTPUT_CLAMP) : '',
  outputFile: path.relative(repoRoot, outLog)
};

fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`Apalache summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- detected=${haveApalache} status=${status}`);

// Non-blocking
process.exit(0);
