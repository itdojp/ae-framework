#!/usr/bin/env node
// Lightweight Lean4 runner: runs `lake build` in spec/lean and writes a summary JSON. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--help' || a === '-h') args.help = true;
    else if (a === '--project' && next) { args.project = next; i += 1; }
    else if (a.startsWith('--project=')) { args.project = a.slice(10); }
    else if (a === '--timeout' && next) { args.timeout = next; i += 1; }
    else if (a.startsWith('--timeout=')) { args.timeout = a.slice(10); }
    else { args._.push(a); }
  }
  return args;
}

function commandExists(cmd) {
  const result = spawnSync(cmd, [], { stdio: 'ignore' });
  if (result.error && result.error.code === 'ENOENT') return false;
  return true;
}

function runCommand(cmd, cmdArgs, options = {}) {
  const result = spawnSync(cmd, cmdArgs, { encoding: 'utf8', cwd: options.cwd });
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  const output = `${stdout}${stderr}`;
  if (result.error) {
    return { available: false, status: result.status ?? null, output: output || (result.error.message ?? ''), errorCode: result.error.code ?? null };
  }
  return { available: true, status: result.status ?? null, output, errorCode: null };
}

function clamp(s, n = 4000) {
  const t = String(s || '');
  return t.length > n ? `${t.slice(0, n)}…` : t;
}

const args = parseArgs(process.argv);
if (args.help) {
  console.log('Usage: node scripts/formal/verify-lean.mjs [--project spec/lean] [--timeout <ms>]');
  process.exit(0);
}

const repoRoot = process.cwd();
const project = args.project || path.join('spec', 'lean');
const projectDir = path.resolve(repoRoot, project);
const outDir = path.join(repoRoot, 'artifacts', 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'lean-summary.json');
fs.mkdirSync(outDir, { recursive: true });

const timeoutMs = Number.isFinite(Number(args.timeout)) ? Number(args.timeout) : 0;
const timeoutSec = timeoutMs > 0 ? Math.max(1, Math.floor(timeoutMs / 1000)) : 0;
const haveTimeout = commandExists('timeout');

let ran = false;
let status = 'n/a';
let output = '';
let exitCode = null;

if (!fs.existsSync(projectDir)) {
  status = 'project_not_found';
  output = `Lean project directory not found: ${projectDir}`;
} else if (!commandExists('lake')) {
  status = 'tool_not_available';
  output = 'lake not found. Install Lean4 via elan and ensure $HOME/.elan/bin is on PATH.';
} else {
  const baseCmd = { cmd: 'lake', args: ['build'] };
  const runSpec = (timeoutSec > 0 && haveTimeout)
    ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
    : baseCmd;
  const res = runCommand(runSpec.cmd, runSpec.args, { cwd: projectDir });
  ran = res.available;
  exitCode = res.status;
  if (!res.available) {
    status = 'tool_not_available';
    output = clamp(res.output);
  } else {
    status = (timeoutSec > 0 && haveTimeout && res.status === 124) ? 'timeout' : (res.status === 0 ? 'ran' : 'failed');
    output = clamp(res.output);
  }
}

const summary = {
  tool: 'lean4',
  project: path.relative(repoRoot, projectDir),
  ran,
  status,
  exitCode,
  timestamp: new Date().toISOString(),
  output,
};

fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`Lean summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- project=${summary.project} status=${status}`);
process.exit(0);

