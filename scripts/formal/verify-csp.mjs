#!/usr/bin/env node
// Lightweight CSP runner stub: executes CSP_RUN_CMD if provided and writes a summary JSON. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--help' || a === '-h') args.help = true;
    else if (a === '--file' && next) { args.file = next; i += 1; }
    else if (a.startsWith('--file=')) { args.file = a.slice(7); }
    else { args._.push(a); }
  }
  return args;
}

function commandExists(cmd) {
  const result = spawnSync(cmd, [], { stdio: 'ignore' });
  if (result.error && result.error.code === 'ENOENT') return false;
  return true;
}

function runShell(cmd) {
  const result = spawnSync(cmd, { shell: true, encoding: 'utf8' });
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  const output = `${stdout}${stderr}`.trim();
  if (result.error) {
    return {
      available: false,
      success: false,
      status: result.status ?? null,
      output: output || (result.error.message ?? ''),
    };
  }
  return { available: true, success: result.status === 0, status: result.status ?? 0, output };
}

function clamp(s, n = 4000) {
  const t = String(s || '');
  return t.length > n ? `${t.slice(0, n)}…` : t;
}

const args = parseArgs(process.argv);
if (args.help) {
  console.log('Usage: node scripts/formal/verify-csp.mjs [--file spec/csp/sample.cspm]');
  console.log('Optional: set CSP_RUN_CMD to execute a CSP tool (supports {file}).');
  process.exit(0);
}

const repoRoot = process.cwd();
const file = args.file || path.join('spec', 'csp', 'sample.cspm');
const absFile = path.resolve(repoRoot, file);
const outDir = path.join(repoRoot, 'artifacts', 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'csp-summary.json');
fs.mkdirSync(outDir, { recursive: true });

let ran = false;
let status = 'n/a';
let output = '';
let exitCode = null;

if (!fs.existsSync(absFile)) {
  status = 'file_not_found';
  output = `CSP file not found: ${absFile}`;
} else {
  const runCmd = process.env.CSP_RUN_CMD;
  if (runCmd) {
    const cmd = runCmd.replace(/{file}/g, absFile);
    const res = runShell(cmd);
    ran = res.available;
    exitCode = res.status;
    status = res.available ? (res.success ? 'ran' : 'failed') : 'tool_not_available';
    output = clamp(res.output || 'CSP_RUN_CMD produced no output');
  } else {
    // Best-effort detection: actual execution depends on selected toolchain.
    const known = ['fdr4', 'fdr', 'refines', 'cspm'];
    const found = known.filter((c) => commandExists(c));
    status = 'tool_not_available';
    output = found.length
      ? `CSP tool detected (${found.join(', ')}), but CSP_RUN_CMD is not set; execution is not configured.`
      : 'No CSP tool configured. Set CSP_RUN_CMD or install a CSP tool.';
  }
}

const summary = {
  tool: 'csp',
  file: path.relative(repoRoot, absFile),
  ran,
  status,
  exitCode,
  timestamp: new Date().toISOString(),
  output,
};
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`CSP summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- file=${summary.file} status=${status}`);
process.exit(0);

