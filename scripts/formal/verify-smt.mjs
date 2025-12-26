#!/usr/bin/env node
// Lightweight SMT runner: accepts --solver and --file, runs if available, writes a summary. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--help' || a === '-h') args.help = true;
    else if (a === '--file' && argv[i+1]) { args.file = argv[++i]; }
    else if (a.startsWith('--file=')) { args.file = a.slice(7); }
    else if (a.startsWith('--solver=')) { args.solver = a.slice(9); }
    else { args._.push(a); }
  }
  return args;
}

function commandExists(cmd) {
  const result = spawnSync(cmd, [], { stdio: 'ignore' });
  if (result.error && result.error.code === 'ENOENT') {
    return false;
  }
  return true;
}

function runCommand(cmd, cmdArgs) {
  const result = spawnSync(cmd, cmdArgs, { encoding: 'utf8' });
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  let output = `${stdout}${stderr}`;
  if (result.error) {
    if (!output && result.error.message) {
      output = result.error.message;
    }
    return {
      available: false,
      status: result.status ?? null,
      output,
      errorCode: result.error.code ?? null,
    };
  }
  return {
    available: true,
    status: result.status ?? null,
    output,
    errorCode: null,
  };
}

const args = parseArgs(process.argv);
const timeoutSec = args.timeout ? Math.max(1, Math.floor(Number(args.timeout)/1000)) : 0;
const haveTimeout = commandExists('timeout');
const timeoutRequested = timeoutSec > 0;
const timeoutIgnored = timeoutRequested && !haveTimeout;
if (args.help) {
  console.log(`Usage: node scripts/formal/verify-smt.mjs [--solver=z3|cvc5] [--file path/to/input.smt2]`);
  console.log('See docs/quality/formal-tools-setup.md for solver setup.');
  process.exit(0);
}

const solver = (args.solver || 'z3').toLowerCase();
const file = args.file;

const repoRoot = path.resolve(process.cwd());
const outDir = path.join(repoRoot, 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'smt-summary.json');
fs.mkdirSync(outDir, { recursive: true });

let status;
let output = '';
let ran = false;

if (!file) {
  status = 'no_file';
} else if (!fs.existsSync(file)) {
  status = 'file_not_found';
  output = `SMT-LIB file not found: ${file}`;
} else if (solver === 'z3' && commandExists('z3')) {
  const baseCmd = { cmd: 'z3', args: ['-smt2', file] };
  const runSpec = (timeoutSec && haveTimeout)
    ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
    : baseCmd;
  const result = runCommand(runSpec.cmd, runSpec.args);
  if (!result.available) {
    status = 'solver_not_available';
    if (runSpec.cmd === 'timeout') {
      output = `Command 'timeout' not found while invoking solver '${solver}'. See docs/quality/formal-tools-setup.md`;
    } else if (result.errorCode && result.errorCode !== 'ENOENT') {
      output = `Failed to execute solver '${solver}' (${result.errorCode}). See docs/quality/formal-tools-setup.md`;
    } else {
      output = `Solver '${solver}' not found. See docs/quality/formal-tools-setup.md`;
    }
  } else {
    output = result.output;
    ran = true;
    status = (timeoutSec && haveTimeout && result.status === 124) ? 'timeout' : 'ran';
    if (timeoutIgnored) {
      output = `Timeout requested (${timeoutSec}s) but 'timeout' is unavailable; running without timeout.\n${output}`;
    }
  }
} else if (solver === 'cvc5' && commandExists('cvc5')) {
  const baseCmd = { cmd: 'cvc5', args: ['--lang=smt2', file] };
  const runSpec = (timeoutSec && haveTimeout)
    ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
    : baseCmd;
  const result = runCommand(runSpec.cmd, runSpec.args);
  if (!result.available) {
    status = 'solver_not_available';
    if (runSpec.cmd === 'timeout') {
      output = `Command 'timeout' not found while invoking solver '${solver}'. See docs/quality/formal-tools-setup.md`;
    } else if (result.errorCode && result.errorCode !== 'ENOENT') {
      output = `Failed to execute solver '${solver}' (${result.errorCode}). See docs/quality/formal-tools-setup.md`;
    } else {
      output = `Solver '${solver}' not found. See docs/quality/formal-tools-setup.md`;
    }
  } else {
    output = result.output;
    ran = true;
    status = (timeoutSec && haveTimeout && result.status === 124) ? 'timeout' : 'ran';
    if (timeoutIgnored) {
      output = `Timeout requested (${timeoutSec}s) but 'timeout' is unavailable; running without timeout.\n${output}`;
    }
  }
} else {
  status = 'solver_not_available';
  output = `Solver '${solver}' not found. See docs/quality/formal-tools-setup.md`;
}

if (!status) {
  status = 'unknown';
}

const summary = {
  solver,
  file: file || null,
  ran,
  status,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000)
};

fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`SMT summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- solver=${solver} status=${status}${ran ? '' : ''}`);

// Non-blocking
process.exit(0);
