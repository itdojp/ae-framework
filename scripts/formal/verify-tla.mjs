#!/usr/bin/env node
// Lightweight TLA runner: accepts --engine and --file, tries to run Apalache or TLC if available; writes a summary. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv){
  const args = { _: [] };
  for (let i=2;i<argv.length;i++){
    const a=argv[i];
    if (a==='-h'||a==='--help') args.help=true;
    else if (a.startsWith('--engine=')) { args.engine=a.slice(9); }
    else if ((a==='--engine' || a==='-e') && argv[i+1]) { args.engine=argv[++i]; }
    else if (a.startsWith('--file=')) { args.file=a.slice(7); }
    else if (a==='--file' && argv[i+1]) { args.file=argv[++i]; }
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

const args = parseArgs(process.argv);
const timeoutSec = args.timeout ? Math.max(1, Math.floor(Number(args.timeout)/1000)) : 0;
const haveTimeout = commandExists('timeout');
if (args.help){
  console.log(`Usage: node scripts/formal/verify-tla.mjs [--engine=tlc|apalache] [--file spec/tla/DomainSpec.tla] [--timeout <ms>]`);
  console.log('See docs/quality/formal-tools-setup.md for TLC/Apalache setup.');
  process.exit(0);
}

const engine = (args.engine || 'tlc').toLowerCase();
const repoRoot = process.cwd();
const file = args.file || path.join('spec','tla','DomainSpec.tla');
const absFile = path.resolve(repoRoot, file);

const outDir = path.join(repoRoot, 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'tla-summary.json');
fs.mkdirSync(outDir, { recursive: true });

let ran = false;
let status;
let output = '';

if (!fs.existsSync(absFile)){
  status = 'file_not_found';
  output = `TLA file not found: ${absFile}`;
} else if (engine === 'apalache'){
  if (!commandExists('apalache-mc')) {
    status = 'tool_not_available';
    output = 'Apalache not found. See docs/quality/formal-tools-setup.md';
  } else {
    const baseCmd = { cmd: 'apalache-mc', args: ['check', '--inv=Invariant', absFile] };
    const runSpec = (timeoutSec && haveTimeout)
      ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
      : baseCmd;
    const result = runCommand(runSpec.cmd, runSpec.args);
    if (!result.available) {
      status = 'tool_not_available';
      output = 'Apalache not found. See docs/quality/formal-tools-setup.md';
    } else {
      output = result.output;
      ran = true;
      status = 'ran';
    }
  }
} else {
  // TLC via TLA_TOOLS_JAR
  if (process.env.TLA_TOOLS_JAR){
    const jarPath = path.resolve(process.env.TLA_TOOLS_JAR);
    if (!fs.existsSync(jarPath)) {
      status = 'jar_not_found';
      output = `TLA tools jar not found: ${jarPath}`;
    } else {
      if (!commandExists('java')) {
        status = 'tool_not_available';
        output = 'TLC not available (java not found). See docs/quality/formal-tools-setup.md';
      } else {
        const baseCmd = { cmd: 'java', args: ['-cp', jarPath, 'tlc2.TLC', absFile] };
        const runSpec = (timeoutSec && haveTimeout)
          ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
          : baseCmd;
        const result = runCommand(runSpec.cmd, runSpec.args);
        if (!result.available) {
          status = 'tool_not_available';
          output = 'TLC not available (java not found). See docs/quality/formal-tools-setup.md';
        } else {
          output = result.output;
          ran = true;
          status = 'ran';
        }
      }
    }
  } else {
    status = 'tool_not_available';
    output = 'TLC not available (TLA_TOOLS_JAR not set). See docs/quality/formal-tools-setup.md';
  }
}

const summary = {
  engine,
  file: path.relative(repoRoot, absFile),
  ran,
  status,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000)
};
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`TLA summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- engine=${engine} file=${summary.file} status=${status}`);

// Non-blocking
process.exit(0);
