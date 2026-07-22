#!/usr/bin/env node
// Lightweight TLA runner: accepts --engine and --file, tries to run Apalache or TLC if available; writes a summary. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { resolveRepoRelativeFileInput, validateChoice, TLA_ENGINES } from './input-policy.mjs';
import {
  buildFormalRunnerOutput,
  buildLegacyFormalExecutionEvidence,
  extractToolVersion,
  sha256FileSync,
} from './execution-evidence.mjs';

function parseArgs(argv){
  const args = { _: [] };
  for (let i=2;i<argv.length;i++){
    const a=argv[i];
    if (a==='-h'||a==='--help') args.help=true;
    else if (a.startsWith('--engine=')) { args.engine=a.slice(9); }
    else if ((a==='--engine' || a==='-e') && argv[i+1]) { args.engine=argv[++i]; }
    else if (a.startsWith('--file=')) { args.file=a.slice(7); }
    else if (a==='--file' && argv[i+1]) { args.file=argv[++i]; }
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

const args = parseArgs(process.argv);
const timeoutSec = args.timeout ? Math.max(1, Math.floor(Number(args.timeout)/1000)) : 0;
const haveTimeout = commandExists('timeout');
if (args.help){
  console.log(`Usage: node scripts/formal/verify-tla.mjs [--engine=tlc|apalache] [--file spec/tla/DomainSpec.tla] [--timeout <ms>]`);
  console.log('See docs/quality/formal-tools-setup.md for TLC/Apalache setup.');
  process.exit(0);
}

const repoRoot = process.cwd();

const outDir = path.join(repoRoot, 'artifacts/hermetic-reports', 'formal');
const outFile = path.join(outDir, 'tla-summary.json');
const outLog = path.join(outDir, 'tla-output.txt');
fs.mkdirSync(outDir, { recursive: true });

let ran = false;
let status;
let output = '';
let exitCode = null;
let ok = null;
let timeMs = null;
let engine = 'tlc';
let file = path.join('spec','tla','DomainSpec.tla');
let absFile = path.resolve(repoRoot, file);
let toolVersion = '';
let versionSource = 'unavailable';
let artifactSha256 = null;
let expectedArtifactSha256 = null;

try {
  engine = validateChoice((args.engine || 'tlc').toLowerCase(), {
    allowed: TLA_ENGINES,
    name: 'TLA engine',
    defaultValue: 'tlc',
  });
  const resolvedFile = resolveRepoRelativeFileInput(args.file, {
    repoRoot,
    defaultPath: path.join('spec','tla','DomainSpec.tla'),
    allowedRoots: ['spec/tla'],
    allowedExtensions: ['.tla'],
    name: 'TLA file',
  });
  file = resolvedFile.relativePath;
  absFile = resolvedFile.absolutePath;
} catch (error) {
  status = 'invalid_input';
  output = error?.message ?? String(error);
}

if (status === 'invalid_input') {
  ok = false;
} else if (!fs.existsSync(absFile)){
  status = 'file_not_found';
  output = `TLA file not found: ${absFile}`;
} else if (engine === 'apalache'){
  if (!commandExists('apalache-mc')) {
    status = 'tool_not_available';
    output = 'Apalache not found. See docs/quality/formal-tools-setup.md';
  } else {
    const versionResult = runCommand('apalache-mc', ['version']);
    toolVersion = extractToolVersion(versionResult.output);
    versionSource = toolVersion ? 'cli' : 'unavailable';
    const baseCmd = { cmd: 'apalache-mc', args: ['check', '--inv=Invariant', absFile] };
    const runSpec = (timeoutSec && haveTimeout)
      ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
      : baseCmd;
    const t0 = Date.now();
    const result = runCommand(runSpec.cmd, runSpec.args);
    timeMs = Date.now() - t0;
    if (!result.available) {
      status = 'tool_not_available';
      output = 'Apalache not found. See docs/quality/formal-tools-setup.md';
    } else {
      output = result.output;
      ran = true;
      exitCode = result.status;
      if (timeoutSec && haveTimeout && result.status === 124) {
        status = 'timeout';
        ok = null;
      } else {
        status = result.success ? 'ran' : 'failed';
        ok = result.success;
      }
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
      artifactSha256 = sha256FileSync(jarPath);
      expectedArtifactSha256 = process.env.TLA_TOOLS_SHA256 || null;
      const versionResult = runCommand('java', ['-cp', jarPath, 'tlc2.TLC', '-version']);
      toolVersion = extractToolVersion(versionResult.output) || process.env.TLA_TOOLS_VERSION || '';
      versionSource = extractToolVersion(versionResult.output)
        ? 'cli'
        : (process.env.TLA_TOOLS_VERSION ? 'reviewed-pin' : 'unavailable');
      if (!commandExists('java')) {
        status = 'tool_not_available';
        output = 'TLC not available (java not found). See docs/quality/formal-tools-setup.md';
      } else {
        const baseCmd = { cmd: 'java', args: ['-cp', jarPath, 'tlc2.TLC', absFile] };
        const runSpec = (timeoutSec && haveTimeout)
          ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
          : baseCmd;
        const t0 = Date.now();
        const result = runCommand(runSpec.cmd, runSpec.args);
        timeMs = Date.now() - t0;
        if (!result.available) {
          status = 'tool_not_available';
          output = 'TLC not available (java not found). See docs/quality/formal-tools-setup.md';
        } else {
          output = result.output;
          ran = true;
          exitCode = result.status;
          if (timeoutSec && haveTimeout && result.status === 124) {
            status = 'timeout';
            ok = null;
          } else {
            status = result.success ? 'ran' : 'failed';
            ok = result.success;
          }
        }
      }
    }
  } else {
    status = 'tool_not_available';
    output = 'TLC not available (TLA_TOOLS_JAR not set). See docs/quality/formal-tools-setup.md';
  }
}

try { fs.writeFileSync(outLog, output, 'utf-8'); } catch {}

const relativeInput = path.relative(repoRoot, absFile);
const relativeLog = path.relative(repoRoot, outLog);
const executionEvidence = buildLegacyFormalExecutionEvidence({
  runner: 'tla',
  toolName: engine === 'apalache' ? 'Apalache' : 'TLC',
  toolVersion,
  versionSource,
  artifactSha256,
  expectedArtifactSha256,
  inputPaths: [relativeInput],
  status,
  ok,
  ran,
  exitCode,
  logPath: relativeLog,
  scope: `${engine === 'apalache' ? 'Apalache' : 'TLC'} verification of ${relativeInput}`,
  assumptions: [
    'The result applies only to the supplied TLA+ module and runner configuration.',
    'The result does not establish correctness of implementation code outside the model.',
  ],
});

const summary = {
  engine,
  file: path.relative(repoRoot, absFile),
  ran,
  status,
  ok,
  exitCode,
  timeMs,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000),
  outputFile: relativeLog,
  runnerResult: buildFormalRunnerOutput({ runner: 'tla', executionEvidence }),
};
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`TLA summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- engine=${engine} file=${summary.file} status=${status}`);

// Non-blocking
process.exit(0);
