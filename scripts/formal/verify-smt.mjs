#!/usr/bin/env node
// Lightweight SMT runner: executes a solver when available and records semantic result evidence. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { buildFormalRunnerOutput, buildLegacyFormalExecutionEvidence, extractToolVersion } from './execution-evidence.mjs';

const SMT_RESULTS = new Set(['sat', 'unsat', 'unknown']);
const SMT_EXPECTED_RESULTS = new Set(['sat', 'unsat']);

function normalizeExpectedResult(value) {
  const normalized = String(value ?? '').trim().toLowerCase();
  return SMT_EXPECTED_RESULTS.has(normalized) ? normalized : null;
}

/**
 * Parse solver stdout without consulting the process exit code.
 * Exactly one whitespace-delimited SMT result token is accepted. Multiple
 * result tokens are kept as an explicit malformed result rather than choosing
 * one of them.
 */
export function parseSmtSemanticResult({ stdout = '', expectedResult = null, timeout = false } = {}) {
  const expected = normalizeExpectedResult(expectedResult);
  const outputLines = String(stdout ?? '')
    .split(/\r?\n/u)
    .map((line) => line.trim())
    .filter(Boolean);
  const resultLines = outputLines.filter((line) => SMT_RESULTS.has(line));

  let parsed = false;
  let actualResult = null;
  if (resultLines.length === 1) {
    parsed = true;
    [actualResult] = resultLines;
  } else if (outputLines.length > 0) {
    actualResult = 'malformed';
  }

  const matchesExpected = expected === null
    ? null
    : parsed && actualResult !== 'unknown' && actualResult === expected;

  return {
    domain: 'smt',
    parsed,
    expectedResult: expected,
    actualResult,
    matchesExpected,
    timeout: timeout === true,
  };
}

export function isSmtSemanticSuccess(semanticResult) {
  return semanticResult?.domain === 'smt'
    && semanticResult.parsed === true
    && semanticResult.matchesExpected === true
    && semanticResult.timeout === false;
}

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--help' || a === '-h') args.help = true;
    else if (a === '--file' && next) { args.file = next; i += 1; }
    else if (a.startsWith('--file=')) { args.file = a.slice(7); }
    else if (a === '--solver' && next) { args.solver = next; i += 1; }
    else if (a.startsWith('--solver=')) { args.solver = a.slice(9); }
    else if (a === '--expected-result' && next) { args.expectedResult = next; i += 1; }
    else if (a.startsWith('--expected-result=')) { args.expectedResult = a.slice(18); }
    else if (a === '--timeout' && next) { args.timeout = Number(next); i += 1; }
    else if (a.startsWith('--timeout=')) { args.timeout = Number(a.slice(10)); }
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
      stdout,
      stderr,
      output,
      errorCode: result.error.code ?? null,
    };
  }
  return {
    available: true,
    status: result.status ?? null,
    stdout,
    stderr,
    output,
    errorCode: null,
  };
}

export function runSmtVerification(argv = process.argv) {
  const args = parseArgs(argv);
  const timeoutSec = args.timeout ? Math.max(1, Math.floor(Number(args.timeout) / 1000)) : 0;
  const haveTimeout = commandExists('timeout');
  const timeoutRequested = timeoutSec > 0;
  const timeoutIgnored = timeoutRequested && !haveTimeout;
  if (args.help) {
    console.log('Usage: node scripts/formal/verify-smt.mjs [--solver=z3|cvc5] [--file path/to/input.smt2] [--expected-result sat|unsat] [--timeout <ms>]');
    console.log('See docs/quality/formal-tools-setup.md for solver setup.');
    return null;
  }

  const solver = (args.solver || 'z3').toLowerCase();
  const file = args.file;
  const expectedResult = normalizeExpectedResult(args.expectedResult);
  const solverSpec = solver === 'z3'
    ? { cmd: 'z3', args: ['-smt2'] }
    : solver === 'cvc5'
      ? { cmd: 'cvc5', args: ['--lang=smt2'] }
      : null;

  const repoRoot = path.resolve(process.cwd());
  const outDir = path.join(repoRoot, 'artifacts/hermetic-reports', 'formal');
  const outFile = path.join(outDir, 'smt-summary.json');
  const outLog = path.join(outDir, 'smt-output.txt');
  fs.mkdirSync(outDir, { recursive: true });

  let status;
  let output = '';
  let ran = false;
  let exitCode = null;
  let ok = null;
  let timeMs = null;
  let toolVersion = '';
  let versionSource = 'unavailable';
  let semanticResult = parseSmtSemanticResult({ expectedResult });

  if (!file) {
    status = 'no_file';
  } else if (!fs.existsSync(file)) {
    status = 'file_not_found';
    output = `SMT-LIB file not found: ${file}`;
  } else if (solverSpec && commandExists(solverSpec.cmd)) {
    toolVersion = extractToolVersion(runCommand(solverSpec.cmd, ['--version']).output);
    versionSource = toolVersion ? 'cli' : 'unavailable';
    const baseCmd = { cmd: solverSpec.cmd, args: [...solverSpec.args, file] };
    const runSpec = (timeoutSec && haveTimeout)
      ? { cmd: 'timeout', args: [`${timeoutSec}s`, baseCmd.cmd, ...baseCmd.args] }
      : baseCmd;
    const t0 = Date.now();
    const result = runCommand(runSpec.cmd, runSpec.args);
    timeMs = Date.now() - t0;
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
      exitCode = result.status;
      const timedOut = timeoutSec > 0 && haveTimeout && result.status === 124;
      semanticResult = parseSmtSemanticResult({
        stdout: result.stdout,
        expectedResult,
        timeout: timedOut,
      });
      status = timedOut ? 'timeout' : (result.status === 0 ? 'ran' : 'failed');
      ok = status === 'ran' ? isSmtSemanticSuccess(semanticResult) : (status === 'failed' ? false : null);
      if (timeoutIgnored) {
        output = `Timeout requested (${timeoutSec}s) but 'timeout' is unavailable; running without timeout.\n${output}`;
      }
    }
  } else {
    status = 'solver_not_available';
    output = `Solver '${solver}' not found. See docs/quality/formal-tools-setup.md`;
  }

  try { fs.writeFileSync(outLog, output, 'utf-8'); } catch {}

  const relativeInput = file ? path.relative(repoRoot, path.resolve(repoRoot, file)) : 'SMT input not supplied';
  const relativeLog = path.relative(repoRoot, outLog);
  const executionEvidence = buildLegacyFormalExecutionEvidence({
    runner: 'smt',
    toolName: solver,
    toolVersion,
    versionSource,
    inputPaths: [relativeInput],
    status,
    ok,
    ran,
    exitCode,
    logPath: relativeLog,
    scope: `SMT solver evaluation of ${relativeInput}`,
    assumptions: [
      'The solver result applies only to the supplied SMT-LIB input and selected solver.',
    ],
    semanticResult,
  });

  const summary = {
    solver,
    file: file || null,
    ran,
    status,
    ok,
    exitCode,
    timeMs,
    timestamp: new Date().toISOString(),
    output: output.slice(0, 4000),
    outputFile: relativeLog,
    semanticResult,
    runnerResult: buildFormalRunnerOutput({ runner: 'smt', executionEvidence }),
  };

  fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
  console.log(`SMT summary written: ${path.relative(repoRoot, outFile)}`);
  console.log(`- solver=${solver} status=${status} expected=${semanticResult.expectedResult ?? 'missing'} actual=${semanticResult.actualResult ?? 'unparsed'}`);
  return summary;
}

const isDirectRun = process.argv[1]
  && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url);
if (isDirectRun) {
  runSmtVerification();
  // Deliberately non-blocking: consumers enforce the recorded evidence contract.
  process.exit(0);
}
