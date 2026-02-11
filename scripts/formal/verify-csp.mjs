#!/usr/bin/env node
// Lightweight CSP runner:
// - If CSP_RUN_CMD is set, execute it via shell (supports {file} placeholder).
// - Else, if `cspx` exists, run typecheck or a basic assertion check (non-blocking summary).
// - Else, if FDR `refines` exists, run a typecheck (non-blocking summary).
// - Else, if `cspmchecker` exists, run a typecheck (non-blocking summary).
// - Else, report tool_not_available.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { normalizeArtifactPath } from '../ci/lib/path-normalization.mjs';

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--help' || a === '-h') args.help = true;
    else if (a === '--file' && next) { args.file = next; i += 1; }
    else if (a.startsWith('--file=')) { args.file = a.slice(7); }
    else if (a === '--mode' && next) { args.mode = next; i += 1; }
    else if (a.startsWith('--mode=')) { args.mode = a.slice(7); }
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

function runCommand(cmd, cmdArgs, options = {}) {
  const result = spawnSync(cmd, cmdArgs, { encoding: 'utf8', cwd: options.cwd });
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  const output = `${stdout}${stderr}`.trim();
  if (result.error) {
    if (result.error.code === 'ENOENT') {
      return { available: false, status: null, output: output || (result.error.message ?? '') };
    }
    return { available: true, status: result.status ?? null, output: output || (result.error.message ?? '') };
  }
  return { available: true, status: result.status ?? 0, output };
}

function clamp(s, n = 4000) {
  const t = String(s || '');
  return t.length > n ? `${t.slice(0, n)}…` : t;
}

function readJsonSafe(p) {
  try { return JSON.parse(fs.readFileSync(p, 'utf8')); } catch { return undefined; }
}

function mapCspxStatusToSummaryStatus(s) {
  const v = String(s || '').toLowerCase();
  if (v === 'pass') return 'ran';
  if (v === 'fail') return 'failed';
  if (v === 'unsupported') return 'unsupported';
  if (v === 'timeout') return 'timeout';
  if (v === 'out_of_memory') return 'out_of_memory';
  if (v === 'error') return 'error';
  return 'failed';
}

function summarizeCspxResult(result) {
  if (!result || typeof result !== 'object') return 'cspx: no result JSON produced';
  const status = result.status || 'n/a';
  const exitCode = result.exit_code ?? 'n/a';
  const schema = result.schema_version || 'n/a';
  const checks = Array.isArray(result.checks) ? result.checks : [];
  const checksLine = checks.length
    ? `checks=${checks.map((c) => `${c.name}:${c.status}`).join(',')}`
    : 'checks=n/a';
  const reason = checks.find((c) => c && c.reason)?.reason;
  const reasonLine = reason && reason.kind
    ? ` reason=${reason.kind}${reason.message ? `:${String(reason.message).slice(0, 120)}` : ''}`
    : '';
  return `cspx schema=${schema} status=${status} exit_code=${exitCode} ${checksLine}${reasonLine}`.trim();
}

const args = parseArgs(process.argv);
if (args.help) {
  console.log('Usage: node scripts/formal/verify-csp.mjs [--file spec/csp/sample.cspm]');
  console.log('Options:');
  console.log('  --mode typecheck|assertions  (default: typecheck; affects cspx/refines backends)');
  console.log('Backends (best-effort): CSP_RUN_CMD -> cspx -> refines -> cspmchecker');
  console.log('Optional: set CSP_RUN_CMD to execute a CSP tool (supports {file}).');
  process.exit(0);
}

const repoRoot = process.cwd();
const file = args.file || path.join('spec', 'csp', 'sample.cspm');
const absFile = path.resolve(repoRoot, file);
const outDir = path.join(repoRoot, 'artifacts', 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'csp-summary.json');
const cspxOutFile = path.join(outDir, 'cspx-result.json');
const outLog = path.join(outDir, 'csp-output.txt');
fs.mkdirSync(outDir, { recursive: true });

let ran = false;
let status;
let output = '';
let outputFull = '';
let exitCode = null;
let ok = null;
let timeMs = null;
let backend = null;
let detailsFile = null;
let resultStatus = null;
let forceWriteSummary = true;

if (!fs.existsSync(absFile)) {
  status = 'file_not_found';
  outputFull = `CSP file not found: ${absFile}`;
  output = clamp(outputFull);
} else {
  const runCmd = process.env.CSP_RUN_CMD;
  if (runCmd) {
    const cmd = runCmd.replace(/{file}/g, absFile);
    const t0 = Date.now();
    const res = runShell(cmd);
    timeMs = res.available ? (Date.now() - t0) : null;
    ran = res.available;
    exitCode = res.status;
    status = res.available ? (res.success ? 'ran' : 'failed') : 'tool_not_available';
    outputFull = res.output || 'CSP_RUN_CMD produced no output';
    output = clamp(outputFull);
    backend = 'CSP_RUN_CMD';
  } else if (commandExists('cspx')) {
    // cspx (OSS): CI-first CSPM checker with JSON output.
    const rawMode = args.mode || 'typecheck';
    let mode = rawMode.toLowerCase();
    if (args.mode && mode !== 'typecheck' && mode !== 'assertions') {
      console.error(
        `Unknown --mode value '${args.mode}'. Expected 'typecheck' or 'assertions'. Defaulting to 'typecheck'.`,
      );
      mode = 'typecheck';
    }

    // Keep the v0.1 integration intentionally narrow and reproducible.
    // - typecheck: cspx typecheck
    // - assertions: currently mapped to a single canonical assertion (deadlock freedom)
    const cspxArgs = (mode === 'assertions')
      ? ['check', '--assert', 'deadlock free', absFile, '--format', 'json', '--output', cspxOutFile, '--summary-json', outFile]
      : ['typecheck', absFile, '--format', 'json', '--output', cspxOutFile, '--summary-json', outFile];

    // Avoid stale reads: if cspx fails before writing a new JSON, a previous run's file must not be reused.
    try { fs.rmSync(cspxOutFile, { force: true }); } catch {}
    try { fs.rmSync(outFile, { force: true }); } catch {}

    const t0 = Date.now();
    const res = runCommand('cspx', cspxArgs);
    timeMs = res.available ? (Date.now() - t0) : null;
    ran = res.available;
    exitCode = res.status;
    backend = `cspx:${mode}`;
    detailsFile = normalizeArtifactPath(cspxOutFile, { repoRoot });

    const result = fs.existsSync(cspxOutFile) ? readJsonSafe(cspxOutFile) : undefined;
    const cspSummary = fs.existsSync(outFile) ? readJsonSafe(outFile) : undefined;
    const schemaVersion = result?.schema_version;
    if (!res.available) {
      status = 'tool_not_available';
      outputFull = res.output || 'cspx not available';
      output = clamp(outputFull);
    } else if (cspSummary && typeof cspSummary === 'object' && !result) {
      // Prefer cspx-generated summary when detail JSON is missing.
      status = cspSummary.status || (res.status === 0 ? 'ran' : 'failed');
      resultStatus = cspSummary.resultStatus || null;
      outputFull = [cspSummary.output, res.output].filter(Boolean).join('\n');
      output = clamp(outputFull);
      forceWriteSummary = false;
    } else if (!result) {
      status = res.status === 0 ? 'ran' : 'failed';
      outputFull = res.output || 'cspx produced no JSON result';
      output = clamp(outputFull);
    } else if (schemaVersion !== '0.1') {
      status = 'unsupported';
      outputFull = `cspx schema_version mismatch: expected 0.1, got ${schemaVersion || 'n/a'}`;
      output = clamp(outputFull);
    } else {
      if (cspSummary && typeof cspSummary === 'object') {
        status = cspSummary.status || mapCspxStatusToSummaryStatus(result.status);
        resultStatus = cspSummary.resultStatus || result.status || null;
        outputFull = [cspSummary.output, res.output].filter(Boolean).join('\n');
        output = clamp(outputFull);
        // cspx-generated summary already follows the contract path and schema.
        forceWriteSummary = false;
      } else {
        resultStatus = result.status || null;
        status = mapCspxStatusToSummaryStatus(result.status);
        outputFull = [summarizeCspxResult(result), res.output].filter(Boolean).join('\n');
        output = clamp(outputFull);
      }
    }
  } else if (commandExists('refines')) {
    // FDR (commercial): allow local runs when installed.
    const rawMode = args.mode || 'typecheck';
    let mode = rawMode.toLowerCase();
    if (args.mode && mode !== 'typecheck' && mode !== 'assertions') {
      console.error(
        `Unknown --mode value '${args.mode}'. Expected 'typecheck' or 'assertions'. Defaulting to 'typecheck'.`,
      );
      mode = 'typecheck';
    }
    const refinesArgs = (mode === 'assertions')
      // Run all assertions in the file (best-effort). Keep output small.
      ? ['--brief', '--quiet', '--format', 'plain', absFile]
      // Fast path: typecheck only (safe default).
      : ['--typecheck', '--format', 'plain', absFile];
    const t0 = Date.now();
    const res = runCommand('refines', refinesArgs);
    timeMs = res.available ? (Date.now() - t0) : null;
    ran = res.available;
    exitCode = res.status;
    status = res.available ? (res.status === 0 ? 'ran' : 'failed') : 'tool_not_available';
    outputFull = res.output || 'refines produced no output';
    output = clamp(outputFull);
    backend = `refines:${mode}`;
  } else if (commandExists('cspmchecker')) {
    // libcspm/cspmchecker (OSS): typecheck-only (no refinement).
    const t0 = Date.now();
    const res = runCommand('cspmchecker', [absFile]);
    timeMs = res.available ? (Date.now() - t0) : null;
    ran = res.available;
    exitCode = res.status;
    status = res.available ? (res.status === 0 ? 'ran' : 'failed') : 'tool_not_available';
    outputFull = res.output || 'cspmchecker produced no output';
    output = clamp(outputFull);
    backend = 'cspmchecker';
  } else {
    // Best-effort detection: actual execution depends on selected toolchain.
    const known = ['cspx', 'refines', 'cspmchecker', 'cspm', 'csp0', 'fdr4', 'fdr'];
    const found = known.filter((c) => commandExists(c));
    status = 'tool_not_available';
    outputFull = found.length
      ? `CSP tool detected (${found.join(', ')}), but runner supports only CSP_RUN_CMD/cspx/refines/cspmchecker. Configure CSP_RUN_CMD or install a supported backend.`
      : 'No CSP tool configured. Set CSP_RUN_CMD, install cspx, install FDR (refines), or install cspmchecker.';
    output = clamp(outputFull);
  }
}

if (ran) {
  ok = status === 'ran' ? true : (status === 'failed' ? false : null);
}

try { fs.writeFileSync(outLog, outputFull || output || '', 'utf-8'); } catch {}

if (forceWriteSummary) {
  const summary = {
    tool: 'csp',
    file: normalizeArtifactPath(absFile, { repoRoot }) ?? path.relative(repoRoot, absFile),
    backend,
    detailsFile,
    resultStatus,
    ran,
    status,
    ok,
    exitCode,
    timeMs,
    timestamp: new Date().toISOString(),
    output,
    outputFile: normalizeArtifactPath(outLog, { repoRoot }),
  };
  fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
} else {
  // Keep cspx-generated summary file and only refresh fields needed by this runner.
  const summary = readJsonSafe(outFile) || {};
  summary.file = normalizeArtifactPath(summary.file, { repoRoot }) ?? normalizeArtifactPath(absFile, { repoRoot }) ?? path.relative(repoRoot, absFile);
  summary.backend = summary.backend || backend;
  summary.detailsFile = normalizeArtifactPath(summary.detailsFile, { repoRoot }) ?? detailsFile;
  summary.resultStatus = summary.resultStatus || resultStatus;
  summary.status = summary.status || status;
  summary.ok = typeof summary.ok === 'boolean' ? summary.ok : ok;
  summary.exitCode = typeof summary.exitCode === 'number'
    ? summary.exitCode
    : (typeof exitCode === 'number' ? exitCode : null);
  summary.timeMs = typeof summary.timeMs === 'number' ? summary.timeMs : timeMs;
  summary.output = clamp(output || summary.output || '');
  summary.outputFile = typeof summary.outputFile === 'string' && summary.outputFile.trim()
    ? normalizeArtifactPath(summary.outputFile, { repoRoot })
    : normalizeArtifactPath(outLog, { repoRoot });
  fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
}
const finalSummary = readJsonSafe(outFile) || {};
console.log(`CSP summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- file=${finalSummary.file || path.relative(repoRoot, absFile)} status=${finalSummary.status || status}${(finalSummary.backend || backend) ? ` backend=${finalSummary.backend || backend}` : ''}`);
process.exit(0);
