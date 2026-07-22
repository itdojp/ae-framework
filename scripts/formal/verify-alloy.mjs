#!/usr/bin/env node
// Lightweight Alloy runner: accepts --file and tries to run Alloy if available; otherwise prints guidance. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { resolveRepoRelativeFileInput } from './input-policy.mjs';
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
    else if (a==='--file' && argv[i+1]) { args.file=argv[++i]; }
    else if (a.startsWith('--file=')) { args.file=a.slice(7); }
    else if (a==='--jar' && argv[i+1]) { args.jar=argv[++i]; }
    else if (a.startsWith('--jar=')) { args.jar=a.slice(6); }
    else { args._.push(a); }
  }
  return args;
}

function runCommand(cmd, cmdArgs){
  const result = spawnSync(cmd, cmdArgs, { encoding: 'utf8' });
  if (result.error) {
    if (result.error.code === 'ENOENT') {
      return { available: false, success: false, status: null, output: '' };
    }
    return { available: true, success: false, status: result.status ?? null, output: result.error.message ?? '' };
  }
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  return { available: true, success: result.status === 0, status: result.status ?? null, output: `${stdout}${stderr}` };
}

function expandHome(inputPath){
  if (!inputPath || inputPath[0] !== '~') return inputPath;
  if (inputPath === '~') return os.homedir();
  if (inputPath.startsWith('~/') || inputPath.startsWith('~\\')) {
    return path.join(os.homedir(), inputPath.slice(2));
  }
  return inputPath;
}

const args = parseArgs(process.argv);
if (args.help){
  console.log(`Usage: node scripts/formal/verify-alloy.mjs [--file spec/alloy/Domain.als] [--jar /path/to/alloy.jar]`);
  process.exit(0);
}

const repoRoot = path.resolve(process.cwd());
const outDir = path.join(repoRoot, 'artifacts/hermetic-reports', 'formal');
const outFile = path.join(outDir, 'alloy-summary.json');
const outLog = path.join(outDir, 'alloy-output.txt');
fs.mkdirSync(outDir, { recursive: true });

let ran = false;
let status;
let output = '';
let temporal = { present: false, operators: [], pastOperators: [] };
let exitCode = null;
let ok = null;
let timeMs = null;
let file = path.join('spec','alloy','Domain.als');
let absFile = path.resolve(repoRoot, file);
let toolVersion = '';
let versionSource = 'unavailable';
let artifactSha256 = null;
let expectedArtifactSha256 = null;

try {
  const resolvedFile = resolveRepoRelativeFileInput(args.file, {
    repoRoot,
    defaultPath: path.join('spec','alloy','Domain.als'),
    allowedRoots: ['spec/alloy'],
    allowedExtensions: ['.als'],
    name: 'Alloy file',
  });
  file = resolvedFile.relativePath;
  absFile = resolvedFile.absolutePath;
} catch (error) {
  status = 'invalid_input';
  output = error?.message ?? String(error);
  ok = false;
}

if (status === 'invalid_input') {
  // fail closed before invoking external formal tools
} else if (!fs.existsSync(absFile)){
  status = 'file_not_found';
  output = `Alloy file not found: ${absFile}`;
} else {
  const runCmd = process.env.ALLOY_RUN_CMD;
  if (runCmd) {
    status = 'run_cmd_unsupported';
    output = 'ALLOY_RUN_CMD shell execution is disabled. Use ALLOY_JAR or the Alloy CLI so the runner can invoke java/alloy with argv-safe arguments.';
  } else {
    const t0 = Date.now();
    const alloyResult = runCommand('alloy', [absFile]);
    if (alloyResult.available) {
      const versionResult = runCommand('alloy', ['--version']);
      toolVersion = extractToolVersion(versionResult.output);
      versionSource = toolVersion ? 'cli' : 'unavailable';
      timeMs = Date.now() - t0;
      output = alloyResult.output;
      ran = true;
      exitCode = alloyResult.status;
      status = alloyResult.success ? 'ran' : 'failed';
      ok = status === 'ran';
    } else if (process.env.ALLOY_JAR || args.jar){
      const jar = args.jar || process.env.ALLOY_JAR;
      const jarPath = path.resolve(expandHome(jar));
      if (!fs.existsSync(jarPath)) {
        status = 'jar_not_found';
        output = `Alloy jar not found: ${jarPath}. Set ALLOY_JAR to a valid path, use --jar /path/to/alloy.jar, or check that the file exists.`;
      } else {
        artifactSha256 = sha256FileSync(jarPath);
        expectedArtifactSha256 = process.env.ALLOY_ARTIFACT_SHA256 || null;
        const versionResult = runCommand('java', ['-jar', jarPath, 'version']);
        const cliVersion = extractToolVersion(versionResult.output);
        toolVersion = cliVersion || process.env.ALLOY_VERSION || '';
        versionSource = cliVersion
          ? 'cli'
          : (process.env.ALLOY_VERSION ? 'reviewed-pin' : 'unavailable');
        const t1 = Date.now();
        const javaResult = runCommand('java', ['-jar', jarPath, 'exec', '-q', '-o', '-', '-f', absFile]);
        if (!javaResult.available) {
          status = 'java_not_available';
          output = 'Java runtime not found. Ensure `java` is installed and on PATH to run the Alloy jar.';
        } else {
          timeMs = Date.now() - t1;
          output = javaResult.output;
          ran = true;
          exitCode = javaResult.status;
          status = javaResult.success ? 'ran' : 'failed';
          ok = status === 'ran';
        }
      }
    } else {
      status = 'tool_not_available';
      output = 'Alloy CLI not found. Set ALLOY_JAR=/path/to/alloy.jar or install Alloy CLI. See docs/quality/formal-tools-setup.md';
    }
  }
}

// Best-effort presence detection of temporal operators (Alloy 6 LTL / past operators)
try {
  const src = fs.readFileSync(absFile, 'utf8');
  const ops = [
    'always', 'eventually', 'historically', 'once', 'since', 'until', 'releases', 'triggered', 'next', 'before'
  ];
  const pastOps = ['historically', 'once', 'since', 'before'];
  const found = new Set();
  const foundPast = new Set();
  for (const op of ops) {
    const re = new RegExp(`\\b${op}\\b`, 'i');
    if (re.test(src)) found.add(op);
  }
  for (const op of pastOps) {
    const re = new RegExp(`\\b${op}\\b`, 'i');
    if (re.test(src)) foundPast.add(op);
  }
  temporal.present = found.size > 0;
  temporal.operators = Array.from(found);
  temporal.pastOperators = Array.from(foundPast);
} catch {}

try { fs.writeFileSync(outLog, output, 'utf-8'); } catch {}

const relativeInput = path.relative(repoRoot, absFile);
const relativeLog = path.relative(repoRoot, outLog);
const executionEvidence = buildLegacyFormalExecutionEvidence({
  runner: 'alloy',
  toolName: 'Alloy',
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
  scope: `Alloy commands and assertions declared by ${relativeInput}`,
  assumptions: [
    'The result applies only to the bounds and commands declared by the supplied Alloy model.',
    'The result does not establish correctness of implementation code outside the model.',
  ],
});

const summary = {
  file: relativeInput,
  ran,
  status,
  ok,
  exitCode,
  timeMs,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000),
  outputFile: relativeLog,
  temporal,
  runnerResult: buildFormalRunnerOutput({ runner: 'alloy', executionEvidence }),
};
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`Alloy summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- file=${summary.file} status=${status}`);

// Non-blocking
process.exit(0);
