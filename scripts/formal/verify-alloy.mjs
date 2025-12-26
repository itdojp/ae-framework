#!/usr/bin/env node
// Lightweight Alloy runner: accepts --file and tries to run Alloy if available; otherwise prints guidance. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

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
      return { available: false, output: '' };
    }
    return { available: true, output: result.error.message ?? '' };
  }
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  return { available: true, output: `${stdout}${stderr}` };
}

const args = parseArgs(process.argv);
if (args.help){
  console.log(`Usage: node scripts/formal/verify-alloy.mjs [--file spec/alloy/Domain.als] [--jar /path/to/alloy.jar]`);
  process.exit(0);
}

const repoRoot = path.resolve(process.cwd());
const file = args.file || path.join('spec','alloy','Domain.als');
const absFile = path.resolve(repoRoot, file);
const outDir = path.join(repoRoot, 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'alloy-summary.json');
fs.mkdirSync(outDir, { recursive: true });

let ran = false;
let status;
let output = '';
let temporal = { present: false, operators: [], pastOperators: [] };

if (!fs.existsSync(absFile)){
  status = 'file_not_found';
  output = `Alloy file not found: ${absFile}`;
} else {
  const alloyResult = runCommand('alloy', [absFile]);
  if (alloyResult.available) {
    output = alloyResult.output;
    ran = true;
    status = 'ran';
  } else if (process.env.ALLOY_JAR || args.jar){
    const jar = args.jar || process.env.ALLOY_JAR;
    const jarPath = path.resolve(jar);
    if (!fs.existsSync(jarPath)) {
      status = 'jar_not_found';
      output = `Alloy jar not found: ${jarPath}`;
    } else {
      const javaResult = runCommand('java', ['-jar', jarPath, absFile]);
      output = javaResult.output;
      ran = true;
      status = 'ran';
    }
  } else {
    status = 'tool_not_available';
    output = 'Alloy CLI not found. Set ALLOY_JAR=/path/to/alloy.jar or install Alloy CLI. See docs/quality/formal-tools-setup.md';
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

const summary = {
  file: path.relative(repoRoot, absFile),
  ran,
  status,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000),
  temporal
};
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`Alloy summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- file=${summary.file} status=${status}`);

// Non-blocking
process.exit(0);
