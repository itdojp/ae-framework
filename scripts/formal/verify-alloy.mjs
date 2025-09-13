#!/usr/bin/env node
// Lightweight Alloy runner: accepts --file and tries to run Alloy if available; otherwise prints guidance. Non-blocking.
import { execSync } from 'node:child_process';
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

function has(cmd){ try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }
function sh(cmd){ try { return execSync(cmd, {encoding:'utf8'}); } catch(e){ return (e.stdout?.toString?.()||'') + (e.stderr?.toString?.()||''); } }

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
let status = 'skipped';
let output = '';

if (!fs.existsSync(absFile)){
  status = 'file_not_found';
} else if (has('alloy')) {
  output = sh(`bash -lc 'alloy ${absFile.replace(/'/g, "'\\''")} 2>&1 || true'`);
  ran = true; status = 'ran';
} else if (process.env.ALLOY_JAR || args.jar){
  const jar = args.jar || process.env.ALLOY_JAR;
  output = sh(`bash -lc 'java -jar ${jar} ${absFile.replace(/'/g, "'\\''")} 2>&1 || true'`);
  ran = true; status = 'ran';
} else {
  status = 'tool_not_available';
  output = 'Alloy CLI not found. Set ALLOY_JAR=/path/to/alloy.jar or install Alloy CLI.';
}

const summary = {
  file: path.relative(repoRoot, absFile),
  ran,
  status,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000)
};
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`Alloy summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- file=${summary.file} status=${status}`);

// Non-blocking
process.exit(0);
