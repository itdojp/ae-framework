#!/usr/bin/env node
// Lightweight Kani runner (stub/minimal):
// - Detects Kani presence (kani or cargo-kani)
// - Optionally runs `kani --version` and writes a summary JSON (non-blocking)
import { execSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function has(cmd){ try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }
function sh(cmd){ try { return execSync(cmd, {encoding:'utf8'}); } catch(e){ return (e.stdout?.toString?.()||'') + (e.stderr?.toString?.()||''); } }

const outDir = path.join(process.cwd(), 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'kani-summary.json');
fs.mkdirSync(outDir, { recursive: true });

const haveKani = has('kani') || has('cargo-kani');
const tool = has('kani') ? 'kani' : (has('cargo-kani') ? 'cargo-kani' : '');
let version = '';
if (tool) {
  version = sh(`bash -lc '${tool} --version 2>&1 || true'`).trim().split(/\n/)[0] || '';
}

const summary = {
  tool: 'kani',
  detected: haveKani,
  ran: false,
  status: haveKani ? 'detected' : 'tool_not_available',
  version: version || null,
  timestamp: new Date().toISOString()
};

fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`Kani summary written: ${path.relative(process.cwd(), outFile)}`);
console.log(`- detected=${haveKani} tool=${tool||'n/a'}`);
process.exit(0);

