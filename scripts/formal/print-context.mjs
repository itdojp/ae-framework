#!/usr/bin/env node
// Print formal run context (branch/commit/time + tools presence/defaults). Non-blocking.
import { execSync } from 'node:child_process';

function tryCmd(cmd){ try { return execSync(cmd, {encoding:'utf8'}).trim(); } catch { return ''; } }
function has(cmd){ try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }

const branch = tryCmd("bash -lc 'git rev-parse --abbrev-ref HEAD'") || process.env.GITHUB_REF_NAME || 'unknown';
const commit = tryCmd("bash -lc 'git rev-parse --short HEAD'") || (process.env.GITHUB_SHA ? process.env.GITHUB_SHA.slice(0,7) : 'unknown');
const when = new Date().toISOString();

// Tool presence
const hasApalache = has('apalache-mc');
const hasZ3 = has('z3');
const hasCvc5 = has('cvc5');
const hasTlc = !!(process.env.TLA_TOOLS_JAR || '').trim();

// Defaults used by verify-lite flow
const defaultTla = 'tlc';
const defaultSmt = 'cvc5';

console.log(`Formal run context: branch=${branch} commit=${commit} time=${when}`);
console.log(`Tools: tlc=${hasTlc?'yes':'no'} apalache=${hasApalache?'yes':'no'} z3=${hasZ3?'yes':'no'} cvc5=${hasCvc5?'yes':'no'}`);
console.log(`Defaults: tla=${defaultTla} smt=${defaultSmt}`);
process.exit(0);
