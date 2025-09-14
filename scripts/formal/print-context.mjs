#!/usr/bin/env node
// Print formal run context (branch/commit/time). Non-blocking.
import { execSync } from 'node:child_process';

function tryCmd(cmd){ try { return execSync(cmd, {encoding:'utf8'}).trim(); } catch { return ''; } }

const branch = tryCmd("bash -lc 'git rev-parse --abbrev-ref HEAD'") || process.env.GITHUB_REF_NAME || 'unknown';
const commit = tryCmd("bash -lc 'git rev-parse --short HEAD'") || (process.env.GITHUB_SHA ? process.env.GITHUB_SHA.slice(0,7) : 'unknown');
const when = new Date().toISOString();

console.log(`Formal run context: branch=${branch} commit=${commit} time=${when}`);
process.exit(0);

