#!/usr/bin/env node
import { execSync } from 'node:child_process';

const TARGETS = [
  'tests/api/generated',
  'artifacts/codex',
  'artifacts/spec'
];

function run(command) {
  try {
    return execSync(command, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim();
  } catch {
    return '';
  }
}

function statusFor(target) {
  const nameStatus = run(`git diff --name-status -- ${target}`);
  if (!nameStatus) {
    return { path: target, hasChanges: false, files: [], diffstat: '' };
  }
  const files = nameStatus.split('\n').map(line => {
    const [status, ...rest] = line.split('\t');
    return { status, file: rest.join('\t') };
  });
  const diffstat = run(`git diff --stat -- ${target}`);
  return { path: target, hasChanges: true, files, diffstat };
}

const summary = {
  generatedAt: new Date().toISOString(),
  targets: TARGETS.map(statusFor)
};

process.stdout.write(JSON.stringify(summary, null, 2));
