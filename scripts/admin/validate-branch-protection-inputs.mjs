#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const allowedBranches = new Set(['main']);
const allowedPresets = new Set([
  'branch-protection.main.require-verify-lite-gate.json',
  'branch-protection.main.require-verify-lite.json',
  'branch-protection.main.verify-lite-noreview.json',
  'branch-protection.main.verify-lite-trace-noreview.json',
  'branch-protection.main.restore.json',
  'branch-protection.main.relax.json',
  'branch-protection.main.relax2.json',
]);
const emergencyPresets = new Set([
  'branch-protection.main.require-verify-lite.json',
  'branch-protection.main.verify-lite-noreview.json',
  'branch-protection.main.verify-lite-trace-noreview.json',
  'branch-protection.main.relax.json',
  'branch-protection.main.relax2.json',
]);

const emergencyApprovalValue = 'approved-break-glass';

function fail(message) {
  console.error(`ERROR: ${message}`);
  process.exit(1);
}

function readRequiredEnv(name) {
  const value = process.env[name];
  if (typeof value !== 'string' || value.trim() === '') {
    fail(`${name} is required.`);
  }
  return value.trim();
}

function appendGithubOutput(name, value) {
  const outputPath = process.env.GITHUB_OUTPUT;
  if (!outputPath) {
    return;
  }
  fs.appendFileSync(outputPath, `${name}=${value}\n`, 'utf8');
}

function validateRepository(value) {
  if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(value)) {
    fail('GITHUB_REPOSITORY must be an owner/name repository identifier.');
  }
  return value;
}

function validateBranch(value) {
  if (!allowedBranches.has(value)) {
    fail(`Branch is not allowlisted: ${value}`);
  }
  return value;
}

function validatePreset(value) {
  if (!allowedPresets.has(value)) {
    fail(`Preset is not allowlisted: ${value}`);
  }
  if (value.includes('/') || value.includes('\\') || value.includes('..')) {
    fail(`Preset must be a filename from the allowlist: ${value}`);
  }

  const presetPath = path.posix.normalize(`.github/${value}`);
  if (presetPath !== `.github/${value}` || !presetPath.startsWith('.github/')) {
    fail(`Preset path did not normalize under .github: ${value}`);
  }
  if (!fs.existsSync(presetPath) || !fs.statSync(presetPath).isFile()) {
    fail(`Preset file not found: ${presetPath}`);
  }

  try {
    JSON.parse(fs.readFileSync(presetPath, 'utf8'));
  } catch (error) {
    fail(`Preset is not valid JSON: ${presetPath}; ${error instanceof Error ? error.message : String(error)}`);
  }

  return { preset: value, presetPath, emergency: emergencyPresets.has(value) };
}

const repository = validateRepository(readRequiredEnv('GITHUB_REPOSITORY'));
const branch = validateBranch(readRequiredEnv('BRANCH_PROTECTION_BRANCH'));
const { preset, presetPath, emergency } = validatePreset(readRequiredEnv('BRANCH_PROTECTION_PRESET'));
const emergencyApproval = (process.env.BRANCH_PROTECTION_EMERGENCY_APPROVAL || '').trim();

if (emergency && emergencyApproval !== emergencyApprovalValue) {
  fail(`Preset ${preset} changes review or check gates and requires BRANCH_PROTECTION_EMERGENCY_APPROVAL=${emergencyApprovalValue}.`);
}

const apiPath = `repos/${repository}/branches/${branch}/protection`;

appendGithubOutput('branch', branch);
appendGithubOutput('preset', preset);
appendGithubOutput('preset_path', presetPath);
appendGithubOutput('api_path', apiPath);
appendGithubOutput('emergency', emergency ? 'true' : 'false');

console.log(`Validated branch-protection preset: ${preset}`);
console.log(`Validated branch-protection branch: ${branch}`);
console.log(`Emergency/break-glass preset: ${emergency ? 'yes' : 'no'}`);
