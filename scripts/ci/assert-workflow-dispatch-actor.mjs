#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

export function parseAllowedPermissions(value = 'admin,maintain,write') {
  return new Set(
    String(value)
      .split(',')
      .map((item) => item.trim().toLowerCase())
      .filter(Boolean),
  );
}

export function isTrustedPermission(permission, allowed = parseAllowedPermissions()) {
  return allowed.has(String(permission || '').trim().toLowerCase());
}

export function parsePermissionResponse(stdout) {
  const text = String(stdout || '').trim();
  if (!text) return '';
  try {
    const parsed = JSON.parse(text);
    return String(parsed?.permission || '').trim().toLowerCase();
  } catch {
    return text.split(/\r?\n/)[0].trim().toLowerCase();
  }
}

export function isDirectInvocation(moduleUrl = import.meta.url, argv = process.argv) {
  const scriptPath = argv?.[1] || '';
  if (!scriptPath) return false;
  return pathToFileURL(path.resolve(scriptPath)).href === moduleUrl;
}

export function main(env = process.env) {
  const actor = env.GITHUB_ACTOR || env.GITHUB_TRIGGERING_ACTOR || '';
  const repo = env.GITHUB_REPOSITORY || '';
  const token = env.GH_TOKEN || env.GITHUB_TOKEN || '';
  const allowed = parseAllowedPermissions(env.TRUSTED_WORKFLOW_DISPATCH_PERMISSIONS || 'admin,maintain,write');

  if (!actor) {
    throw new Error('GITHUB_ACTOR is required to authorize workflow_dispatch');
  }
  if (!repo) {
    throw new Error('GITHUB_REPOSITORY is required to authorize workflow_dispatch');
  }
  if (!token) {
    throw new Error('GH_TOKEN or GITHUB_TOKEN is required to authorize workflow_dispatch');
  }

  const result = spawnSync(
    'gh',
    ['api', `repos/${repo}/collaborators/${actor}/permission`, '--jq', '.permission'],
    {
      encoding: 'utf8',
      env: {
        ...env,
        GH_TOKEN: token,
      },
    },
  );
  if (result.error) {
    throw new Error(`failed to query collaborator permission: ${result.error.message}`);
  }
  if (result.status !== 0) {
    const diagnostic = `${result.stdout || ''}${result.stderr || ''}`.trim();
    throw new Error(`failed to query collaborator permission for ${actor}: ${diagnostic || `exit ${result.status}`}`);
  }

  const permission = parsePermissionResponse(result.stdout);
  if (!isTrustedPermission(permission, allowed)) {
    throw new Error(`workflow_dispatch actor ${actor} has permission '${permission || 'unknown'}'; required one of: ${[...allowed].join(', ')}`);
  }

  console.log(`workflow_dispatch actor ${actor} authorized with permission '${permission}'`);
  return 0;
}

if (isDirectInvocation(import.meta.url, process.argv)) {
  try {
    process.exit(main());
  } catch (error) {
    console.error(error?.message ?? String(error));
    process.exit(1);
  }
}
