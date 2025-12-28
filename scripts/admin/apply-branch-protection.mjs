#!/usr/bin/env node
/**
 * Apply branch protection from a preset JSON file.
 * Usage:
 *   ADMIN_TOKEN=ghp_xxx REPO=itdojp/ae-framework BRANCH=main node scripts/admin/apply-branch-protection.mjs .github/branch-protection.main.relax2.json
 */
import fs from 'node:fs/promises';
import path from 'node:path';

const token = process.env.ADMIN_TOKEN || process.env.GITHUB_TOKEN;
const repo = process.env.REPO || process.env.GITHUB_REPOSITORY;
const branch = process.env.BRANCH || 'main';
const presetPath = process.argv[2];

if (!token) {
  console.error('ERROR: ADMIN_TOKEN (or GITHUB_TOKEN) is required (must have repo admin scope).');
  process.exit(1);
}
if (!repo) {
  console.error('ERROR: REPO is required (e.g., itdojp/ae-framework).');
  process.exit(1);
}
if (!presetPath) {
  console.error('ERROR: preset JSON path is required.');
  process.exit(1);
}

async function main() {
  const api = `https://api.github.com/repos/${repo}/branches/${branch}/protection`;
  const file = path.resolve(process.cwd(), presetPath);
  const body = await fs.readFile(file, 'utf8');

  const res = await fetch(api, { // lgtm[js/file-access-to-http] Applying branch protection is an explicit admin CLI action.
    method: 'PUT',
    headers: {
      'Authorization': `token ${token}`,
      'Accept': 'application/vnd.github.luke-cage-preview+json',
      'Content-Type': 'application/json'
    },
    body
  });

  if (!res.ok) {
    const text = await res.text();
    console.error(`Failed to apply branch protection: ${res.status} ${res.statusText}\n${text}`);
    process.exit(1);
  }

  const json = await res.json();
  console.log('Applied. required_pull_request_reviews:', json.required_pull_request_reviews);
  console.log('Applied. required_status_checks:', json.required_status_checks);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
