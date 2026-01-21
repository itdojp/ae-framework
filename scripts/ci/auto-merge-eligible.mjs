#!/usr/bin/env node
import { execFileSync } from 'node:child_process';

const repo = process.env.GITHUB_REPOSITORY;
const prNumber = process.env.PR_NUMBER;
const enable = process.env.ENABLE_AUTO_MERGE === 'true';

if (!repo) {
  console.error('[auto-merge] GITHUB_REPOSITORY is required.');
  process.exit(1);
}
if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) {
  console.error('[auto-merge] GITHUB_REPOSITORY format is invalid.');
  process.exit(1);
}
if (!prNumber) {
  console.error('[auto-merge] PR_NUMBER is required.');
  process.exit(1);
}

const execJson = (args) => {
  const output = execFileSync('gh', args, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  return JSON.parse(output);
};

const summarizeChecks = (rollup = []) => {
  const counts = { success: 0, failure: 0, pending: 0 };
  const failed = [];
  for (const item of rollup) {
    if (item.__typename === 'CheckRun') {
      if (item.status !== 'COMPLETED') {
        counts.pending += 1;
        continue;
      }
      if (item.conclusion === 'SUCCESS' || item.conclusion === 'SKIPPED') {
        counts.success += 1;
        continue;
      }
      counts.failure += 1;
      failed.push(item.name);
      continue;
    }
    if (item.__typename === 'StatusContext') {
      if (item.state === 'SUCCESS') {
        counts.success += 1;
        continue;
      }
      if (item.state === 'PENDING') {
        counts.pending += 1;
        continue;
      }
      counts.failure += 1;
      failed.push(item.context);
    }
  }
  return { counts, failed };
};

const pr = execJson([
  'pr',
  'view',
  String(prNumber),
  '--json',
  'number,title,mergeable,reviewDecision,statusCheckRollup',
]);

const { counts, failed } = summarizeChecks(pr.statusCheckRollup || []);
const eligible =
  pr.mergeable === 'MERGEABLE' &&
  pr.reviewDecision === 'APPROVED' &&
  counts.failure === 0 &&
  counts.pending === 0;

console.log(`[auto-merge] PR #${pr.number}: ${pr.title}`);
console.log(`[auto-merge] mergeable=${pr.mergeable} review=${pr.reviewDecision}`);
console.log(`[auto-merge] checks: success=${counts.success} failure=${counts.failure} pending=${counts.pending}`);
if (failed.length > 0) {
  console.log(`[auto-merge] failed: ${failed.slice(0, 10).join(', ')}`);
}

if (!eligible) {
  console.log('[auto-merge] Not eligible.');
  process.exit(0);
}

if (!enable) {
  console.log('[auto-merge] Eligible. Enable with ENABLE_AUTO_MERGE=true to activate.');
  process.exit(0);
}

execFileSync('gh', ['pr', 'merge', String(prNumber), '--auto', '--squash'], {
  stdio: 'inherit',
});
