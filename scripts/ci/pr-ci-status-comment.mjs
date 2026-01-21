import { execSync } from 'node:child_process';

const repo = process.env.GITHUB_REPOSITORY;
if (!repo) {
  console.error('[pr-ci-status] GITHUB_REPOSITORY is required.');
  process.exit(1);
}

const marker = '<!-- AE-CI-STATUS -->';

const execJson = (command) => {
  const output = execSync(command, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  return JSON.parse(output);
};

const summarizeChecks = (rollup = []) => {
  const counts = { success: 0, failure: 0, pending: 0, skipped: 0, neutral: 0 };
  const failed = [];

  for (const item of rollup) {
    if (item.__typename === 'CheckRun') {
      if (item.status !== 'COMPLETED') {
        counts.pending += 1;
        continue;
      }
      switch (item.conclusion) {
        case 'SUCCESS':
          counts.success += 1;
          break;
        case 'FAILURE':
        case 'CANCELLED':
        case 'TIMED_OUT':
        case 'ACTION_REQUIRED':
        case 'STALE':
          counts.failure += 1;
          failed.push(item.name);
          break;
        case 'SKIPPED':
          counts.skipped += 1;
          break;
        default:
          counts.neutral += 1;
          break;
      }
    } else if (item.__typename === 'StatusContext') {
      switch (item.state) {
        case 'SUCCESS':
          counts.success += 1;
          break;
        case 'FAILURE':
        case 'ERROR':
          counts.failure += 1;
          failed.push(item.context);
          break;
        case 'PENDING':
          counts.pending += 1;
          break;
        default:
          counts.neutral += 1;
          break;
      }
    }
  }

  return { counts, failed: failed.slice(0, 5) };
};

const listOpenPrs = () =>
  execJson('gh pr list --state open --json number,title,updatedAt');

const buildBody = (pr, view) => {
  const rollup = view.statusCheckRollup || [];
  const { counts, failed } = summarizeChecks(rollup);
  const summaryLine = [
    `- #${pr.number} ${pr.title}`,
    `✅${counts.success} ❌${counts.failure} ⏳${counts.pending} ⏭️${counts.skipped}`,
    `review:${view.reviewDecision || 'NONE'}`,
    `mergeable:${view.mergeable || 'UNKNOWN'}`,
  ].join(' | ');

  const lines = [marker, `## CI Status Snapshot (${new Date().toISOString()})`, summaryLine];
  if (failed.length > 0) {
    lines.push(`  - failed: ${failed.join(', ')}`);
  }
  return `${lines.join('\n')}\n`;
};

const upsertComment = (number, body) => {
  const comments = execJson(`gh api repos/${repo}/issues/${number}/comments`);
  const existing = comments.find((comment) => comment.body && comment.body.includes(marker));
  if (existing) {
    execSync(
      `gh api --method PATCH repos/${repo}/issues/comments/${existing.id} -f body=${JSON.stringify(body)}`,
      { stdio: 'inherit' }
    );
    return;
  }
  execSync(`gh api repos/${repo}/issues/${number}/comments -f body=${JSON.stringify(body)}`, {
    stdio: 'inherit',
  });
};

const prs = listOpenPrs();
for (const pr of prs) {
  const view = execJson(
    `gh pr view ${pr.number} --json number,title,mergeable,reviewDecision,statusCheckRollup`
  );
  const body = buildBody(pr, view);
  upsertComment(pr.number, body);
}
