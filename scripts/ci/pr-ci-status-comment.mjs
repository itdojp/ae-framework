import { execFileSync } from 'node:child_process';

const repo = process.env.GITHUB_REPOSITORY;
if (!repo) {
  console.error('[pr-ci-status] GITHUB_REPOSITORY is required.');
  process.exit(1);
}
if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) {
  console.error('[pr-ci-status] GITHUB_REPOSITORY format is invalid.');
  process.exit(1);
}

const marker = '<!-- AE-CI-STATUS v1 -->';
const FAILED_LIST_LIMIT = 5;
const PR_LIMIT = 50;
const PR_SLEEP_MS = 150;

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

const execJson = (args, input) => {
  try {
    const output = execFileSync('gh', args, {
      encoding: 'utf8',
      stdio: ['pipe', 'pipe', 'pipe'],
      input,
    });
    return JSON.parse(output);
  } catch (error) {
    console.error('[pr-ci-status] gh failed:', error && error.message ? error.message : error);
    throw error;
  }
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

  return { counts, failed: failed.slice(0, FAILED_LIST_LIMIT) };
};

const listOpenPrs = () =>
  execJson(['pr', 'list', '--state', 'open', '--limit', String(PR_LIMIT), '--json', 'number,title,updatedAt']);

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
  const comments = execJson(['api', `repos/${repo}/issues/${number}/comments`]);
  const existing = comments.find((comment) => comment.body && comment.body.startsWith(marker));
  const payload = JSON.stringify({ body });
  if (existing) {
    execFileSync(
      'gh',
      ['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'],
      { stdio: ['pipe', 'inherit', 'inherit'], input: payload }
    );
    return;
  }
  execFileSync('gh', ['api', `repos/${repo}/issues/${number}/comments`, '--input', '-'], {
    stdio: ['pipe', 'inherit', 'inherit'],
    input: payload,
  });
};

const main = async () => {
  const prs = listOpenPrs();
  for (const pr of prs) {
    try {
      const view = execJson([
        'pr',
        'view',
        String(pr.number),
        '--json',
        'number,title,mergeable,reviewDecision,statusCheckRollup',
      ]);
      const body = buildBody(pr, view);
      upsertComment(pr.number, body);
    } catch (error) {
      console.error(`[pr-ci-status] Failed to process PR #${pr.number}:`, error);
    }
    await sleep(PR_SLEEP_MS);
  }
};

await main();
