#!/usr/bin/env node

import { existsSync, readFileSync } from 'node:fs';

function parseArgs(argv) {
  const args = {
    summary: 'reports/mutation/mutation-summary.json',
    label: 'mutation:survivors',
    labelColor: 'b60205',
    dryRun: false,
    repo: process.env.GITHUB_REPOSITORY,
    token: process.env.GITHUB_TOKEN,
    branch: process.env.GITHUB_REF_NAME || process.env.GITHUB_HEAD_REF,
    commit: process.env.GITHUB_SHA,
    context: process.env.GITHUB_WORKFLOW || 'mutation-quick',
    apiBase: process.env.GITHUB_API_URL || 'https://api.github.com',
  };

  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    const next = argv[i + 1];
    switch (current) {
      case '--summary':
      case '-s':
        if (next) {
          args.summary = next;
          i += 1;
        }
        break;
      case '--label':
        if (next) {
          args.label = next;
          i += 1;
        }
        break;
      case '--label-color':
        if (next) {
          const color = next.replace('#', '').slice(0, 6);
          if (/^[0-9a-fA-F]{6}$/.test(color)) {
            args.labelColor = color.toLowerCase();
          } else {
            console.warn(`Warning: Invalid label color "${next}". Using default color "${args.labelColor}".`);
          }
          i += 1;
        }
        break;
      case '--repo':
        if (next) {
          args.repo = next;
          i += 1;
        }
        break;
      case '--token':
        if (next) {
          args.token = next;
          i += 1;
        }
        break;
      case '--branch':
        if (next) {
          args.branch = next;
          i += 1;
        }
        break;
      case '--commit':
        if (next) {
          args.commit = next;
          i += 1;
        }
        break;
      case '--context':
        if (next) {
          args.context = next;
          i += 1;
        }
        break;
      case '--api':
        if (next) {
          args.apiBase = next;
          i += 1;
        }
        break;
      case '--pr':
        if (next) {
          args.pullRequest = Number.parseInt(next, 10);
          i += 1;
        }
        break;
      case '--dry-run':
        args.dryRun = true;
        break;
      default:
        break;
    }
  }

  return args;
}

function readJsonFile(path) {
  try {
    const contents = readFileSync(path, 'utf8');
    return JSON.parse(contents);
  } catch (error) {
    throw new Error(`Failed to read JSON at ${path}: ${error instanceof Error ? error.message : String(error)}`);
  }
}

function buildIssueTitle(summary, survivors, context) {
  const branch = context.branch || 'unknown-ref';
  const survivorCount = survivors.length;
  const score = typeof summary.metrics?.mutationScore === 'number'
    ? summary.metrics.mutationScore.toFixed(2)
    : 'n/a';
  return `Mutation survivors detected (${survivorCount}) on ${branch} — score ${score}%`;
}

function buildIssueBody(summary, survivors, context) {
  const lines = [];
  const metrics = summary.metrics ?? {};
  const mutationScore = typeof metrics.mutationScore === 'number'
    ? metrics.mutationScore.toFixed(2)
    : 'n/a';

  lines.push('## Mutation survivors report');
  lines.push('');
  lines.push(`- Report: \`${summary.report}\``);
  lines.push(`- Generated: ${summary.generatedAt ?? 'unknown'}`);
  lines.push(`- Branch: ${context.branch ?? 'unknown'}`);
  if (context.commit) {
    lines.push(`- Commit: ${context.commit}`);
  }
  if (context.runUrl) {
    lines.push(`- Workflow run: ${context.runUrl}`);
  }
  lines.push('');
  lines.push(`### Metrics`);
  lines.push(`- Score: ${mutationScore}%`);
  lines.push(`- Killed: ${metrics.killed ?? 0}`);
  lines.push(`- Survived: ${metrics.survived ?? 0}`);
  lines.push(`- Timeout: ${metrics.timeout ?? 0}`);
  lines.push(`- No coverage: ${metrics.noCover ?? 0}`);
  lines.push(`- Errors: ${metrics.errors ?? 0}`);

  if (survivors.length > 0) {
    lines.push('');
    lines.push('### Surviving mutants');
    lines.push('| File | Line | Mutator |');
    lines.push('| --- | --- | --- |');
    for (const survivor of survivors) {
      const line = survivor.location?.start?.line ?? '—';
      const file = survivor.file ?? 'unknown';
      const mutator = survivor.mutator ?? 'unknown';
      lines.push(`| ${file} | ${line} | ${mutator} |`);
    }
  }

  lines.push('');
  lines.push('> This issue was generated automatically from the mutation quick pipeline.');

  return lines.join('\n');
}

function detectPullRequestFromEnv() {
  const ref = process.env.GITHUB_REF || '';
  const match = ref.match(/^refs\/pull\/(\d+)\//);
  if (match) {
    return Number.parseInt(match[1], 10);
  }

  const eventPath = process.env.GITHUB_EVENT_PATH;
  if (eventPath && existsSync(eventPath)) {
    try {
      const payload = JSON.parse(readFileSync(eventPath, 'utf8'));
      if (typeof payload?.pull_request?.number === 'number') {
        return payload.pull_request.number;
      }
      if (typeof payload?.issue?.number === 'number') {
        return payload.issue.number;
      }
    } catch (error) {
      // Ignore parse errors and proceed without PR context
    }
  }

  return undefined;
}

async function githubRequest(apiBase, token, method, path, body, dryRun) {
  if (dryRun) {
    console.log(`[dry-run] ${method} ${path}`);
    if (body) {
      console.log(JSON.stringify(body, null, 2));
    }
    return undefined;
  }

  const response = await fetch(`${apiBase}${path}`, {
    method,
    headers: {
      'Accept': 'application/vnd.github+json',
      'Authorization': `Bearer ${token}`,
      'User-Agent': 'ae-framework-mutation-survivors-script',
    },
    body: body ? JSON.stringify(body) : undefined,
  });

  if (response.status === 404) {
    return undefined;
  }

  if (!response.ok) {
    const text = await response.text();
    throw new Error(`GitHub API ${method} ${path} failed: ${response.status} ${response.statusText} — ${text}`);
  }

  if (response.status === 204) {
    return undefined;
  }

  return await response.json();
}

async function ensureLabel(apiBase, token, owner, repo, label, color, dryRun) {
  const encodedName = encodeURIComponent(label);
  const existing = await githubRequest(apiBase, token, 'GET', `/repos/${owner}/${repo}/labels/${encodedName}`, undefined, dryRun);
  if (existing) {
    return existing;
  }
  return await githubRequest(apiBase, token, 'POST', `/repos/${owner}/${repo}/labels`, {
    name: label,
    color,
    description: 'Marked automatically when mutation survivors are detected',
  }, dryRun);
}

async function listOpenIssues(apiBase, token, owner, repo, label, dryRun) {
  const query = `/repos/${owner}/${repo}/issues?labels=${encodeURIComponent(label)}&state=open&per_page=20`;
  const issues = await githubRequest(apiBase, token, 'GET', query, undefined, dryRun);
  return Array.isArray(issues) ? issues : [];
}

async function createOrUpdateIssue({
  apiBase,
  token,
  owner,
  repo,
  label,
  title,
  body,
  dryRun,
}) {
  const openIssues = await listOpenIssues(apiBase, token, owner, repo, label, dryRun);
  const target = openIssues[0];
  if (target) {
    let labels;
    if (Array.isArray(target.labels)) {
      const labelNames = target.labels.map((entry) => (typeof entry === 'object' ? entry.name : entry));
      const filteredLabelNames = labelNames.filter(Boolean);
      const allLabels = filteredLabelNames.concat(label);
      labels = Array.from(new Set(allLabels));
    } else {
      labels = [label];
    }
    await githubRequest(apiBase, token, 'PATCH', `/repos/${owner}/${repo}/issues/${target.number}`, {
      title,
      body,
      labels,
    }, dryRun);
    return target.number;
  }

  const issue = await githubRequest(apiBase, token, 'POST', `/repos/${owner}/${repo}/issues`, {
    title,
    body,
    labels: [label],
  }, dryRun);
  return issue?.number;
}

async function closeOpenIssues(apiBase, token, owner, repo, label, dryRun, context) {
  const openIssues = await listOpenIssues(apiBase, token, owner, repo, label, dryRun);
  for (const issue of openIssues) {
    const issueNumber = issue.number;
    if (!issueNumber) continue;
    if (!dryRun) {
      await githubRequest(apiBase, token, 'POST', `/repos/${owner}/${repo}/issues/${issueNumber}/comments`, {
        body: `No surviving mutants detected (${context.context} @ ${context.branch ?? 'unknown'}). Closing automatically.`,
      }, dryRun);
    }
    await githubRequest(apiBase, token, 'PATCH', `/repos/${owner}/${repo}/issues/${issueNumber}`, {
      state: 'closed',
    }, dryRun);
  }
}

async function addLabelToPullRequest(apiBase, token, owner, repo, label, prNumber, dryRun) {
  if (!prNumber) return;
  await githubRequest(apiBase, token, 'POST', `/repos/${owner}/${repo}/issues/${prNumber}/labels`, {
    labels: [label],
  }, dryRun);
}

async function removeLabelFromPullRequest(apiBase, token, owner, repo, label, prNumber, dryRun) {
  if (!prNumber) return;
  const encodedName = encodeURIComponent(label);
  try {
    await githubRequest(apiBase, token, 'DELETE', `/repos/${owner}/${repo}/issues/${prNumber}/labels/${encodedName}`, undefined, dryRun);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    if (!/404/.test(message)) {
      throw error;
    }
  }
}

async function main() {
  const args = parseArgs(process.argv);

  if (!existsSync(args.summary)) {
    console.log(`Mutation summary not found at ${args.summary}; skipping issue reflection.`);
    return;
  }

  const summary = readJsonFile(args.summary);
  const survivors = Array.isArray(summary.survivors) ? summary.survivors : [];

  const repoSlug = args.repo;
  if (!repoSlug || !repoSlug.includes('/')) {
    console.error('Repository context is missing (set via --repo or GITHUB_REPOSITORY).');
    process.exit(1);
  }
  const [owner, repo] = repoSlug.split('/');

  const token = args.token;
  if (!token) {
    console.log('GITHUB_TOKEN not provided; skipping mutation survivor automation.');
    return;
  }

  const context = {
    branch: args.branch,
    commit: args.commit,
    context: args.context,
    runId: process.env.GITHUB_RUN_ID,
    runUrl: process.env.GITHUB_SERVER_URL && process.env.GITHUB_RUN_ID && process.env.GITHUB_REPOSITORY
      ? `${process.env.GITHUB_SERVER_URL}/${process.env.GITHUB_REPOSITORY}/actions/runs/${process.env.GITHUB_RUN_ID}`
      : undefined,
  };

  const prNumber = args.pullRequest ?? detectPullRequestFromEnv();

  await ensureLabel(args.apiBase, token, owner, repo, args.label, args.labelColor, args.dryRun);

  if (survivors.length > 0) {
    const title = buildIssueTitle(summary, survivors, context);
    const body = buildIssueBody(summary, survivors, context);
    const issueNumber = await createOrUpdateIssue({
      apiBase: args.apiBase,
      token,
      owner,
      repo,
      label: args.label,
      title,
      body,
      dryRun: args.dryRun,
    });

    if (issueNumber) {
      console.log(`Mutation survivors reflected in issue #${issueNumber}.`);
    }

    await addLabelToPullRequest(args.apiBase, token, owner, repo, args.label, prNumber, args.dryRun);
  } else {
    console.log('No surviving mutants detected. Removing labels and closing open survivor issues.');
    await closeOpenIssues(args.apiBase, token, owner, repo, args.label, args.dryRun, context);
    await removeLabelFromPullRequest(args.apiBase, token, owner, repo, args.label, prNumber, args.dryRun);
  }
}

await main().catch((error) => {
  console.error('Failed to publish mutation survivor report:', error instanceof Error ? error.stack ?? error.message : String(error));
  process.exit(1);
});
