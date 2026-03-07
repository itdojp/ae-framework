#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { deriveGhPrBaseBranch } from './branch-inventory.mjs';

const DEFAULT_INPUT_JSON = 'tmp/maintenance/branch-inventory.json';
const DEFAULT_OUTPUT_JSON = 'tmp/maintenance/remote-branch-triage.json';
const DEFAULT_OUTPUT_MD = 'tmp/maintenance/remote-branch-triage.md';
const DEFAULT_GH_PR_LIMIT = 1000;
const DEFAULT_GH_PR_BASE = '';

export const LOW_RISK_PREFIXES = ['docs/', 'chore/', 'test/', 'ci/', 'types/'];
export const HIGH_RISK_PREFIXES = ['feat/', 'feature/', 'fix/', 'ops/', 'policy/'];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-branch-triage.mjs [options]

Options:
  --input-json <path>  Branch inventory JSON path (default: ${DEFAULT_INPUT_JSON})
  --output-json <path> Triage JSON output path (default: ${DEFAULT_OUTPUT_JSON})
  --output-md <path>   Triage Markdown output path (default: ${DEFAULT_OUTPUT_MD})
  --gh-pr-limit <n>    Max PRs to inspect via gh (default: ${DEFAULT_GH_PR_LIMIT}, 0 disables lookup)
  --gh-pr-base <name>  Optional GitHub PR base branch filter (default: auto-derived from inventory)
  --help               Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    inputJson: DEFAULT_INPUT_JSON,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    ghPrLimit: DEFAULT_GH_PR_LIMIT,
    ghPrBase: DEFAULT_GH_PR_BASE,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--input-json') {
      options.inputJson = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--gh-pr-limit') {
      options.ghPrLimit = Number(argv[++i]);
      continue;
    }
    if (arg === '--gh-pr-base') {
      options.ghPrBase = String(argv[++i] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.inputJson) throw new Error('--input-json is required');
  if (!options.outputJson) throw new Error('--output-json is required');
  if (!options.outputMd) throw new Error('--output-md is required');
  if (!Number.isInteger(options.ghPrLimit) || options.ghPrLimit < 0) {
    throw new Error('--gh-pr-limit must be a non-negative integer');
  }
  return options;
};

const runCommand = (command, args) =>
  execFileSync(command, args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  }).trimEnd();

const runCommandSafe = (command, args) => {
  try {
    return {
      ok: true,
      output: runCommand(command, args),
    };
  } catch (error) {
    const stderr = error && error.stderr ? String(error.stderr) : '';
    const stdout = error && error.stdout ? String(error.stdout) : '';
    return {
      ok: false,
      output: `${stdout}\n${stderr}`.trim(),
      message: error instanceof Error ? error.message : String(error),
    };
  }
};

const runGhSafe = (args) => runCommandSafe('gh', args);
const runGitSafe = (args) => runCommandSafe('git', args);

const shellQuote = (value) => `'${String(value).replace(/'/g, `'"'"'`)}'`;

const escapeCell = (value) =>
  String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');

const renderTable = (headers, rows) => {
  if (rows.length === 0) {
    return '- (none)\n';
  }
  const head = `| ${headers.join(' | ')} |\n| ${headers.map(() => '---').join(' | ')} |`;
  const body = rows
    .map((row) => `| ${row.map((cell) => escapeCell(cell)).join(' | ')} |`)
    .join('\n');
  return `${head}\n${body}\n`;
};

const prefixOfBranch = (branch) => {
  const value = String(branch || '');
  if (!value.includes('/')) return '(no-slash)';
  return value.split('/', 1)[0];
};

export const classifyRiskBand = (branch) => {
  const value = String(branch || '');
  if (LOW_RISK_PREFIXES.some((prefix) => value.startsWith(prefix))) return 'low';
  if (HIGH_RISK_PREFIXES.some((prefix) => value.startsWith(prefix))) return 'high';
  return 'standard';
};

const normalizePrState = (value) => {
  const state = String(value || '').toUpperCase();
  if (state === 'OPEN') return 'open';
  if (state === 'MERGED') return 'merged';
  if (state === 'CLOSED') return 'closed';
  return 'unknown';
};

const prTimestamp = (item) =>
  String(item?.updatedAt || item?.mergedAt || item?.closedAt || '');

const sortPullRequests = (items) =>
  [...items].sort((a, b) => prTimestamp(b).localeCompare(prTimestamp(a)));

export const groupPullRequestsByHeadRefName = (items) => {
  const byBranch = new Map();
  for (const item of items) {
    if (!item?.headRefName) continue;
    const current = byBranch.get(item.headRefName) || [];
    current.push(item);
    byBranch.set(item.headRefName, sortPullRequests(current));
  }
  return byBranch;
};

const parseGitHubRemoteUrl = (value) => {
  const match = String(value || '')
    .trim()
    .match(/github\.com[:/](?<owner>[^/]+)\/(?<repo>[^/]+?)(?:\.git)?$/i);
  if (!match?.groups?.owner || !match?.groups?.repo) {
    return {
      owner: '',
      name: '',
    };
  }
  return {
    owner: match.groups.owner,
    name: match.groups.repo,
  };
};

const loadRepositoryIdentity = (remoteName, { gitRunner = runGitSafe } = {}) => {
  const result = gitRunner(['config', '--get', `remote.${remoteName}.url`]);
  if (!result.ok) {
    return {
      owner: '',
      name: '',
    };
  }
  return parseGitHubRemoteUrl(result.output);
};

export const loadPullRequests = (
  {
    limit = DEFAULT_GH_PR_LIMIT,
    baseBranch = DEFAULT_GH_PR_BASE,
    repositoryOwner = '',
    repositoryName = '',
  } = {},
  { ghRunner = runGhSafe } = {},
) => {
  if (limit === 0) {
    return {
      available: false,
      disabled: true,
      reason: 'gh pr lookup disabled',
      requestedBaseBranch: baseBranch,
      requestedLimit: limit,
      partialResults: false,
      lookupCoverage: 'disabled',
      items: [],
      byHeadRefName: new Map(),
    };
  }

  const queryLimit = limit + 1;
  const args = [
    'pr',
    'list',
    '--state',
    'all',
    '--limit',
    String(queryLimit),
    '--json',
    'number,title,url,state,isDraft,mergedAt,closedAt,updatedAt,headRefName,headRefOid,baseRefName,headRepository,headRepositoryOwner',
  ];
  if (baseBranch) {
    args.splice(6, 0, '--base', baseBranch);
  }

  const result = ghRunner(args);
  if (!result.ok) {
    return {
      available: false,
      disabled: false,
      reason: result.message || result.output || 'gh unavailable',
      requestedBaseBranch: baseBranch,
      requestedLimit: limit,
      partialResults: false,
      lookupCoverage: 'unavailable',
      items: [],
      byHeadRefName: new Map(),
    };
  }

  const filteredItems = JSON.parse(result.output || '[]')
    .filter((item) => item && item.headRefName)
    .filter((item) => !baseBranch || item.baseRefName === baseBranch)
    .filter(
      (item) =>
        !repositoryOwner ||
        !repositoryName ||
        (item.headRepositoryOwner?.login === repositoryOwner && item.headRepository?.name === repositoryName),
    )
    .map((item) => ({
      number: item.number,
      title: item.title || '',
      url: item.url || '',
      state: normalizePrState(item.state),
      isDraft: Boolean(item.isDraft),
      mergedAt: item.mergedAt || '',
      closedAt: item.closedAt || '',
      updatedAt: item.updatedAt || '',
      headRefName: item.headRefName,
      headRefOid: item.headRefOid || '',
      baseRefName: item.baseRefName || '',
    }));
  const partialResults = filteredItems.length > limit;
  const items = filteredItems.slice(0, limit);

  return {
    available: true,
    disabled: false,
    reason: '',
    requestedBaseBranch: baseBranch,
    requestedLimit: limit,
    partialResults,
    lookupCoverage: partialResults ? 'truncated' : 'complete',
    items,
    byHeadRefName: groupPullRequestsByHeadRefName(items),
  };
};

const countBy = (items, keyOf, knownKeys = []) => {
  const counts = Object.fromEntries(knownKeys.map((key) => [key, 0]));
  for (const item of items) {
    const key = keyOf(item);
    counts[key] = (counts[key] || 0) + 1;
  }
  return counts;
};

const summarizePrefixes = (items, top = 10) => {
  const byPrefix = new Map();
  for (const item of items) {
    const prefix = prefixOfBranch(item.branch);
    const current = byPrefix.get(prefix) || { prefix, count: 0, examples: [] };
    current.count += 1;
    if (current.examples.length < 3) {
      current.examples.push(item.branch);
    }
    byPrefix.set(prefix, current);
  }
  return [...byPrefix.values()]
    .sort((a, b) => b.count - a.count || a.prefix.localeCompare(b.prefix))
    .slice(0, top);
};

const normalizeRemoteMergedCandidates = (inventory) => {
  const detailed = inventory?.candidates?.remoteMergedDetailed || [];
  if (Array.isArray(detailed) && detailed.length > 0) {
    return detailed.map((item) => ({
      branch: item.branch,
      oid: item.oid || '',
    }));
  }
  return (inventory?.candidates?.remoteMerged || []).map((branch) => ({
    branch,
    oid: '',
  }));
};

const normalizeRemoteStaleCandidates = (inventory) => {
  const detailed = inventory?.candidates?.remoteStaleByAgeDetailed || [];
  if (Array.isArray(detailed) && detailed.length > 0) {
    return detailed.map((item) => ({
      branch: item.branch,
      oid: item.oid || '',
      ageDays: item.ageDays,
    }));
  }
  return (inventory?.candidates?.remoteStaleByAge || []).map((item) => ({
    branch: item.branch,
    oid: '',
    ageDays: item.ageDays,
  }));
};

const latestPullRequestSummary = (items, { branchOid = '' } = {}) => {
  if (!items || items.length === 0) {
    return {
      state: 'none',
      counts: { open: 0, closed: 0, merged: 0 },
      latest: null,
      baseBranches: [],
      matchMode: 'none',
    };
  }

  const sorted = sortPullRequests(items);
  const counts = countBy(sorted, (item) => item.state, ['open', 'closed', 'merged']);
  const oid = String(branchOid || '').trim();
  const exactMatches = oid ? sorted.filter((item) => item.headRefOid === oid) : [];
  const matched = exactMatches.length > 0 ? exactMatches : sorted;
  const baseBranches = [...new Set(matched.map((item) => item.baseRefName).filter(Boolean))].sort();
  const latest = matched[0];
  let state = latest.state;
  let matchMode = oid ? 'head-oid' : 'branch-name-only';

  if (oid) {
    if (exactMatches.length === 0) {
      state = 'ambiguous';
      matchMode = 'branch-name-only';
    } else if (exactMatches.length > 1) {
      state = 'ambiguous';
    }
  } else if (sorted.length > 1) {
    state = 'ambiguous';
  }

  return {
    state,
    counts,
    latest: {
      number: latest.number,
      title: latest.title,
      url: latest.url,
      state: latest.state,
      isDraft: latest.isDraft,
      baseRefName: latest.baseRefName,
      mergedAt: latest.mergedAt,
      closedAt: latest.closedAt,
      updatedAt: latest.updatedAt,
      headRefOid: latest.headRefOid || '',
    },
    baseBranches,
    matchMode,
  };
};

export const classifyStaleAction = ({ ageDays, riskBand, prState, prLookupAvailable }) => {
  if (!prLookupAvailable) return 'manual-review';
  if (prState === 'ambiguous') return 'manual-review';
  if (prState === 'open') return 'keep-review';
  if (riskBand === 'low' && ageDays >= 120) return 'delete-review';
  if ((prState === 'closed' || prState === 'merged') && ageDays >= 180) return 'archive-review';
  if (prState === 'none' && riskBand === 'high') return 'archive-review';
  if (prState === 'none' && riskBand === 'low') return 'delete-review';
  return 'keep-review';
};

const formatLatestPrLabel = (latestPr) => {
  if (!latestPr) return '(none)';
  return `#${latestPr.number} (${latestPr.state})`;
};

const renderSummaryCounts = (counts, order) =>
  order.map((key) => `${key}=${counts[key] || 0}`).join(', ');

const lookupStatusState = (githubPullRequests) => {
  if (githubPullRequests?.available && githubPullRequests?.lookupCoverage === 'truncated') return 'partial';
  if (githubPullRequests?.available) return 'enabled';
  if (githubPullRequests?.disabled) return 'disabled';
  return 'unavailable';
};

const formatLookupStatus = (githubPullRequests) => {
  const state = lookupStatusState(githubPullRequests);
  if (state === 'enabled' || state === 'partial') {
    return `${state} (matched=${githubPullRequests.matchedItems}, base=${githubPullRequests.requestedBaseBranch || 'all'}, coverage=${githubPullRequests.lookupCoverage || 'complete'})`;
  }
  if (state === 'disabled') {
    return 'disabled';
  }
  return `unavailable (${githubPullRequests?.reason || 'gh unavailable'})`;
};

const buildIssueCommentTemplate = (report) => {
  const prefixLines = report.summary.topPrefixes
    .map((item) => `- ${item.prefix}: ${item.count} (${item.examples.join(', ')})`)
    .join('\n');
  const deleteLines = report.remoteMerged.map((item) => item.deleteCommand).join('\n');

  return `## Remote branch triage summary
- generatedAt: ${report.generatedAt}
- remote merged candidates: ${report.summary.remoteMergedCandidates}
- remote stale candidates: ${report.summary.remoteStaleCandidates}
- PR lookup coverage: ${report.githubPullRequests.lookupCoverage || 'unknown'}
- stale risk bands: ${renderSummaryCounts(report.summary.staleByRiskBand, ['low', 'standard', 'high'])}
- stale PR states: ${renderSummaryCounts(report.summary.staleByPrState, ['open', 'closed', 'merged', 'none', 'ambiguous', 'unavailable'])}
- stale PR match modes: ${renderSummaryCounts(report.summary.staleByMatchMode, ['head-oid', 'branch-name-only', 'none'])}

### Top prefixes
${prefixLines || '- (none)'}

### Remote delete commands (operator approval required)
\`\`\`bash
${deleteLines || '# (none)'}
\`\`\`
`;
};

export const buildTriageReport = (
  inventory,
  {
    generatedAt = new Date().toISOString(),
    inputJsonPath = DEFAULT_INPUT_JSON,
    pullRequests = {
      available: false,
      disabled: true,
      reason: 'gh pr lookup disabled',
      requestedBaseBranch: '',
      requestedLimit: 0,
      partialResults: false,
      lookupCoverage: 'disabled',
      items: [],
      byHeadRefName: new Map(),
    },
  } = {},
) => {
  const remoteName = inventory?.remote || 'origin';
  const prLookupAvailable = Boolean(pullRequests?.available);
  const remoteMerged = normalizeRemoteMergedCandidates(inventory).map((item) => {
    const prSummary = latestPullRequestSummary(pullRequests?.byHeadRefName?.get(item.branch) || [], {
      branchOid: item.oid,
    });
    return {
      branch: item.branch,
      branchOid: item.oid || '',
      prefix: prefixOfBranch(item.branch),
      proposedAction: 'delete',
      approval: 'required',
      rationale: 'merged-to-base inventory candidate',
      prState: prLookupAvailable ? prSummary.state : 'unavailable',
      prMatchMode: prSummary.matchMode,
      prCounts: prSummary.counts,
      latestPr: prSummary.latest,
      baseBranches: prSummary.baseBranches,
      deleteCommand: `git push ${shellQuote(remoteName)} --delete ${shellQuote(item.branch)}`,
    };
  });

  const remoteStale = normalizeRemoteStaleCandidates(inventory).map((item) => {
    const riskBand = classifyRiskBand(item.branch);
    const prSummary = latestPullRequestSummary(pullRequests?.byHeadRefName?.get(item.branch) || [], {
      branchOid: item.oid,
    });
    const prState = prLookupAvailable ? prSummary.state : 'unavailable';
    return {
      branch: item.branch,
      branchOid: item.oid || '',
      prefix: prefixOfBranch(item.branch),
      ageDays: item.ageDays,
      riskBand,
      prState,
      prMatchMode: prSummary.matchMode,
      prCounts: prSummary.counts,
      latestPr: prSummary.latest,
      baseBranches: prSummary.baseBranches,
      proposedAction: classifyStaleAction({
        ageDays: item.ageDays,
        riskBand,
        prState,
        prLookupAvailable,
      }),
      decision: '',
      notes: '',
    };
  });

  const summary = {
    remoteMergedCandidates: remoteMerged.length,
    remoteStaleCandidates: remoteStale.length,
    staleByRiskBand: countBy(remoteStale, (item) => item.riskBand, ['low', 'standard', 'high']),
    staleByPrState: countBy(
      remoteStale,
      (item) => item.prState,
      ['open', 'closed', 'merged', 'none', 'ambiguous', 'unavailable'],
    ),
    staleByMatchMode: countBy(remoteStale, (item) => item.prMatchMode, ['head-oid', 'branch-name-only', 'none']),
    topPrefixes: summarizePrefixes(remoteStale),
  };

  const report = {
    generatedAt,
    sourceInventory: {
      path: inputJsonPath,
      generatedAt: inventory?.generatedAt || '',
      base: inventory?.base || '',
      remote: remoteName,
    },
    githubPullRequests: {
      available: prLookupAvailable,
      disabled: Boolean(pullRequests?.disabled),
      reason: pullRequests?.reason || '',
      requestedBaseBranch: pullRequests?.requestedBaseBranch || '',
      requestedLimit: pullRequests?.requestedLimit ?? DEFAULT_GH_PR_LIMIT,
      partialResults: Boolean(pullRequests?.partialResults),
      lookupCoverage: pullRequests?.lookupCoverage || (prLookupAvailable ? 'complete' : 'unavailable'),
      matchedItems: Array.isArray(pullRequests?.items) ? pullRequests.items.length : 0,
    },
    summary,
    remoteMerged,
    remoteStale,
    templates: {
      issueComment: '',
    },
  };

  report.templates.issueComment = buildIssueCommentTemplate(report);
  return report;
};

export const renderMarkdown = (report) => {
  const mergedRows = report.remoteMerged.map((item) => [
    `\`${item.branch}\``,
    item.branchOid || '-',
    formatLatestPrLabel(item.latestPr),
    item.prMatchMode,
    item.baseBranches.join(', ') || '-',
    item.prState,
    item.proposedAction,
    item.approval,
  ]);
  const staleRows = report.remoteStale.map((item) => [
    `\`${item.branch}\``,
    String(item.ageDays),
    item.branchOid || '-',
    item.riskBand,
    item.prState,
    item.prMatchMode,
    formatLatestPrLabel(item.latestPr),
    item.baseBranches.join(', ') || '-',
    item.proposedAction,
    item.decision || '(operator)',
    item.notes || '',
  ]);
  const prefixRows = report.summary.topPrefixes.map((item) => [
    item.prefix,
    String(item.count),
    item.examples.join(', '),
  ]);
  const deleteCommands = report.remoteMerged.map((item) => item.deleteCommand).join('\n') || '# (none)';
  const lookupStatus = formatLookupStatus(report.githubPullRequests);
  const lookupWarning =
    report.githubPullRequests.lookupCoverage === 'truncated'
      ? '> Warning: GitHub PR lookup hit the configured window limit. Treat `prState=none` as incomplete evidence until the lookup window is widened.\n'
      : '';

  return `# Remote Branch Triage Worksheet

- generatedAt: ${report.generatedAt}
- source inventory: \`${report.sourceInventory.path}\`
- inventory generatedAt: ${report.sourceInventory.generatedAt}
- base: \`${report.sourceInventory.base}\`
- remote: \`${report.sourceInventory.remote}\`
- GitHub PR lookup: ${lookupStatus}
${lookupWarning}

## Summary

- remote merged candidates: ${report.summary.remoteMergedCandidates}
- remote stale candidates: ${report.summary.remoteStaleCandidates}
- stale risk bands: ${renderSummaryCounts(report.summary.staleByRiskBand, ['low', 'standard', 'high'])}
- stale PR states: ${renderSummaryCounts(report.summary.staleByPrState, ['open', 'closed', 'merged', 'none', 'ambiguous', 'unavailable'])}
- stale PR match modes: ${renderSummaryCounts(report.summary.staleByMatchMode, ['head-oid', 'branch-name-only', 'none'])}

### Top stale prefixes

${renderTable(['prefix', 'count', 'examples'], prefixRows)}
## Remote merged candidates (delete after operator approval)

${renderTable(['branch', 'branchOid', 'latestPr', 'match', 'bases', 'prState', 'proposed', 'approval'], mergedRows)}
## Remote stale candidates (operator triage required)

${renderTable(['branch', 'ageDays', 'branchOid', 'risk', 'prState', 'match', 'latestPr', 'bases', 'proposed', 'decision', 'notes'], staleRows)}
## Approval checklist

- [ ] \`pnpm run maintenance:branch:inventory\` を再実行して最新 inventory を確認した
- [ ] remote merged candidates の削除対象を確認した
- [ ] remote stale candidates に keep / archive / delete を記録した
- [ ] remote delete 実行前に operator approval を取得した

## Remote delete commands (operator approval required)

\`\`\`bash
${deleteCommands}
\`\`\`

## Issue/comment template

\`\`\`\`md
${report.templates.issueComment}
\`\`\`\`

## Suggested commands

\`\`\`bash
# Refresh source inventory
pnpm run maintenance:branch:inventory

# Render triage worksheet (disable PR lookup with --gh-pr-limit 0 when needed)
pnpm run maintenance:branch:triage:render

# Remote delete (operator approval required)
node scripts/maintenance/branch-cleanup.mjs --scope remote --max 100 --apply
\`\`\`
`;
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const inputJsonPath = path.resolve(options.inputJson);
  const outputJsonPath = path.resolve(options.outputJson);
  const outputMdPath = path.resolve(options.outputMd);

  const inventory = JSON.parse(fs.readFileSync(inputJsonPath, 'utf8'));
  const repositoryIdentity = loadRepositoryIdentity(inventory?.remote || 'origin');
  const ghPrBase = options.ghPrBase || deriveGhPrBaseBranch(inventory?.base || '', inventory?.remote || 'origin');
  const pullRequests = loadPullRequests({
    limit: options.ghPrLimit,
    baseBranch: ghPrBase,
    repositoryOwner: repositoryIdentity.owner,
    repositoryName: repositoryIdentity.name,
  });
  const report = buildTriageReport(inventory, {
    inputJsonPath: options.inputJson,
    pullRequests,
  });
  const markdown = renderMarkdown(report);

  fs.mkdirSync(path.dirname(outputJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(outputMdPath), { recursive: true });
  fs.writeFileSync(outputJsonPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  fs.writeFileSync(outputMdPath, markdown, 'utf8');

  console.log(`[remote-branch-triage] wrote ${outputJsonPath}`);
  console.log(`[remote-branch-triage] wrote ${outputMdPath}`);
  console.log(
    `[remote-branch-triage] merged=${report.summary.remoteMergedCandidates} stale=${report.summary.remoteStaleCandidates} prLookup=${lookupStatusState(report.githubPullRequests)}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error(`[remote-branch-triage] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
