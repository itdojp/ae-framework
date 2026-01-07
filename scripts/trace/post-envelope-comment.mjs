#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

function isErrnoException(value) {
  if (!value || typeof value !== 'object') return false;
  if (!('code' in value)) return false;
  return typeof value.code === 'string';
}

function readFileIfExists(filePath) {
  try {
    return fs.readFileSync(filePath, 'utf8');
  } catch (error) {
    if (isErrnoException(error) && error.code === 'ENOENT') {
      return null;
    }
    throw error;
  }
}

function parseArgs(argv) {
  const options = {
    envelope: process.env.ENVELOPE_COMMENT_SOURCE ?? 'artifacts/trace/report-envelope.json',
    issue: null,
    pr: null,
    repo: process.env.GITHUB_REPOSITORY ?? null,
    dryRun: false,
    output: null,
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--envelope' || arg === '-e') && next) {
      options.envelope = next;
      i += 1;
    } else if ((arg === '--issue' || arg === '-i') && next) {
      const parsed = Number(next);
      options.issue = Number.isNaN(parsed) ? null : parsed;
      i += 1;
    } else if (arg === '--pr' && next) {
      const parsed = Number(next);
      options.pr = Number.isNaN(parsed) ? null : parsed;
      i += 1;
    } else if ((arg === '--repo' || arg === '-r') && next) {
      options.repo = next;
      i += 1;
    } else if (arg === '--output' && next) {
      options.output = next;
      i += 1;
    } else if (arg === '--dry-run') {
      options.dryRun = true;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node scripts/trace/post-envelope-comment.mjs [options]

Options:
  -e, --envelope <file>    Envelope JSON path (default: artifacts/trace/report-envelope.json)
  -i, --issue <number>     Issue number to comment on
      --pr <number>        Pull request number to comment on
  -r, --repo <owner/repo>  Repository (default: $GITHUB_REPOSITORY)
      --output <file>      Write the generated comment Markdown to a file
      --dry-run            Print the comment and skip posting to GitHub
  -h, --help               Show this message
`);
      process.exit(0);
    }
  }

  return options;
}

function readEnvelope(filePath) {
  const resolved = path.resolve(filePath);
  const content = readFileIfExists(resolved);
  if (content === null) {
    console.error(`[envelope-comment] envelope not found: ${resolved}`);
    process.exit(1);
  }
  try {
    return JSON.parse(content);
  } catch (error) {
    console.error(`[envelope-comment] failed to parse envelope: ${resolved}`);
    const message = error instanceof Error ? error.message : String(error);
    console.error(message);
    process.exit(1);
  }
}

const inlineCode = (value) => `\`${value}\``;

function formatArtifacts(envelope) {
  const records = Array.isArray(envelope?.artifacts) ? envelope.artifacts : [];
  const items = records
    .filter((item) => typeof item?.path === 'string' && item.path.trim())
    .map((item) => {
      const label = item.description ? `${item.description}` : 'artifact';
      return `- ${label}: ${inlineCode(item.path)}`;
    });
  if (items.length === 0) return null;
  return ['### Artifacts', ...items].join('\n');
}

function collectStringValues(...maybeArrays) {
  const values = new Set();
  for (const candidate of maybeArrays) {
    if (!Array.isArray(candidate)) continue;
    for (const value of candidate) {
      if (typeof value === 'string' && value.trim()) {
        values.add(value.trim());
      }
    }
  }
  return Array.from(values);
}

function formatTraceIds(envelope) {
  const traceIds = collectStringValues(
    envelope?.summary?.trace?.traceIds,
    envelope?.summary?.traceIds,
    envelope?.correlation?.traceIds,
  );
  if (traceIds.length === 0) return null;
  const lines = traceIds.sort().map((id) => `- ${inlineCode(id)}`);
  return ['### Trace IDs', ...lines].join('\n');
}

function formatTempoLinks(envelope) {
  const tempoLinks = collectStringValues(envelope?.tempoLinks, envelope?.summary?.tempoLinks);
  if (tempoLinks.length === 0) return null;
  const items = tempoLinks.sort().map((link) => `- ${link}`);
  return ['### Tempo Links', ...items].join('\n');
}

function formatDomains(envelope) {
  const domains = Array.isArray(envelope?.summary?.trace?.domains) ? envelope.summary.trace.domains : [];
  if (domains.length === 0) return null;
  const items = domains.map((domain) => {
    const label = domain?.label ?? domain?.key ?? 'unknown';
    const status = domain?.status ?? 'unknown';
    const issues = domain?.issues ?? 0;
    const traceIds = Array.isArray(domain?.traceIds) && domain.traceIds.length > 0 ? ` traceIds=${domain.traceIds.join(', ')}` : '';
    return `- **${label}**: status=${status} issues=${issues}${traceIds}`;
  });
  return ['### Trace Domains', ...items].join('\n');
}

function getCaseValidity(value) {
  if (value === true) return 'valid';
  if (value === false) return 'invalid';
  return 'unknown';
}

function formatCases(envelope) {
  const cases = Array.isArray(envelope?.summary?.cases) ? envelope.summary.cases : [];
  if (cases.length === 0) return null;
  const items = cases.map((entry) => {
    const label = entry.label ?? entry.format ?? entry.key ?? 'unknown';
    const valid = getCaseValidity(entry.valid);
    const traceIds = Array.isArray(entry.traceIds) ? entry.traceIds.filter((id) => typeof id === 'string' && id.trim()) : [];
    const suffix = traceIds.length > 0 ? ` traceIds=${traceIds.join(', ')}` : '';
    return `- **${label}**: status=${valid}${suffix}`;
  });
  return ['### Trace Cases', ...items].join('\n');
}

function buildComment(envelope) {
  const meta = envelope?.correlation ?? {};
  const source = envelope?.source ?? 'unknown';
  const runId = meta.runId ?? '(unknown run)';
  const branch = meta.branch ?? '(unknown branch)';
  const status = envelope?.summary?.trace?.status ?? envelope?.summary?.status ?? 'unknown';
  const workflow = meta.workflow ?? null;

  const header = [
    '## Trace Envelope Summary',
    `- Source: ${inlineCode(source)}`,
    `- Status: ${inlineCode(status)}`,
    `- Run: ${inlineCode(runId)}`,
    `- Branch: ${inlineCode(branch)}`,
    workflow ? `- Workflow: ${inlineCode(workflow)}` : null,
  ].filter(Boolean).join('\n');

  const sections = [
    header,
    formatTraceIds(envelope),
    formatTempoLinks(envelope),
    formatDomains(envelope),
    formatArtifacts(envelope),
    formatCases(envelope),
  ].filter(Boolean);

  return sections.join('\n\n');
}

function writeOutput(outputPath, content) {
  if (!outputPath) return;
  const resolved = path.resolve(outputPath);
  fs.mkdirSync(path.dirname(resolved), { recursive: true });
  fs.writeFileSync(resolved, `${content}\n`);
  console.log(`[envelope-comment] wrote comment body to ${resolved}`);
}

function postToGithub({ repo, issueNumber, body }) {
  if (!repo) {
    console.error('[envelope-comment] repository not specified (use --repo or set GITHUB_REPOSITORY)');
    process.exit(1);
  }
  if (!issueNumber) {
    console.error('[envelope-comment] issue or PR number is required');
    process.exit(1);
  }
  const payload = JSON.stringify({ body });
  const args = [
    'api',
    `repos/${repo}/issues/${issueNumber}/comments`,
    '--method',
    'POST',
    '-H',
    'Content-Type: application/json',
    '--input',
    '-',
  ];
  const result = spawnSync('gh', args, { stdio: ['pipe', 'inherit', 'inherit'], input: payload });
  if (result.status !== 0) {
    console.error('[envelope-comment] failed to post comment with gh');
    process.exit(result.status ?? 1);
  }
}

function main() {
  const options = parseArgs(process.argv);
  const envelope = readEnvelope(options.envelope);
  const body = buildComment(envelope);
  if (!body) {
    console.error('[envelope-comment] failed to build comment body');
    process.exit(1);
  }
  if (options.output) {
    writeOutput(options.output, body);
  }
  console.log(body);
  if (options.dryRun) {
    return;
  }
  const issueNumber = options.pr ?? options.issue;
  postToGithub({ repo: options.repo, issueNumber, body });
}

const isDirectExecution = (() => {
  const invoked = process.argv[1] ? path.resolve(process.argv[1]) : null;
  const current = fileURLToPath(import.meta.url);
  return invoked && current === invoked;
})();

if (isDirectExecution) {
  main();
}
