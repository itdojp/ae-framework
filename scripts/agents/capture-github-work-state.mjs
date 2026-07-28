#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import {
  captureGitHubWorkState,
  validateSnapshotSemantics,
} from './github-work-state-lib.mjs';

const ISSUE_QUERY = `
query GitHubWorkStateIssue($owner: String!, $name: String!, $issue: Int!) {
  repository(owner: $owner, name: $name) {
    issue(number: $issue) { number }
  }
}`;

const PULL_REQUEST_QUERY = `
query GitHubWorkStatePullRequest($owner: String!, $name: String!, $pullRequest: Int!) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $pullRequest) {
      number
      baseRefName
      baseRefOid
      headRefName
      headRefOid
      isDraft
      mergeStateStatus
    }
  }
}`;

const REVIEW_THREADS_QUERY = `
query GitHubWorkStateReviewThreads(
  $owner: String!
  $name: String!
  $pullRequest: Int!
  $pageSize: Int!
  $cursor: String
) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $pullRequest) {
      reviewThreads(first: $pageSize, after: $cursor) {
        totalCount
        pageInfo { hasNextPage endCursor }
        nodes {
          id
          isResolved
          path
          comments(first: 1) { nodes { id } }
        }
      }
    }
  }
}`;

const REQUIRED_CHECKS_QUERY = `
query GitHubWorkStateRequiredChecks(
  $owner: String!
  $name: String!
  $pullRequest: Int!
  $pageSize: Int!
  $cursor: String
) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $pullRequest) {
      commits(last: 1) {
        nodes {
          commit {
            oid
            statusCheckRollup {
              contexts(first: $pageSize, after: $cursor) {
                totalCount
                pageInfo { hasNextPage endCursor }
                nodes {
                  __typename
                  ... on CheckRun {
                    name
                    status
                    conclusion
                    databaseId
                    checkSuite {
                      app { databaseId }
                      commit { oid }
                    }
                  }
                  ... on StatusContext {
                    context
                    state
                    commit { oid }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}`;

function readRequiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (!value || value.startsWith('--')) throw new Error(`missing value for ${option}`);
  return value;
}

function readPositiveInteger(argv, index, option, { maximum = null } = {}) {
  const raw = readRequiredValue(argv, index, option);
  if (!/^[1-9][0-9]*$/u.test(raw)) throw new Error(`${option} must be a positive integer`);
  const value = Number(raw);
  if (!Number.isSafeInteger(value) || (maximum !== null && value > maximum)) {
    throw new Error(`${option} must be a positive integer${maximum === null ? '' : ` <= ${maximum}`}`);
  }
  return value;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    repository: null,
    issueNumber: null,
    pullRequestNumber: null,
    expectedHead: null,
    outputPath: null,
    generatedAt: null,
    pageSize: 100,
    help: false,
  };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    } else if (arg === '--repo') {
      options.repository = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--issue') {
      options.issueNumber = readPositiveInteger(argv, index, arg);
      index += 1;
    } else if (arg === '--pr') {
      options.pullRequestNumber = readPositiveInteger(argv, index, arg);
      index += 1;
    } else if (arg === '--expected-head') {
      options.expectedHead = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--output') {
      options.outputPath = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--page-size') {
      options.pageSize = readPositiveInteger(argv, index, arg, { maximum: 100 });
      index += 1;
    } else if (arg === '--help' || arg === '-h') {
      options.help = true;
    } else {
      throw new Error(`unknown option: ${arg}`);
    }
  }
  if (!options.help) {
    for (const [key, flag] of [
      ['repository', '--repo'],
      ['issueNumber', '--issue'],
      ['pullRequestNumber', '--pr'],
      ['expectedHead', '--expected-head'],
      ['outputPath', '--output'],
    ]) {
      if (!options[key]) throw new Error(`${flag} is required`);
    }
  }
  return options;
}

function printHelp() {
  process.stdout.write(
    'Capture a content-addressed GitHub Issue/PR authority snapshot.\n\n'
      + 'Usage:\n'
      + '  node scripts/agents/capture-github-work-state.mjs \\\n'
      + '    --repo owner/name --issue N --pr N --expected-head SHA --output PATH\n\n'
      + 'Options:\n'
      + '  --generated-at ISO8601  Explicit capture time (fixture/replay use)\n'
      + '  --page-size 1..100       GraphQL page size (default: 100)\n',
  );
}

function splitRepository(repository) {
  const [owner, name, extra] = String(repository).split('/');
  if (!owner || !name || extra) throw new Error('--repo must use owner/name format');
  return { owner, name };
}

function runGhJson(args, { input = null } = {}) {
  const result = spawnSync('gh', args, {
    encoding: 'utf8',
    input,
    env: process.env,
    maxBuffer: 16 * 1024 * 1024,
  });
  if (result.error) throw result.error;
  if (result.status !== 0) {
    const stderr = String(result.stderr ?? '').trim().slice(0, 800);
    throw new Error(`gh ${args.slice(0, 2).join(' ')} failed (exit ${result.status}): ${stderr}`);
  }
  try {
    return JSON.parse(result.stdout);
  } catch (error) {
    throw new Error(`gh returned malformed JSON: ${error instanceof Error ? error.message : String(error)}`);
  }
}

function executeGraphql(query, variables) {
  const response = runGhJson(['api', 'graphql', '--input', '-'], {
    input: JSON.stringify({ query, variables }),
  });
  if (Array.isArray(response?.errors) && response.errors.length > 0) {
    const messages = response.errors
      .map((entry) => typeof entry?.message === 'string' ? entry.message : 'unknown GraphQL error')
      .join('; ')
      .slice(0, 800);
    throw new Error(`GitHub GraphQL query failed: ${messages}`);
  }
  return response;
}

function buildGitHubClients() {
  return {
    async fetchIssue({ repository, issueNumber }) {
      const { owner, name } = splitRepository(repository);
      const response = executeGraphql(ISSUE_QUERY, { owner, name, issue: issueNumber });
      return response?.data?.repository?.issue ?? null;
    },
    async fetchPullRequest({ repository, pullRequestNumber }) {
      const { owner, name } = splitRepository(repository);
      const response = executeGraphql(PULL_REQUEST_QUERY, {
        owner,
        name,
        pullRequest: pullRequestNumber,
      });
      return response?.data?.repository?.pullRequest ?? null;
    },
    async fetchReviewThreadsPage({ repository, pullRequestNumber, cursor, pageSize }) {
      const { owner, name } = splitRepository(repository);
      const response = executeGraphql(REVIEW_THREADS_QUERY, {
        owner,
        name,
        pullRequest: pullRequestNumber,
        pageSize,
        cursor,
      });
      const page = response?.data?.repository?.pullRequest?.reviewThreads;
      if (!page) throw new Error('GitHub did not return reviewThreads');
      return page;
    },
    async fetchRequiredChecksPage({ repository, pullRequestNumber, headSha, cursor, pageSize }) {
      const { owner, name } = splitRepository(repository);
      const response = executeGraphql(REQUIRED_CHECKS_QUERY, {
        owner,
        name,
        pullRequest: pullRequestNumber,
        pageSize,
        cursor,
      });
      const commit = response?.data?.repository?.pullRequest?.commits?.nodes?.[0]?.commit;
      if (!commit) throw new Error('GitHub did not return the PR head commit');
      if (commit.oid !== headSha) {
        throw new Error(`status rollup is bound to wrong head ${commit.oid}; expected ${headSha}`);
      }
      return commit.statusCheckRollup?.contexts ?? {
        totalCount: 0,
        nodes: [],
        pageInfo: { hasNextPage: false, endCursor: null },
      };
    },
    async fetchRequiredCheckPolicy({ repository, baseRef }) {
      const endpoint = `repos/${repository}/branches/${encodeURIComponent(baseRef)}/protection/required_status_checks`;
      const response = runGhJson(['api', endpoint]);
      const checks = Array.isArray(response?.checks)
        ? response.checks.map((entry) => ({ name: entry.context, appId: entry.app_id }))
        : [];
      const representedNames = new Set(checks.map((entry) => entry.name));
      const legacyContexts = Array.isArray(response?.contexts)
        ? response.contexts
          .filter((name) => !representedNames.has(name))
          .map((name) => ({ name, appId: null }))
        : [];
      return [...checks, ...legacyContexts];
    },
  };
}

function writeSnapshot(outputPath, snapshot) {
  const resolved = path.resolve(outputPath);
  fs.mkdirSync(path.dirname(resolved), { recursive: true });
  const temporary = `${resolved}.tmp-${process.pid}`;
  fs.writeFileSync(temporary, `${JSON.stringify(snapshot, null, 2)}\n`, { encoding: 'utf8', mode: 0o600 });
  fs.renameSync(temporary, resolved);
  return resolved;
}

export async function run(argv = process.argv.slice(2), clients = buildGitHubClients()) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return { exitCode: 0 };
  }
  const snapshot = await captureGitHubWorkState({
    repository: options.repository,
    issueNumber: options.issueNumber,
    pullRequestNumber: options.pullRequestNumber,
    expectedHead: options.expectedHead,
    generatedAt: options.generatedAt ?? new Date().toISOString(),
    pageSize: options.pageSize,
    ...clients,
  });
  const errors = validateSnapshotSemantics(snapshot);
  if (errors.length > 0) throw new Error(`snapshot validation failed: ${errors.join('; ')}`);
  const outputPath = writeSnapshot(options.outputPath, snapshot);
  process.stdout.write(
    `[github-work-state] captured ${snapshot.snapshotDigest} at ${outputPath}\n`
      + `[github-work-state] head=${snapshot.headSha} threads=${snapshot.reviewThreads.length} checks=${snapshot.requiredChecks.length}\n`,
  );
  return { exitCode: 0, snapshot, outputPath };
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  return Boolean(argvPath) && fileURLToPath(importMetaUrl) === path.resolve(argvPath);
}

if (isExecutedAsMain(import.meta.url)) {
  run().catch((error) => {
    process.stderr.write(`[github-work-state] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  });
}
