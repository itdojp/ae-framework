import { chmodSync, mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import os from 'node:os';
import path, { delimiter, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, expect, it } from 'vitest';

const scriptPath = resolve('scripts/ci/codex-autopilot-lane.mjs');

function writeFakeGh(binDir: string, stateFile: string) {
  const ghPath = path.join(binDir, 'gh');
  const script = `#!/usr/bin/env node
const fs = require('node:fs');

function readState() {
  try {
    return JSON.parse(fs.readFileSync(process.env.FAKE_GH_STATE_FILE, 'utf8'));
  } catch {
    return { stateQueryCount: 0 };
  }
}

function writeState(next) {
  fs.writeFileSync(process.env.FAKE_GH_STATE_FILE, JSON.stringify(next));
}

function printJson(value) {
  process.stdout.write(JSON.stringify(value));
}

const args = process.argv.slice(2);
if (args[0] === 'pr' && args[1] === 'view') {
  printJson({
    number: 123,
    title: 'Test PR',
    url: 'https://example.invalid/pr/123',
    state: 'OPEN',
    isDraft: false,
    mergeable: 'MERGEABLE',
    mergeStateStatus: 'CLEAN',
    headRefName: 'feat/test',
    headRefOid: 'deadbeef',
    autoMergeRequest: null,
    labels: [{ name: 'autopilot:on' }],
    statusCheckRollup: [
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-03-03T00:00:00Z'
      }
    ]
  });
  process.exit(0);
}

if (args[0] === 'api' && typeof args[1] === 'string' && args[1].includes('/pulls/123/files')) {
  printJson([{ filename: 'docs/README.md' }]);
  process.exit(0);
}

if (args[0] === 'api' && args[1] === 'graphql') {
  const queryArg = args.find((arg) => typeof arg === 'string' && arg.startsWith('query=')) || '';
  const query = String(queryArg).slice('query='.length);
  if (query.includes('reviewThreads(first:100') && query.includes('bodyText')) {
    printJson({
      data: {
        repository: {
          pullRequest: {
            reviewThreads: {
              pageInfo: { hasNextPage: false, endCursor: null },
              nodes: [
                {
                  id: 'RT_1',
                  path: 'src/a.ts',
                  isResolved: false,
                  comments: {
                    pageInfo: { hasNextPage: false, endCursor: null },
                    nodes: [
                      {
                        databaseId: 101,
                        bodyText: 'Please rename this helper for clarity.',
                        path: 'src/a.ts',
                        line: 12,
                        startLine: 12,
                        url: 'https://example.invalid/101',
                        createdAt: '2026-03-03T00:00:00Z',
                        author: { login: 'github-copilot[bot]', __typename: 'Bot' }
                      }
                    ]
                  }
                }
              ]
            }
          }
        }
      }
    });
    process.exit(0);
  }

  if (query.includes('reviewThreads(first:100')) {
    const state = readState();
    state.stateQueryCount = (state.stateQueryCount || 0) + 1;
    writeState(state);
    const unresolved = state.stateQueryCount === 1;
    printJson({
      data: {
        repository: {
          pullRequest: {
            reviewThreads: {
              pageInfo: { hasNextPage: false, endCursor: null },
              nodes: unresolved
                ? [
                    {
                      id: 'RT_1',
                      isResolved: false,
                      comments: {
                        pageInfo: { hasNextPage: false, endCursor: null },
                        nodes: [
                          {
                            author: { login: 'github-copilot[bot]', __typename: 'Bot' }
                          }
                        ]
                      }
                    }
                  ]
                : []
            }
          }
        }
      }
    });
    process.exit(0);
  }

  if (query.includes('node(id:$threadId)')) {
    printJson({
      data: {
        node: {
          comments: {
            pageInfo: { hasNextPage: false, endCursor: null },
            nodes: []
          }
        }
      }
    });
    process.exit(0);
  }
}

process.stderr.write('unexpected gh args: ' + JSON.stringify(args) + '\\n');
process.exit(2);
`;

  writeFileSync(ghPath, script, 'utf8');
  chmodSync(ghPath, 0o755);
  writeFileSync(path.join(binDir, 'gh.cmd'), '@echo off\\r\\nnode "%~dp0gh" %*\\r\\n', 'utf8');
  writeFileSync(stateFile, JSON.stringify({ stateQueryCount: 0 }), 'utf8');
}

describe('codex-autopilot-lane pseudo e2e (actionable execution)', () => {
  it('executes actionable task command and reports deterministic result', () => {
    const tempDir = mkdtempSync(path.join(os.tmpdir(), 'codex-autopilot-e2e-'));
    const binDir = path.join(tempDir, 'bin');
    mkdirSync(binDir, { recursive: true });
    const stateFile = path.join(tempDir, 'gh-state.json');
    writeFakeGh(binDir, stateFile);

    const actionableCommand = [
      'node -e',
      `"const fs=require('node:fs');`,
      `const payload=JSON.parse(fs.readFileSync(process.env.AE_ACTIONABLE_TASKS_JSON,'utf8'));`,
      `const results=(payload.tasks||[]).map((task)=>({commentId:task.commentId,status:'success'}));`,
      `process.stdout.write(JSON.stringify({results}));"`,
    ].join(' ');

    const result = spawnSync('node', [scriptPath], {
      cwd: resolve('.'),
      encoding: 'utf8',
      env: {
        ...process.env,
        PATH: `${binDir}${delimiter}${process.env.PATH || ''}`,
        GITHUB_REPOSITORY: 'itdojp/ae-framework',
        PR_NUMBER: '123',
        AE_AUTOPILOT_DRY_RUN: '1',
        AE_AUTOPILOT_ACTIONABLE_DRY_RUN: '0',
        AE_AUTOPILOT_ACTIONABLE_COMMAND: actionableCommand,
        AE_AUTOPILOT_MAX_ROUNDS: '1',
        AE_AUTOPILOT_ROUND_WAIT_SECONDS: '0',
        AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS: '0',
        AE_GH_THROTTLE_MS: '0',
        AE_GH_RETRY_MAX_ATTEMPTS: '1',
        AE_GH_RETRY_NO_SLEEP: '1',
        AI_REVIEW_ACTORS: 'github-copilot[bot]',
        FAKE_GH_STATE_FILE: stateFile,
      },
    });

    try {
      expect(result.status).toBe(0);
      expect(result.stdout).toContain('execution-result=success');
      const reportLine = String(result.stdout || '')
        .split('\n')
        .find((line) => line.startsWith('[ae-automation-report] '));
      expect(reportLine).toBeTruthy();
      const report = JSON.parse(String(reportLine).replace(/^\[ae-automation-report\] /, ''));
      expect(report.status).toBe('resolved');
      expect(report.metrics.actionableAttempted).toBe(1);
      expect(report.metrics.actionableSucceeded).toBe(1);
      expect(report.metrics.actionableFailed).toBe(0);
      expect(report.data.executionResult).toBe('success');
      expect(report.data.actionableExecutionStatus).toBe('success');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
