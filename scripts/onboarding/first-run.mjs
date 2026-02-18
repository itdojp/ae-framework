#!/usr/bin/env node

import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const SUMMARY_SCHEMA_VERSION = 'first-run-summary/v1';

export const EXIT_CODES = {
  SUCCESS: 0,
  FAILED: 1,
  INVALID_ARGUMENT: 3,
  INTERNAL_ERROR: 4,
};

const STEP_PLAN = [
  {
    id: 'doctor',
    label: 'doctor:env',
    command: 'pnpm run doctor:env',
    required: true,
    allowedExitCodes: [0, 2],
  },
  {
    id: 'build',
    label: 'build',
    command: 'pnpm run build',
    required: true,
  },
  {
    id: 'verifyLite',
    label: 'verify:lite',
    command: 'pnpm run verify:lite',
    required: true,
  },
];

export function shellEscape(value) {
  return `'${String(value).replace(/'/g, '\'\\\'\'')}'`;
}

export function parseArgs(argv = process.argv) {
  const options = {
    outputDir: 'artifacts/first-run',
    json: false,
    help: false,
    unknown: [],
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--json') {
      options.json = true;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg.startsWith('--output-dir=')) {
      const value = arg.slice('--output-dir='.length);
      if (value) {
        options.outputDir = value;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg === '--output-dir') {
      if (next && !next.startsWith('-')) {
        options.outputDir = next;
        index += 1;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    options.unknown.push(arg);
  }

  return options;
}

function defaultExecuteStep(step, context) {
  const logPath = path.join(context.outputDir, 'logs', `${step.id}.log`);
  mkdirSync(path.dirname(logPath), { recursive: true });

  const commandText = `set -o pipefail; ${step.command} 2>&1 | tee ${shellEscape(logPath)}`;
  const started = Date.now();
  const result = spawnSync('bash', ['-lc', commandText], {
    cwd: context.cwd,
    env: context.env,
    stdio: 'inherit',
  });
  const durationMs = Date.now() - started;

  let exitCode = result.status ?? 1;
  if (result.error?.code === 'ENOENT') {
    exitCode = 127;
  }

  return {
    id: step.id,
    label: step.label,
    command: step.command,
    required: step.required,
    status: exitCode === 0 ? 'passed' : 'failed',
    exitCode,
    durationMs,
    logPath,
    error: result.error ? String(result.error.message ?? result.error) : null,
  };
}

function suggestNextActions(failedStepId) {
  if (failedStepId === 'doctor') {
    return [
      'artifacts/doctor/env.json の error/warn を確認し、Node.js・pnpm を修正してください。',
      '修正後に pnpm run first-run を再実行してください。',
    ];
  }
  if (failedStepId === 'build') {
    return [
      'artifacts/first-run/logs/build.log を確認し、ビルドエラーを修正してください。',
      '必要に応じて pnpm run doctor:env で環境再確認後、pnpm run first-run を再実行してください。',
    ];
  }
  if (failedStepId === 'verifyLite') {
    return [
      'artifacts/first-run/logs/verifyLite.log と artifacts/verify-lite/verify-lite-run-summary.json を確認してください。',
      'lint/type/build 失敗箇所を修正後、pnpm run first-run を再実行してください。',
    ];
  }
  if (!failedStepId) {
    return [
      'pnpm run setup-hooks で Git hooks を有効化してください。',
      'docs/integrations/QUICK-START-CODEX.md を参照し、必要に応じて pnpm run codex:quickstart を実行してください。',
      'PR作業前に pnpm run verify:lite を再実行し、最新状態を確認してください。',
    ];
  }
  return [
    'pnpm run first-run を再実行して、失敗ステップのログを確認してください。',
  ];
}

function normalizeArtifactPath(pathValue, rootDir) {
  if (!pathValue) {
    return '';
  }
  return path.relative(rootDir, path.resolve(rootDir, pathValue));
}

function renderMarkdownSummary(summary) {
  const lines = [];
  lines.push('# First Run Summary');
  lines.push('');
  lines.push(`- schemaVersion: ${summary.schemaVersion}`);
  lines.push(`- generatedAt: ${summary.generatedAt}`);
  lines.push(`- status: ${summary.status}`);
  lines.push(`- exitCode: ${summary.exitCode}`);
  lines.push('');
  lines.push('## Steps');
  lines.push('| Step | Status | Exit Code | Duration(ms) | Log |');
  lines.push('| --- | --- | --- | ---: | --- |');
  for (const step of summary.steps) {
    lines.push(`| ${step.label} | ${step.status} | ${step.exitCode} | ${step.durationMs} | \`${path.relative(summary.rootDir, step.logPath)}\` |`);
  }

  lines.push('');
  lines.push('## Key Artifacts');
  for (const artifact of summary.keyArtifacts) {
    const status = existsSync(path.resolve(summary.rootDir, artifact.path)) ? 'present' : 'missing';
    lines.push(`- ${artifact.label}: \`${artifact.path}\` (${status})`);
  }

  lines.push('');
  lines.push('## Next Actions');
  for (const action of summary.nextActions) {
    lines.push(`- ${action}`);
  }

  lines.push('');
  lines.push('## Next References');
  lines.push('- docs/integrations/QUICK-START-CODEX.md');
  lines.push('- docs/ci/label-gating.md');
  lines.push('- docs/product/USER-MANUAL.md');

  return `${lines.join('\n')}\n`;
}

function writeSummary(summary, outputDir, cwd = process.cwd()) {
  const outputAbsDir = path.resolve(cwd, outputDir);
  mkdirSync(outputAbsDir, { recursive: true });
  const jsonPath = path.join(outputAbsDir, 'summary.json');
  const markdownPath = path.join(outputAbsDir, 'summary.md');
  writeFileSync(jsonPath, JSON.stringify(summary, null, 2));
  writeFileSync(markdownPath, renderMarkdownSummary(summary));
  return { outputDir: outputAbsDir, jsonPath, markdownPath };
}

export function runFirstRun(options, deps = {}) {
  const cwd = deps.cwd ?? process.cwd();
  const env = deps.env ?? process.env;
  const executeStep = deps.executeStep ?? defaultExecuteStep;
  const nowIso = deps.nowIso ?? (() => new Date().toISOString());
  const writeSummaryFn = deps.writeSummary ?? writeSummary;
  const outputDir = path.resolve(cwd, options.outputDir);

  const steps = [];
  let failedStepId = null;
  for (const step of STEP_PLAN) {
    const rawResult = executeStep(step, { cwd, env, outputDir });
    const allowedExitCodes = step.allowedExitCodes ?? [0];
    const stepSucceeded = allowedExitCodes.includes(rawResult.exitCode);
    const status = rawResult.exitCode === 0 ? 'passed' : (stepSucceeded ? 'warn' : 'failed');
    const result = { ...rawResult, status };
    steps.push(result);
    if (!stepSucceeded && step.required) {
      failedStepId = step.id;
      break;
    }
  }

  const exitCode = failedStepId ? EXIT_CODES.FAILED : EXIT_CODES.SUCCESS;
  const summary = {
    schemaVersion: SUMMARY_SCHEMA_VERSION,
    generatedAt: nowIso(),
    rootDir: cwd,
    status: exitCode === 0 ? 'success' : 'failure',
    exitCode,
    steps,
    keyArtifacts: [
      { label: 'doctor report', path: 'artifacts/doctor/env.json' },
      { label: 'verify-lite summary', path: 'artifacts/verify-lite/verify-lite-run-summary.json' },
      { label: 'first-run summary', path: normalizeArtifactPath(path.join(options.outputDir, 'summary.json'), cwd) },
    ],
    nextActions: suggestNextActions(failedStepId),
  };

  try {
    const output = writeSummaryFn(summary, options.outputDir, cwd);
    summary.outputs = output;
  } catch (error) {
    if (options.json) {
      process.stdout.write(`${JSON.stringify(summary, null, 2)}\n`);
    }
    process.stderr.write(`[first-run] failed to write summary: ${String(error instanceof Error ? error.message : error)}\n`);
    return EXIT_CODES.INTERNAL_ERROR;
  }

  if (options.json) {
    process.stdout.write(`${JSON.stringify(summary, null, 2)}\n`);
  } else {
    process.stdout.write(`[first-run] summary: ${summary.outputs.jsonPath}\n`);
  }

  return exitCode;
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/onboarding/first-run.mjs [options]

Options:
  --output-dir <dir>   Summary output directory (default: artifacts/first-run)
  --json               Print summary JSON to stdout
  -h, --help           Show this help
`);
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return EXIT_CODES.SUCCESS;
  }
  if (options.unknown.length > 0) {
    process.stderr.write(`[first-run] unknown argument(s): ${options.unknown.join(', ')}\n`);
    printHelp();
    return EXIT_CODES.INVALID_ARGUMENT;
  }
  return runFirstRun(options);
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath || typeof argvPath !== 'string') {
    return false;
  }
  try {
    const modulePath = path.resolve(fileURLToPath(importMetaUrl));
    const entryPath = path.resolve(argvPath);
    return modulePath === entryPath;
  } catch {
    return false;
  }
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  process.exitCode = main(process.argv);
}
