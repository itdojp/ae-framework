#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';

const AUDIT_STEPS = [
  {
    key: 'scope',
    script: 'scripts/legal/inventory-license-scope.mjs',
    outputs: ['license-scope-audit.json', 'license-scope-audit.md'],
    extraArgs: [],
  },
  {
    key: 'conditional',
    script: 'scripts/legal/inventory-conditional-assets.mjs',
    outputs: ['conditional-asset-audit.json', 'conditional-asset-audit.md'],
    extraArgs: [],
  },
  {
    key: 'notice',
    script: 'scripts/legal/build-notice-readiness.mjs',
    outputs: ['notice-readiness-audit.json', 'notice-readiness-audit.md'],
    extraArgs: ({ outputsByKey, rootDir }) => [
      '--scope-audit',
      relativePosix(rootDir, outputsByKey.scope.json),
      '--conditional-audit',
      relativePosix(rootDir, outputsByKey.conditional.json),
    ],
  },
  {
    key: 'contributors',
    script: 'scripts/legal/build-contributor-license-readiness.mjs',
    outputs: ['contributor-license-readiness-audit.json', 'contributor-license-readiness-audit.md'],
    extraArgs: ({ outputsByKey, rootDir }) => [
      '--scope-audit',
      relativePosix(rootDir, outputsByKey.scope.json),
    ],
  },
  {
    key: 'third-party',
    script: 'scripts/legal/build-third-party-notice-candidate-audit.mjs',
    outputs: ['third-party-notice-candidate-audit.json', 'third-party-notice-candidate-audit.md'],
    extraArgs: [],
  },
  {
    key: 'cutover',
    script: 'scripts/legal/build-apache-license-cutover-readiness.mjs',
    outputs: ['apache-license-cutover-readiness-audit.json', 'apache-license-cutover-readiness-audit.md'],
    extraArgs: ({ outputsByKey, rootDir }) => [
      '--scope-audit',
      relativePosix(rootDir, outputsByKey.scope.json),
      '--conditional-audit',
      relativePosix(rootDir, outputsByKey.conditional.json),
      '--notice-readiness-audit',
      relativePosix(rootDir, outputsByKey.notice.json),
      '--contributor-readiness-audit',
      relativePosix(rootDir, outputsByKey.contributors.json),
    ],
  },
];

function relativePosix(rootDir, targetPath) {
  return path.relative(rootDir, targetPath).replace(/\\/g, '/');
}

export function buildLicenseAuditSuitePlan({
  rootDir,
  outputDir = path.join(rootDir, 'artifacts/reference/legal'),
}) {
  const outputsByKey = Object.fromEntries(
    AUDIT_STEPS.map((step) => [
      step.key,
      {
        json: path.join(outputDir, step.outputs[0]),
        md: path.join(outputDir, step.outputs[1]),
      },
    ]),
  );

  return AUDIT_STEPS.map((step) => {
    const jsonPath = outputsByKey[step.key].json;
    const mdPath = outputsByKey[step.key].md;
    const extraArgs = typeof step.extraArgs === 'function'
      ? step.extraArgs({ outputsByKey, rootDir })
      : step.extraArgs;
    return {
      key: step.key,
      script: step.script,
      args: [
        step.script,
        '--root',
        rootDir,
        ...extraArgs,
        '--output-json',
        relativePosix(rootDir, jsonPath),
        '--output-md',
        relativePosix(rootDir, mdPath),
      ],
      outputs: {
        json: jsonPath,
        md: mdPath,
      },
    };
  });
}

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    outputDir: null,
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --root');
      options.root = next;
      index += 1;
      continue;
    }
    if (arg === '--output-dir') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --output-dir');
      options.outputDir = next;
      index += 1;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`Run all legal audits from a single repository HEAD

Usage:
  node scripts/legal/run-license-audit-suite.mjs [options]

Options:
  --root <path>         Repository root (default: current working directory)
  --output-dir <path>   Output directory (default: artifacts/reference/legal)
  --help, -h            Show this help
`);
}

export function runLicenseAuditSuite({
  rootDir,
  outputDir,
  env = process.env,
  spawnSyncImpl = spawnSync,
}) {
  const resolvedOutputDir = outputDir ?? path.join(rootDir, 'artifacts/reference/legal');
  const plan = buildLicenseAuditSuitePlan({ rootDir, outputDir: resolvedOutputDir });
  fs.mkdirSync(resolvedOutputDir, { recursive: true });

  for (const step of plan) {
    const result = spawnSyncImpl(process.execPath, step.args, {
      cwd: rootDir,
      env,
      encoding: 'utf8',
    });
    if (result.status !== 0) {
      const stderr = String(result.stderr || '').trim();
      const stdout = String(result.stdout || '').trim();
      const cause = result.error instanceof Error ? result.error.message : '';
      throw new Error(
        `legal audit step failed (${step.key})${stderr ? `: ${stderr}` : stdout ? `: ${stdout}` : cause ? `: ${cause}` : ''}`,
      );
    }
  }

  return {
    rootDir,
    outputDir: resolvedOutputDir,
    sourceDateEpoch: env.SOURCE_DATE_EPOCH ?? null,
    steps: plan.map((step) => ({
      key: step.key,
      script: step.script,
      outputs: {
        json: relativePosix(rootDir, step.outputs.json),
        md: relativePosix(rootDir, step.outputs.md),
      },
    })),
  };
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const rootDir = path.resolve(options.root);
  const outputDir = options.outputDir
    ? path.resolve(rootDir, options.outputDir)
    : path.join(rootDir, 'artifacts/reference/legal');

  const summary = runLicenseAuditSuite({
    rootDir,
    outputDir,
  });
  process.stdout.write(`${JSON.stringify(summary, null, 2)}\n`);
  return 0;
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath) return false;
  return importMetaUrl === pathToFileURL(path.resolve(argvPath)).href;
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    process.exit(run(process.argv));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[license-audit-suite] ${message}\n`);
    process.exit(1);
  }
}
