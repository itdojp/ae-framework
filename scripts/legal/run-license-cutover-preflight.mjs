#!/usr/bin/env node

import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { runLicenseAuditSuite } from './run-license-audit-suite.mjs';

const DEFAULT_APPROVAL_RECORD = 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md';
const APPROVAL_SCRIPT = 'scripts/legal/build-apache-license-cutover-approval-readiness.mjs';

function relativePosix(rootDir, targetPath) {
  const relative = path.relative(rootDir, targetPath).replace(/\\/g, '/');
  return relative.length > 0 ? relative : '.';
}

export function buildLicenseCutoverPreflightPlan({
  rootDir,
  outputDir = path.join(rootDir, 'artifacts/reference/legal'),
  approvalRecord = DEFAULT_APPROVAL_RECORD,
}) {
  const approvalRecordPath = path.resolve(rootDir, approvalRecord);
  const cutoverReadinessAuditPath = path.join(outputDir, 'apache-license-cutover-readiness-audit.json');
  const approvalAuditJsonPath = path.join(outputDir, 'apache-license-cutover-approval-readiness-audit.json');
  const approvalAuditMdPath = path.join(outputDir, 'apache-license-cutover-approval-readiness-audit.md');

  return {
    rootDir,
    outputDir,
    approvalRecordPath,
    approval: {
      script: APPROVAL_SCRIPT,
      args: [
        APPROVAL_SCRIPT,
        '--root',
        rootDir,
        '--approval-record',
        relativePosix(rootDir, approvalRecordPath),
        '--cutover-readiness-audit',
        relativePosix(rootDir, cutoverReadinessAuditPath),
        '--output-json',
        relativePosix(rootDir, approvalAuditJsonPath),
        '--output-md',
        relativePosix(rootDir, approvalAuditMdPath),
      ],
      inputs: {
        approvalRecordPath,
        cutoverReadinessAuditPath,
      },
      outputs: {
        json: approvalAuditJsonPath,
        md: approvalAuditMdPath,
      },
    },
  };
}

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    outputDir: null,
    approvalRecord: DEFAULT_APPROVAL_RECORD,
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
    if (arg === '--approval-record') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --approval-record');
      options.approvalRecord = next;
      index += 1;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`Run legal audit preflight for the Apache-2.0 cutover\n\nUsage:\n  node scripts/legal/run-license-cutover-preflight.mjs [options]\n\nOptions:\n  --root <path>             Repository root (default: current working directory)\n  --output-dir <path>       Output directory (default: artifacts/reference/legal)\n  --approval-record <path>  Approval record path (default: docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md)\n  --help, -h                Show this help\n`);
}

export function runLicenseCutoverPreflight({
  rootDir,
  outputDir,
  approvalRecord,
  env = process.env,
  spawnSyncImpl = spawnSync,
  runLicenseAuditSuiteImpl = runLicenseAuditSuite,
}) {
  const plan = buildLicenseCutoverPreflightPlan({
    rootDir,
    outputDir,
    approvalRecord,
  });

  const suiteSummary = runLicenseAuditSuiteImpl({
    rootDir: plan.rootDir,
    outputDir: plan.outputDir,
    env,
    spawnSyncImpl,
  });

  const approvalResult = spawnSyncImpl(process.execPath, plan.approval.args, {
    cwd: plan.rootDir,
    env,
    encoding: 'utf8',
  });
  if (approvalResult.status !== 0) {
    const stderr = String(approvalResult.stderr || '').trim();
    const stdout = String(approvalResult.stdout || '').trim();
    throw new Error(
      `license cutover preflight failed (approval)${stderr ? `: ${stderr}` : stdout ? `: ${stdout}` : ''}`,
    );
  }

  return {
    rootDir: plan.rootDir,
    outputDir: plan.outputDir,
    sourceDateEpoch: env.SOURCE_DATE_EPOCH ?? null,
    approvalRecordPath: relativePosix(plan.rootDir, plan.approval.inputs.approvalRecordPath),
    suite: suiteSummary,
    approval: {
      script: plan.approval.script,
      inputs: {
        approvalRecordPath: relativePosix(plan.rootDir, plan.approval.inputs.approvalRecordPath),
        cutoverReadinessAuditPath: relativePosix(plan.rootDir, plan.approval.inputs.cutoverReadinessAuditPath),
      },
      outputs: {
        json: relativePosix(plan.rootDir, plan.approval.outputs.json),
        md: relativePosix(plan.rootDir, plan.approval.outputs.md),
      },
    },
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

  const summary = runLicenseCutoverPreflight({
    rootDir,
    outputDir,
    approvalRecord: options.approvalRecord,
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
    process.stderr.write(`[license-cutover-preflight] ${message}\n`);
    process.exit(1);
  }
}
