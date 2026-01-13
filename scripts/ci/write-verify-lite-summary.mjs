#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const summaryPathFromArg = process.argv[2];
const summaryPath = summaryPathFromArg ?? process.env.VERIFY_LITE_SUMMARY_FILE ?? 'verify-lite-run-summary.json';
const resolvedPath = path.resolve(summaryPath);

const bool = (value) => value === '1' || value === true || value === 'true';
const existsOrNull = (p) => (p && fs.existsSync(p) ? p : null);

const readStatus = (name, fallback) => {
  const value = process.env[name];
  return value ?? fallback;
};

const SCHEMA_VERSION = process.env.VERIFY_LITE_SUMMARY_SCHEMA_VERSION ?? '1.0.0';

const summary = {
  schemaVersion: SCHEMA_VERSION,
  timestamp: process.env.RUN_TIMESTAMP || new Date().toISOString(),
  flags: {
    install: process.env.INSTALL_FLAGS_STR || '',
    noFrozen: bool(process.env.VERIFY_LITE_NO_FROZEN || '0'),
    keepLintLog: bool(process.env.VERIFY_LITE_KEEP_LINT_LOG || '0'),
    enforceLint: bool(process.env.VERIFY_LITE_ENFORCE_LINT || '0'),
    runMutation: bool(process.env.VERIFY_LITE_RUN_MUTATION || '0'),
  },
  steps: {
    install: {
      status: readStatus('INSTALL_STATUS', 'unknown'),
      notes: process.env.INSTALL_NOTES || null,
      retried: readStatus('INSTALL_RETRIED', '0') === '1',
    },
    specCompilerBuild: { status: readStatus('SPEC_COMPILER_STATUS', 'skipped') },
    typeCheck: { status: readStatus('TYPECHECK_STATUS', 'unknown') },
    lint: { status: readStatus('LINT_STATUS', 'unknown') },
    build: { status: readStatus('BUILD_STATUS', 'unknown') },
    stateMachineValidation: { status: readStatus('STATE_MACHINE_STATUS', 'unknown') },
    bddLint: { status: readStatus('BDD_LINT_STATUS', 'skipped') },
    mutationQuick: {
      status: readStatus('MUTATION_STATUS', 'skipped'),
      notes: process.env.MUTATION_NOTES || null,
    },
    conformanceReport: {
      status: readStatus('CONFORMANCE_STATUS', 'skipped'),
      notes: process.env.CONFORMANCE_NOTES || null,
    },
  },
  artifacts: {
    lintSummary: existsOrNull(process.env.LINT_SUMMARY_PATH),
    lintLog: existsOrNull(process.env.LINT_LOG_EXPORT),
    mutationSummary: existsOrNull(process.env.MUTATION_SUMMARY_PATH),
    mutationSurvivors: existsOrNull(process.env.MUTATION_SURVIVORS_PATH),
    conformanceSummary: existsOrNull(process.env.CONFORMANCE_SUMMARY_PATH),
    conformanceSummaryMarkdown: existsOrNull(process.env.CONFORMANCE_SUMMARY_MARKDOWN_PATH),
  },
};

try {
  fs.writeFileSync(resolvedPath, JSON.stringify(summary, null, 2));
  console.log(`[verify-lite] summary written to ${resolvedPath}`);
} catch (error) {
  console.error('[verify-lite] failed to write summary', error);
  process.exit(1);
}
