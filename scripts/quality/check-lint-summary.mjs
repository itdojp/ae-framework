#!/usr/bin/env node
/**
 * Quality gate helper for Verify Lite lint baseline comparison.
 *
 * Executes ESLint (JSON format), rebuilds the detailed summary used by
 * Verify Lite dashboards, persists it to `reports/lint/verify-lite-lint-summary.json`,
 * and compares the result with `config/verify-lite-lint-baseline.json`.
 *
 * The command prints "<n> error ..." / "<n> warning ..." lines so that
 * `QualityGateRunner` can interpret the outcome.
 */

import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { createHash } from 'node:crypto';

const SUMMARY_DEFAULT = 'reports/lint/verify-lite-lint-summary.json';
const BASELINE_DEFAULT = 'config/verify-lite-lint-baseline.json';
const SUMMARY_GENERATOR_VERSION = '0.3.0';
const TOP_RULE_LIMIT = 15;
const TOP_FILES_LIMIT = 10;
const FOCUS_RULES = [
  '@typescript-eslint/no-unused-vars',
  '@typescript-eslint/require-await',
  '@typescript-eslint/no-explicit-any',
  '@typescript-eslint/no-unsafe-assignment',
  '@typescript-eslint/no-unsafe-member-access',
  '@typescript-eslint/no-unsafe-argument',
  '@typescript-eslint/no-unsafe-return',
];

function parseArgs() {
  const args = process.argv.slice(2);
  let summaryPath = SUMMARY_DEFAULT;
  let baselinePath = BASELINE_DEFAULT;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === '--summary' && args[i + 1]) {
      summaryPath = args[++i];
    } else if (arg === '--baseline' && args[i + 1]) {
      baselinePath = args[++i];
    }
  }

  return {
    summaryPath: path.resolve(summaryPath),
    baselinePath: path.resolve(baselinePath),
  };
}

function runEslint() {
  const result = spawnSync('pnpm', ['exec', 'eslint', '.', '--format', 'json'], {
    encoding: 'utf8',
    maxBuffer: 1024 * 1024 * 150,
    stdio: ['ignore', 'pipe', 'pipe'],
  });

  if (result.error) {
    throw result.error;
  }

  const stdout = (result.stdout || '').trim();
  if (!stdout) {
    throw new Error('ESLint produced no JSON output');
  }

  return { data: JSON.parse(stdout), exitCode: result.status ?? 0 };
}

function readFileIfExists(filePath) {
  try {
    return fs.readFileSync(filePath, 'utf8');
  } catch {
    return null;
  }
}

function getEslintVersion() {
  const result = spawnSync('pnpm', ['exec', 'eslint', '--version'], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (result.error) {
    return 'unknown';
  }
  const version = (result.stdout || result.stderr || '').trim();
  return version || 'unknown';
}

function computeConfigHash() {
  const configPath = path.resolve('eslint.config.js');
  const content = readFileIfExists(configPath);
  if (!content) {
    return 'n/a';
  }
  return createHash('sha256').update(content).digest('hex').slice(0, 12);
}

function normalizePath(filePath) {
  if (!filePath) return 'unknown';
  const relative = path.relative(process.cwd(), filePath);
  return relative && !relative.startsWith('..') ? relative : filePath;
}

function incrementMap(map, key, delta = 1) {
  map.set(key, (map.get(key) ?? 0) + delta);
}

function sortedEntries(map, limit = Infinity) {
  return Array.from(map.entries())
    .sort((a, b) => b[1] - a[1])
    .slice(0, limit)
    .map(([key, value]) => ({ key, value }));
}

function buildSummary(eslintJson, options) {
  const {
    eslintVersion,
    configHash,
  } = options;

  const ruleCounts = new Map();
  const ruleFileCounts = new Map();
  const fixableByRule = new Map();
  const fixableByFile = new Map();
  let totalIssues = 0;

  for (const fileEntry of eslintJson) {
    const filePath = normalizePath(fileEntry.filePath);
    const messages = fileEntry.messages ?? [];

    for (const message of messages) {
      totalIssues += 1;
      const rule = message.ruleId ?? 'unknown';

      incrementMap(ruleCounts, rule);

      let fileMap = ruleFileCounts.get(rule);
      if (!fileMap) {
        fileMap = new Map();
        ruleFileCounts.set(rule, fileMap);
      }
      incrementMap(fileMap, filePath);

      if (message.fix) {
        incrementMap(fixableByRule, rule);
        incrementMap(fixableByFile, filePath);
      }
    }
  }

  const rulesArray = Array.from(ruleCounts.entries())
    .sort((a, b) => b[1] - a[1])
    .map(([rule, count]) => ({ rule, count }));

  const clusters = {
    unsafe: rulesArray
      .filter(entry => entry.rule.startsWith('@typescript-eslint/no-unsafe'))
      .reduce((sum, entry) => sum + entry.count, 0),
    explicitAny: ruleCounts.get('@typescript-eslint/no-explicit-any') ?? 0,
    unusedVars: ruleCounts.get('@typescript-eslint/no-unused-vars') ?? 0,
    requireAwait: ruleCounts.get('@typescript-eslint/require-await') ?? 0,
  };

  const topRules = rulesArray.slice(0, TOP_RULE_LIMIT);

  const focusRules = FOCUS_RULES
    .filter(rule => (ruleCounts.get(rule) ?? 0) > 0)
    .map(rule => {
      const total = ruleCounts.get(rule) ?? 0;
      const fileMap = ruleFileCounts.get(rule) ?? new Map();
      const topFiles = Array.from(fileMap.entries())
        .sort((a, b) => b[1] - a[1])
        .slice(0, TOP_FILES_LIMIT)
        .map(([file, count]) => ({ file, count }));
      return { rule, total, topFiles };
    });

  const fixable = {
    byRule: sortedEntries(fixableByRule, TOP_RULE_LIMIT).map(({ key, value }) => ({
      rule: key,
      count: value,
    })),
    byFile: sortedEntries(fixableByFile, TOP_RULE_LIMIT).map(({ key, value }) => ({
      file: key,
      count: value,
    })),
  };

  return {
    schemaVersion: '1.0.0',
    generator: {
      name: 'verify-lite-lint-summary',
      version: SUMMARY_GENERATOR_VERSION,
      eslintVersion,
      configHash,
    },
    generatedAt: new Date().toISOString(),
    totals: {
      totalIssues,
      fixableIssues: fixableByRule.size === 0
        ? 0
        : Array.from(fixableByRule.values()).reduce((sum, count) => sum + count, 0),
    },
    clusters,
    topRules,
    focusRules,
    fixable,
    rules: rulesArray,
  };
}

function saveSummary(summaryPath, summary) {
  fs.mkdirSync(path.dirname(summaryPath), { recursive: true });
  fs.writeFileSync(summaryPath, JSON.stringify(summary, null, 2));
}

function loadBaseline(baselinePath) {
  if (!fs.existsSync(baselinePath)) {
    throw new Error(`Baseline not found: ${baselinePath}`);
  }

  return JSON.parse(fs.readFileSync(baselinePath, 'utf8'));
}

function computeDelta(summary, baseline) {
  const baselineRules = baseline.rules ?? {};
  const summaryRuleMap = new Map((summary.rules ?? []).map(entry => [entry.rule, entry.count]));

  const totalActual = summary.totals?.totalIssues ?? 0;
  const totalBaseline = baseline.total ?? baseline.totals?.totalIssues ?? 0;
  const totalDelta = Math.max(0, totalActual - totalBaseline);

  let ruleDelta = 0;
  const details = [];

  const allRules = new Set([
    ...Object.keys(baselineRules),
    ...summaryRuleMap.keys(),
  ]);

  for (const rule of allRules) {
    const baselineCount = baselineRules[rule] ?? 0;
    const actual = summaryRuleMap.get(rule) ?? 0;
    const delta = actual - baselineCount;
    if (delta > 0) {
      ruleDelta += delta;
      details.push({ rule, actual, baseline: baselineCount, delta });
    }
  }

  details.sort((a, b) => b.delta - a.delta);
  return { totalDelta, totalBaseline, ruleDelta, details, totalActual };
}

function main() {
  try {
    const { summaryPath, baselinePath } = parseArgs();

    console.log('ℹ️  Running ESLint in JSON mode to capture Verify Lite summary...');
    const { data, exitCode } = runEslint();
    const eslintVersion = getEslintVersion();
    const configHash = computeConfigHash();
    const summary = buildSummary(data, { eslintVersion, configHash });
    saveSummary(summaryPath, summary);

    if (exitCode !== 0) {
      console.warn('⚠️  ESLint reported issues (non-zero exit). Baseline comparison will still proceed.');
    }

    const baseline = loadBaseline(baselinePath);
    const { totalDelta, totalBaseline, ruleDelta, details, totalActual } = computeDelta(summary, baseline);

    console.log(`${totalDelta} error lint-delta (actual ${totalActual}, baseline ${totalBaseline})`);
    console.log(`${ruleDelta} warning rule-delta above baseline`);

    if (details.length > 0) {
      console.log('⚠️  Lint regressions detected (rule → +delta):');
      for (const detail of details.slice(0, 10)) {
        console.log(`   - ${detail.rule}: +${detail.delta} (actual ${detail.actual}, baseline ${detail.baseline})`);
      }
      if (details.length > 10) {
        console.log(`   … ${details.length - 10} more rules exceeded the baseline`);
      }
    } else {
      console.log('✅ No lint regressions over baseline');
    }

    const hasRegression = totalDelta > 0 || ruleDelta > 0;
    const exitStatus = exitCode !== 0 ? exitCode : (hasRegression ? 1 : 0);

    if (exitStatus !== 0) {
      console.error('❌ Lint quality gate failed: regressions detected or ESLint exited with errors.');
    }

    process.exit(exitStatus);
  } catch (error) {
    console.error('❌ Failed to check lint baseline:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}

main();
