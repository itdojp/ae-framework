#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const SUMMARY_SCHEMA_VERSION = 'bootstrap-local-summary/v1';

export const EXIT_CODES = {
  SUCCESS: 0,
  PREREQUISITE_FAILED: 2,
  COMMAND_FAILED: 3,
  INTERNAL_ERROR: 4,
};

export function isExecutedAsMain(importMetaUrl, argvPath) {
  const modulePath = fileURLToPath(importMetaUrl);
  return path.resolve(modulePath) === path.resolve(argvPath);
}

export function parseArgs(argv) {
  const options = {
    skipSetupHooks: false,
    skipVerifyLite: false,
    withCodex: false,
    skipCodex: false,
    json: false,
    outputDir: 'artifacts/bootstrap',
    help: false,
    unknown: [],
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if (arg === '--skip-setup-hooks') {
      options.skipSetupHooks = true;
    } else if (arg === '--skip-verify-lite') {
      options.skipVerifyLite = true;
    } else if (arg === '--with-codex') {
      options.withCodex = true;
    } else if (arg === '--skip-codex') {
      options.skipCodex = true;
    } else if (arg === '--json') {
      options.json = true;
    } else if (arg === '--help' || arg === '-h') {
      options.help = true;
    } else if (arg.startsWith('--output-dir=')) {
      const value = arg.slice('--output-dir='.length);
      if (value) {
        options.outputDir = value;
      } else {
        options.unknown.push(arg);
      }
    } else if (arg === '--output-dir') {
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        options.outputDir = next;
        i += 1;
      }
    } else {
      options.unknown.push(arg);
    }
  }

  return options;
}

export function isSupportedNodeVersion(version = process.version) {
  const match = /^v?(\d+)\.(\d+)\.(\d+)/.exec(version);
  if (!match) {
    return false;
  }
  const major = Number(match[1]);
  const minor = Number(match[2]);

  if (major < 20 || major >= 23) {
    return false;
  }
  if (major === 20 && minor < 11) {
    return false;
  }
  return true;
}

function checkPnpmAvailable(spawn = spawnSync) {
  const result = spawn('pnpm', ['--version'], {
    stdio: 'pipe',
    encoding: 'utf8',
  });
  if (result.error) {
    return false;
  }
  return (result.status ?? 1) === 0;
}

export function checkPrerequisites({
  nodeVersion = process.version,
  spawn = spawnSync,
} = {}) {
  const issues = [];
  if (!isSupportedNodeVersion(nodeVersion)) {
    issues.push({
      code: 'node_version_unsupported',
      message: `Node.js ${nodeVersion} is unsupported. Expected >=20.11 <23.`,
      fix: 'Use Node.js 20.11+ (<23).',
    });
  }

  if (!checkPnpmAvailable(spawn)) {
    issues.push({
      code: 'pnpm_not_found',
      message: 'pnpm command is not available.',
      fix: 'Run: corepack enable && corepack prepare pnpm@10.0.0 --activate',
    });
  }

  return {
    ok: issues.length === 0,
    issues,
  };
}

function defaultRunCommand(command, args, context) {
  const result = spawnSync(command, args, {
    stdio: 'inherit',
    cwd: context.cwd,
    env: context.env,
  });
  if (result.error) {
    return {
      status: 1,
      error: result.error.message,
    };
  }
  return {
    status: result.status ?? 1,
  };
}

function renderMarkdownSummary(summary) {
  const lines = [
    '# Bootstrap Local Summary',
    '',
    `- schemaVersion: ${summary.schemaVersion}`,
    `- generatedAt: ${summary.generatedAt}`,
    `- exitCode: ${summary.exitCode}`,
    '',
    '## Prerequisites',
  ];

  if (summary.prerequisites.ok) {
    lines.push('- ok: true');
  } else {
    lines.push('- ok: false');
    for (const issue of summary.prerequisites.issues) {
      lines.push(`- ${issue.code}: ${issue.message}`);
      lines.push(`  - fix: ${issue.fix}`);
    }
  }

  lines.push('', '## Steps');
  for (const step of summary.steps) {
    lines.push(
      `- ${step.name}: ${step.status} (required=${step.required}, exitCode=${step.exitCode}, durationMs=${step.durationMs})`,
    );
  }
  return `${lines.join('\n')}\n`;
}

export function writeSummary(summary, outputDir, cwd = process.cwd()) {
  const absoluteDir = path.resolve(cwd, outputDir);
  mkdirSync(absoluteDir, { recursive: true });

  const jsonPath = path.join(absoluteDir, 'bootstrap-summary.json');
  const mdPath = path.join(absoluteDir, 'bootstrap-summary.md');
  writeFileSync(jsonPath, JSON.stringify(summary, null, 2));
  writeFileSync(mdPath, renderMarkdownSummary(summary));
  return {
    outputDir: absoluteDir,
    jsonPath,
    markdownPath: mdPath,
  };
}

function createPlan(options) {
  const runCodex = options.withCodex && !options.skipCodex;
  return [
    {
      name: 'setup-hooks',
      command: ['pnpm', 'run', 'setup-hooks'],
      required: true,
      skip: options.skipSetupHooks,
    },
    {
      name: 'verify-lite',
      command: ['pnpm', 'run', 'verify:lite'],
      required: true,
      skip: options.skipVerifyLite,
    },
    {
      name: 'codex-quickstart',
      command: ['pnpm', 'run', 'codex:quickstart'],
      required: false,
      skip: !runCodex,
    },
  ];
}

export function runBootstrapLocal(options, deps = {}) {
  const context = {
    cwd: deps.cwd || process.cwd(),
    env: deps.env || process.env,
  };
  const runCommand = deps.runCommand || defaultRunCommand;
  const checkPrerequisitesFn = deps.checkPrerequisites || checkPrerequisites;
  const writeSummaryFn = deps.writeSummary || writeSummary;
  const now = deps.now || (() => Date.now());
  const nowIso = deps.nowIso || (() => new Date().toISOString());

  const prerequisites = checkPrerequisitesFn({
    nodeVersion: deps.nodeVersion || process.version,
    spawn: deps.spawn || spawnSync,
  });
  const steps = [];
  let exitCode = EXIT_CODES.SUCCESS;

  if (prerequisites.ok) {
    const plan = createPlan(options);
    for (const step of plan) {
      if (step.skip) {
        steps.push({
          name: step.name,
          command: step.command.join(' '),
          required: step.required,
          status: 'skipped',
          exitCode: 0,
          durationMs: 0,
        });
        continue;
      }

      const started = now();
      const result = runCommand(step.command[0], step.command.slice(1), context);
      const durationMs = Math.max(0, now() - started);
      const stepExitCode = typeof result.status === 'number' ? result.status : 1;
      const status = stepExitCode === 0 ? 'passed' : 'failed';
      steps.push({
        name: step.name,
        command: step.command.join(' '),
        required: step.required,
        status,
        exitCode: stepExitCode,
        durationMs,
        error: result.error || null,
      });

      if (stepExitCode !== 0 && step.required) {
        exitCode = EXIT_CODES.COMMAND_FAILED;
        break;
      }
    }
  } else {
    exitCode = EXIT_CODES.PREREQUISITE_FAILED;
  }

  const summary = {
    schemaVersion: SUMMARY_SCHEMA_VERSION,
    generatedAt: nowIso(),
    exitCode,
    options: {
      skipSetupHooks: options.skipSetupHooks,
      skipVerifyLite: options.skipVerifyLite,
      withCodex: options.withCodex,
      skipCodex: options.skipCodex,
      outputDir: options.outputDir,
    },
    prerequisites,
    steps,
  };

  try {
    const output = writeSummaryFn(summary, options.outputDir, context.cwd);
    summary.outputs = output;
  } catch (error) {
    if (options.json) {
      console.log(JSON.stringify(summary, null, 2));
    }
    return EXIT_CODES.INTERNAL_ERROR;
  }

  if (options.json) {
    console.log(JSON.stringify(summary, null, 2));
  } else {
    console.log(`[bootstrap] summary: ${summary.outputs.jsonPath}`);
  }

  return exitCode;
}

function printHelp() {
  console.log(`Usage: node scripts/project/bootstrap-local.mjs [options]

Options:
  --skip-setup-hooks      Skip "pnpm run setup-hooks"
  --skip-verify-lite      Skip "pnpm run verify:lite"
  --with-codex            Run "pnpm run codex:quickstart"
  --skip-codex            Force-skip codex quickstart even with --with-codex
  --output-dir <dir>      Summary output directory (default: artifacts/bootstrap)
  --json                  Print summary JSON to stdout
  -h, --help              Show this help
`);
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return EXIT_CODES.SUCCESS;
  }
  if (options.unknown.length > 0) {
    console.error(`[bootstrap] unknown argument(s): ${options.unknown.join(', ')}`);
    printHelp();
    return EXIT_CODES.PREREQUISITE_FAILED;
  }
  return runBootstrapLocal(options);
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  process.exitCode = main(process.argv);
}
