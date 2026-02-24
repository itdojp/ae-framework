#!/usr/bin/env node

import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';

const DEFAULT_FIXTURE_DIR = 'fixtures/context-pack/e2e';

function normalizePath(value) {
  return value.replace(/\\/g, '/');
}

function toRepoRelative(absolutePath) {
  return normalizePath(path.relative(process.cwd(), absolutePath) || '.');
}

function printHelp() {
  process.stdout.write(`Context Pack fixture E2E runner\n\nUsage:\n  node scripts/context-pack/run-e2e-fixture.mjs [options]\n\nOptions:\n  --fixture-dir <path>  Fixture root path (default: ${DEFAULT_FIXTURE_DIR})\n  --report-dir <path>   Persist reports to this directory (default: temp dir)\n  --keep-reports        Keep reports even when all checks pass\n  --help, -h            Show this help\n\nEnvironment:\n  CONTEXT_PACK_E2E_KEEP_REPORTS=1  Same as --keep-reports\n`);
}

function parseArgs(argv) {
  const options = {
    fixtureDir: DEFAULT_FIXTURE_DIR,
    reportDir: null,
    keepReports: process.env.CONTEXT_PACK_E2E_KEEP_REPORTS === '1',
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--fixture-dir') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --fixture-dir');
      }
      options.fixtureDir = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--fixture-dir=')) {
      options.fixtureDir = arg.slice('--fixture-dir='.length);
      continue;
    }
    if (arg === '--report-dir') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --report-dir');
      }
      options.reportDir = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--report-dir=')) {
      options.reportDir = arg.slice('--report-dir='.length);
      continue;
    }
    if (arg === '--keep-reports') {
      options.keepReports = true;
      continue;
    }

    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function runNodeScript(scriptPath, args) {
  return spawnSync(process.execPath, [scriptPath, ...args], {
    cwd: process.cwd(),
    stdio: 'inherit',
  });
}

function ensurePathExists(candidatePath, label) {
  if (!fs.existsSync(candidatePath)) {
    throw new Error(`${label} not found: ${candidatePath}`);
  }
}

function reportPath(reportDir, fileName) {
  return path.join(reportDir, fileName);
}

function buildCommands(fixtureDirAbsolute, reportDirAbsolute) {
  const contextPackSources = `${toRepoRelative(fixtureDirAbsolute)}/context-pack/**/*.{yml,yaml,json}`;

  return [
    {
      name: 'context-pack:validate',
      script: 'scripts/context-pack/validate.mjs',
      args: [
        '--sources',
        contextPackSources,
        '--schema',
        'schema/context-pack-v1.schema.json',
        '--report-json',
        reportPath(reportDirAbsolute, 'context-pack-validate-report.json'),
        '--report-md',
        reportPath(reportDirAbsolute, 'context-pack-validate-report.md'),
      ],
    },
    {
      name: 'context-pack:verify-functor',
      script: 'scripts/context-pack/verify-functor.mjs',
      args: [
        '--map',
        path.join(toRepoRelative(fixtureDirAbsolute), 'functor-map.json'),
        '--schema',
        'schema/context-pack-functor-map.schema.json',
        '--context-pack-sources',
        contextPackSources,
        '--report-json',
        reportPath(reportDirAbsolute, 'context-pack-functor-report.json'),
        '--report-md',
        reportPath(reportDirAbsolute, 'context-pack-functor-report.md'),
      ],
    },
    {
      name: 'context-pack:verify-natural-transformation',
      script: 'scripts/context-pack/verify-natural-transformation.mjs',
      args: [
        '--map',
        path.join(toRepoRelative(fixtureDirAbsolute), 'natural-transformations.json'),
        '--schema',
        'schema/context-pack-natural-transformation.schema.json',
        '--context-pack-sources',
        contextPackSources,
        '--report-json',
        reportPath(reportDirAbsolute, 'context-pack-natural-transformation-report.json'),
        '--report-md',
        reportPath(reportDirAbsolute, 'context-pack-natural-transformation-report.md'),
      ],
    },
    {
      name: 'context-pack:verify-product-coproduct',
      script: 'scripts/context-pack/verify-product-coproduct.mjs',
      args: [
        '--map',
        path.join(toRepoRelative(fixtureDirAbsolute), 'product-coproduct-map.json'),
        '--schema',
        'schema/context-pack-product-coproduct.schema.json',
        '--context-pack-sources',
        contextPackSources,
        '--report-json',
        reportPath(reportDirAbsolute, 'context-pack-product-coproduct-report.json'),
        '--report-md',
        reportPath(reportDirAbsolute, 'context-pack-product-coproduct-report.md'),
      ],
    },
    {
      name: 'context-pack:verify-phase5',
      script: 'scripts/context-pack/verify-phase5-templates.mjs',
      args: [
        '--map',
        path.join(toRepoRelative(fixtureDirAbsolute), 'phase5-templates.json'),
        '--schema',
        'schema/context-pack-phase5-templates.schema.json',
        '--context-pack-sources',
        contextPackSources,
        '--report-json',
        reportPath(reportDirAbsolute, 'context-pack-phase5-report.json'),
        '--report-md',
        reportPath(reportDirAbsolute, 'context-pack-phase5-report.md'),
      ],
    },
  ];
}

function main() {
  let options;
  try {
    options = parseArgs(process.argv);
  } catch (error) {
    process.stderr.write(`[context-pack:e2e-fixture] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
    return;
  }

  if (options.help) {
    printHelp();
    return;
  }

  const fixtureDirAbsolute = path.resolve(options.fixtureDir);
  ensurePathExists(fixtureDirAbsolute, 'fixture directory');

  const reportDirProvided = typeof options.reportDir === 'string' && options.reportDir.trim().length > 0;
  const reportDirAbsolute = reportDirProvided
    ? path.resolve(options.reportDir)
    : fs.mkdtempSync(path.join(os.tmpdir(), 'context-pack-e2e-fixture-'));

  fs.mkdirSync(reportDirAbsolute, { recursive: true });

  const commands = buildCommands(fixtureDirAbsolute, reportDirAbsolute);
  const steps = [];
  let failed = false;

  process.stdout.write(`[context-pack:e2e-fixture] fixture dir: ${toRepoRelative(fixtureDirAbsolute)}\n`);
  process.stdout.write(`[context-pack:e2e-fixture] report dir: ${toRepoRelative(reportDirAbsolute)}\n`);

  for (const command of commands) {
    process.stdout.write(`[context-pack:e2e-fixture] running ${command.name}\n`);
    const result = runNodeScript(command.script, command.args);
    const exitCode = result.status ?? 1;
    steps.push({ name: command.name, exitCode });
    if (exitCode !== 0) {
      failed = true;
      break;
    }
  }

  const summary = {
    generatedAt: new Date().toISOString(),
    fixtureDir: toRepoRelative(fixtureDirAbsolute),
    reportDir: toRepoRelative(reportDirAbsolute),
    keepReports: options.keepReports || reportDirProvided,
    status: failed ? 'fail' : 'pass',
    steps,
  };

  const summaryPath = reportPath(reportDirAbsolute, 'context-pack-e2e-summary.json');
  fs.writeFileSync(summaryPath, `${JSON.stringify(summary, null, 2)}\n`, 'utf8');
  process.stdout.write(`[context-pack:e2e-fixture] summary: ${toRepoRelative(summaryPath)}\n`);

  if (!failed && !options.keepReports && !reportDirProvided) {
    fs.rmSync(reportDirAbsolute, { recursive: true, force: true });
    process.stdout.write('[context-pack:e2e-fixture] reports cleaned up (default behavior)\n');
  } else {
    process.stdout.write(`[context-pack:e2e-fixture] reports kept at ${toRepoRelative(reportDirAbsolute)}\n`);
  }

  if (failed) {
    process.stderr.write('[context-pack:e2e-fixture] validation failed\n');
    process.exitCode = 2;
  }
}

main();
