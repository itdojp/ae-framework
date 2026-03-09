#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawn } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const DEFAULT_PORT = 3100;
const DEFAULT_HOST = '127.0.0.1';
const DEFAULT_OUTPUT_JSON = 'artifacts/e2e/ui-e2e-summary.json';
const DEFAULT_OUTPUT_MD = 'artifacts/e2e/ui-e2e-summary.md';
const DEFAULT_ADAPTER_SUMMARY = 'artifacts/e2e/summary.json';
const DEFAULT_ARIA_DIR = 'artifacts/e2e/ui-aria-snapshots';

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function slugify(value) {
  return String(value || '')
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 80) || 'scenario';
}

async function waitForServer(url, timeoutMs = 120000) {
  const deadline = Date.now() + timeoutMs;
  let lastError = 'server not reachable';

  while (Date.now() < deadline) {
    try {
      const response = await fetch(url);
      if (response.ok) {
        return;
      }
      lastError = `HTTP ${response.status}`;
    } catch (error) {
      lastError = error instanceof Error ? error.message : String(error);
    }
    await sleep(1000);
  }

  throw new Error(`Timed out waiting for ${url}: ${lastError}`);
}

function parseArgs(argv = process.argv) {
  const options = {
    host: DEFAULT_HOST,
    port: DEFAULT_PORT,
    baseUrl: '',
    outputJsonPath: DEFAULT_OUTPUT_JSON,
    outputMarkdownPath: DEFAULT_OUTPUT_MD,
    adapterSummaryPath: DEFAULT_ADAPTER_SUMMARY,
    ariaDir: DEFAULT_ARIA_DIR,
    skipServer: false,
    help: false,
  };

  const readValue = (value, optionName) => {
    if (!value || value.startsWith('-')) {
      throw new Error(`missing value for ${optionName}`);
    }
    return value;
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--host') {
      options.host = readValue(next, '--host');
      index += 1;
      continue;
    }
    if (arg.startsWith('--host=')) {
      options.host = arg.slice('--host='.length);
      continue;
    }
    if (arg === '--port') {
      options.port = Number.parseInt(readValue(next, '--port'), 10);
      index += 1;
      continue;
    }
    if (arg.startsWith('--port=')) {
      options.port = Number.parseInt(arg.slice('--port='.length), 10);
      continue;
    }
    if (arg === '--base-url') {
      options.baseUrl = readValue(next, '--base-url');
      index += 1;
      continue;
    }
    if (arg.startsWith('--base-url=')) {
      options.baseUrl = arg.slice('--base-url='.length);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readValue(next, '--output-json');
      index += 1;
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue(next, '--output-md');
      index += 1;
      continue;
    }
    if (arg.startsWith('--output-md=')) {
      options.outputMarkdownPath = arg.slice('--output-md='.length);
      continue;
    }
    if (arg === '--adapter-summary') {
      options.adapterSummaryPath = readValue(next, '--adapter-summary');
      index += 1;
      continue;
    }
    if (arg.startsWith('--adapter-summary=')) {
      options.adapterSummaryPath = arg.slice('--adapter-summary='.length);
      continue;
    }
    if (arg === '--aria-dir') {
      options.ariaDir = readValue(next, '--aria-dir');
      index += 1;
      continue;
    }
    if (arg.startsWith('--aria-dir=')) {
      options.ariaDir = arg.slice('--aria-dir='.length);
      continue;
    }
    if (arg === '--skip-server') {
      options.skipServer = true;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  if (!Number.isInteger(options.port) || options.port <= 0) {
    throw new Error('--port must be a positive integer');
  }

  return options;
}

function printHelp() {
  process.stdout.write(
    'Run semantic UI E2E checks with Playwright and emit evidence artifacts.\n\n'
      + 'Usage:\n'
      + '  node scripts/e2e/run-ui-e2e-semantic.mjs [options]\n\n'
      + 'Options:\n'
      + `  --host <host>                Host for local web server (default: ${DEFAULT_HOST})\n`
      + `  --port <port>                Port for local web server (default: ${DEFAULT_PORT})\n`
      + '  --base-url <url>             Use an existing base URL instead of starting Next dev\n'
      + `  --output-json <path>         Summary JSON output (default: ${DEFAULT_OUTPUT_JSON})\n`
      + `  --output-md <path>           Summary Markdown output (default: ${DEFAULT_OUTPUT_MD})\n`
      + `  --adapter-summary <path>     Adapter summary output (default: ${DEFAULT_ADAPTER_SUMMARY})\n`
      + `  --aria-dir <path>            Semantic snapshot directory (default: ${DEFAULT_ARIA_DIR})\n`
      + '  --skip-server                Do not start the local web server\n'
      + '  --help, -h                   Show help\n',
  );
}

async function captureAriaSnapshot(page, ariaDir, scenarioId, suffix) {
  const targetDir = path.resolve(ariaDir);
  fs.mkdirSync(targetDir, { recursive: true });
  const filePath = path.join(targetDir, `${slugify(scenarioId)}-${suffix}.txt`);
  const locator = await page.getByRole('main').count() > 0 ? page.getByRole('main') : page.locator('body');
  const snapshot = await locator.ariaSnapshot();
  fs.writeFileSync(filePath, `${snapshot}\n`);
  return path.relative(process.cwd(), filePath) || filePath;
}

async function runScenario(page, scenario, baseUrl, ariaDir) {
  const startedAt = new Date().toISOString();
  const start = Date.now();
  const diagnostics = [];
  let ariaSnapshotPath = null;

  try {
    await scenario.execute(page, baseUrl);
    ariaSnapshotPath = await captureAriaSnapshot(page, ariaDir, scenario.id, 'success');
    return {
      id: scenario.id,
      title: scenario.title,
      status: 'pass',
      startedAt,
      finishedAt: new Date().toISOString(),
      durationMs: Date.now() - start,
      url: page.url(),
      semanticChecks: scenario.semanticChecks,
      diagnostics,
      ariaSnapshotPath,
    };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    try {
      ariaSnapshotPath = await captureAriaSnapshot(page, ariaDir, scenario.id, 'failure');
    } catch (snapshotError) {
      diagnostics.push({
        kind: 'semantic',
        message: snapshotError instanceof Error ? snapshotError.message : String(snapshotError),
        ariaSnapshotPath: null,
      });
    }
    diagnostics.push({
      kind: 'semantic',
      message,
      ariaSnapshotPath,
    });
    return {
      id: scenario.id,
      title: scenario.title,
      status: 'fail',
      startedAt,
      finishedAt: new Date().toISOString(),
      durationMs: Date.now() - start,
      url: page.url(),
      semanticChecks: scenario.semanticChecks,
      diagnostics,
      ariaSnapshotPath,
    };
  }
}

export function buildUiE2ESummary({
  baseUrl,
  scenarios,
  ariaDir,
  adapterSummaryPath = DEFAULT_ADAPTER_SUMMARY,
  generatedAt = new Date().toISOString(),
}) {
  const passed = scenarios.filter((scenario) => scenario.status === 'pass').length;
  const failed = scenarios.filter((scenario) => scenario.status === 'fail').length;
  const skipped = scenarios.filter((scenario) => scenario.status === 'skip').length;
  const ariaSnapshotCount = scenarios.filter((scenario) => typeof scenario.ariaSnapshotPath === 'string').length;
  return {
    schemaVersion: 'ui-e2e-summary/v1',
    generatedAt,
    status: failed > 0 ? 'error' : skipped > 0 ? 'warn' : 'ok',
    baseUrl,
    summary: {
      total: scenarios.length,
      passed,
      failed,
      skipped,
      ariaSnapshotCount,
    },
    scenarios,
    artifacts: {
      ariaSnapshotsDir: ariaDir,
      adapterSummaryPath: path.relative(process.cwd(), path.resolve(adapterSummaryPath)) || adapterSummaryPath,
    },
  };
}

export function renderMarkdown(summary) {
  const lines = [
    '# UI Semantic E2E Summary',
    `- status: **${summary.status}**`,
    `- baseUrl: \`${summary.baseUrl}\``,
    `- scenarios: ${summary.summary.passed}/${summary.summary.total} passed`,
    `- aria snapshots: ${summary.summary.ariaSnapshotCount}`,
    '',
    '| Scenario | Status | Duration (ms) | Snapshot |',
    '| --- | --- | ---: | --- |',
  ];

  for (const scenario of summary.scenarios) {
    lines.push(`| ${scenario.id} | ${scenario.status} | ${scenario.durationMs} | ${scenario.ariaSnapshotPath ? `\`${scenario.ariaSnapshotPath}\`` : 'n/a'} |`);
  }

  lines.push('', '## Diagnostics');
  const diagnostics = summary.scenarios.flatMap((scenario) => scenario.diagnostics.map((entry) => ({ scenario: scenario.id, ...entry })));
  if (diagnostics.length === 0) {
    lines.push('- none');
  } else {
    for (const diagnostic of diagnostics) {
      lines.push(`- ${diagnostic.scenario}: ${diagnostic.message}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

export function toAdapterSummary(summary, adapterSummaryPath) {
  return {
    adapter: 'ui-e2e',
    status: summary.status,
    summary: `UI semantic E2E: ${summary.summary.passed}/${summary.summary.total} scenarios passed`,
    details: summary.scenarios.map((scenario) => ({
      id: scenario.id,
      title: scenario.title,
      status: scenario.status,
      url: scenario.url,
      ariaSnapshotPath: scenario.ariaSnapshotPath,
      diagnostics: scenario.diagnostics.map((entry) => entry.message),
    })),
    sourceArtifact: path.relative(process.cwd(), path.resolve(adapterSummaryPath)) || adapterSummaryPath,
  };
}

function createScenarios() {
  return [
    {
      id: 'health-overview',
      title: 'Health page exposes operational status',
      semanticChecks: [
        'Health Status heading is visible',
        'System Healthy status text is visible',
        'Service Information heading is visible',
      ],
      async execute(page, baseUrl) {
        await page.goto(`${baseUrl}/ja/health`, { waitUntil: 'domcontentloaded' });
        await page.getByRole('heading', { name: 'Health Status' }).waitFor();
        await page.getByText('System Healthy').waitFor();
        await page.getByRole('heading', { name: 'Service Information' }).waitFor();
      },
    },
    {
      id: 'semantic-form',
      title: 'Semantic form validates and submits accessibly',
      semanticChecks: [
        'Validation alert is exposed on empty submit',
        'Form fields are addressable by label',
        'Success status is exposed after submit',
      ],
      async execute(page, baseUrl) {
        await page.goto(`${baseUrl}/ja/e2e/semantic-form`, { waitUntil: 'domcontentloaded' });
        await page.getByRole('heading', { name: 'Semantic Form Demo' }).waitFor();
        await page.getByRole('button', { name: 'Submit Semantic Form' }).click();
        await page.getByRole('alert').waitFor();
        await page.getByLabel('Team name').fill('Platform QA');
        await page.getByLabel('Owner email').fill('qa@example.com');
        await page.getByRole('checkbox', { name: 'I confirm the workflow is keyboard-accessible' }).click();
        await page.getByRole('button', { name: 'Submit Semantic Form' }).click();
        await page.getByRole('status').waitFor();
        await page.getByText('Submitted semantic form for Platform QA').waitFor();
      },
    },
  ];
}

async function startServerIfNeeded(options, onSpawn = () => {}) {
  if (options.skipServer || options.baseUrl) {
    return {
      baseUrl: options.baseUrl || `http://${options.host}:${options.port}`,
      serverProcess: null,
    };
  }

  const serverProcess = spawn(
    'pnpm',
    ['--filter', '@ae-framework/web', 'exec', 'next', 'dev', '--hostname', options.host, '--port', String(options.port)],
    {
      cwd: process.cwd(),
      env: {
        ...process.env,
        CI: '1',
        NEXT_TELEMETRY_DISABLED: '1',
      },
      stdio: 'inherit',
    },
  );
  onSpawn(serverProcess);

  const baseUrl = `http://${options.host}:${options.port}`;
  await waitForServer(`${baseUrl}/api/health`);
  return { baseUrl, serverProcess };
}

async function runMain(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return { exitCode: 0 };
  }

  const outputJsonPath = path.resolve(options.outputJsonPath);
  const outputMarkdownPath = path.resolve(options.outputMarkdownPath);
  const adapterSummaryPath = path.resolve(options.adapterSummaryPath);
  const ariaDir = path.resolve(options.ariaDir);

  ensureParentDir(outputJsonPath);
  ensureParentDir(outputMarkdownPath);
  ensureParentDir(adapterSummaryPath);
  fs.mkdirSync(ariaDir, { recursive: true });

  let serverProcess = null;
  const browser = await chromium.launch({ headless: true });
  try {
    const server = await startServerIfNeeded(options, (processHandle) => {
      serverProcess = processHandle;
    });
    serverProcess = server.serverProcess;
    const baseUrl = server.baseUrl;
    const scenarios = [];
    for (const scenario of createScenarios()) {
      const page = await browser.newPage();
      const result = await runScenario(page, scenario, baseUrl, ariaDir);
      scenarios.push(result);
      await page.close();
    }

    const summary = buildUiE2ESummary({
      baseUrl,
      scenarios,
      ariaDir: path.relative(process.cwd(), ariaDir) || ariaDir,
      adapterSummaryPath,
    });
    const adapterSummary = toAdapterSummary(summary, adapterSummaryPath);

    fs.writeFileSync(outputJsonPath, `${JSON.stringify(summary, null, 2)}\n`);
    fs.writeFileSync(outputMarkdownPath, renderMarkdown(summary));
    fs.writeFileSync(adapterSummaryPath, `${JSON.stringify(adapterSummary, null, 2)}\n`);

    process.stdout.write(`[ui-e2e] summary(json): ${outputJsonPath}\n`);
    process.stdout.write(`[ui-e2e] summary(md): ${outputMarkdownPath}\n`);
    process.stdout.write(`[ui-e2e] adapter summary: ${adapterSummaryPath}\n`);
    return { exitCode: summary.status === 'error' ? 1 : 0 };
  } finally {
    await browser.close();
    if (serverProcess && !serverProcess.killed) {
      serverProcess.kill('SIGTERM');
    }
  }
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath) {
    return false;
  }
  return fileURLToPath(importMetaUrl) === path.resolve(argvPath);
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  runMain(process.argv)
    .then((result) => {
      if (result.exitCode !== 0) {
        process.exitCode = result.exitCode;
      }
    })
    .catch((error) => {
      const message = error instanceof Error ? error.message : String(error);
      process.stderr.write(`[ui-e2e] ${message}\n`);
      process.exitCode = 1;
    });
}
