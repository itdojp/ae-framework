#!/usr/bin/env node

import { spawn } from 'child_process';
import fs from 'node:fs';
import path from 'node:path';

const args = process.argv.slice(2);
const skipArg = args.find((arg) => arg.startsWith('--skip='));
const skipSteps = new Set(
  skipArg
    ? skipArg
        .split('=')[1]
        .split(',')
        .map((item) => item.trim())
        .filter(Boolean)
    : []
);
const dryRun = args.includes('--dry-run');

const steps = [
  {
    name: 'BDD (inventory reservations)',
    identifier: 'bdd',
    command: ['pnpm', 'bdd'],
  },
  {
    name: 'Pact contracts (reservations)',
    identifier: 'pact',
    command: ['pnpm', 'pipelines:pact'],
  },
  {
    name: 'Property tests (web api reservations)',
    identifier: 'property',
    command: ['pnpm', 'test:property:webapi'],
  },
  {
    name: 'MBT harness (inventory model)',
    identifier: 'mbt',
    command: ['pnpm', 'test:mbt:ci'],
  },
];

const LOG_PREFIX = '\u001b[36m[pipelines]\u001b[0m';
const summaryPath = 'artifacts/e2e-demo/summary.json';

const ensureSummaryDir = () => {
  fs.mkdirSync(path.dirname(summaryPath), { recursive: true });
};

const runStep = (step) =>
  new Promise((resolve, reject) => {
    const child = spawn(step.command[0], step.command.slice(1), {
      stdio: 'inherit',
    });

    child.on('error', (error) => {
      reject(new Error(`${step.name} failed to start: ${error.message}`));
    });

    child.on('close', (code) => {
      if (code === 0) {
        resolve(0);
      } else {
        reject(new Error(`${step.name} failed with exit code ${code ?? 'unknown (process terminated)'}`));
      }
    });
  });

const run = async () => {
  const summary = {
    createdAt: new Date().toISOString(),
    dryRun,
    steps: [],
  };

  try {
    for (const step of steps) {
      const startedAt = new Date().toISOString();
      if (skipSteps.has(step.identifier)) {
        console.log(`${LOG_PREFIX} skip ${step.name}`);
        summary.steps.push({
          id: step.identifier,
          name: step.name,
          command: step.command.join(' '),
          status: 'skipped',
          startedAt,
          finishedAt: new Date().toISOString(),
        });
        continue;
      }

      console.log(`${LOG_PREFIX} start ${step.name}`);
      if (dryRun) {
        console.log(`${LOG_PREFIX} dry-run: ${step.command.join(' ')}`);
        summary.steps.push({
          id: step.identifier,
          name: step.name,
          command: step.command.join(' '),
          status: 'dry-run',
          startedAt,
          finishedAt: new Date().toISOString(),
        });
        continue;
      }

      try {
        await runStep(step);
        summary.steps.push({
          id: step.identifier,
          name: step.name,
          command: step.command.join(' '),
          status: 'success',
          startedAt,
          finishedAt: new Date().toISOString(),
        });
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        console.error(`${LOG_PREFIX} ${message}`);
        summary.steps.push({
          id: step.identifier,
          name: step.name,
          command: step.command.join(' '),
          status: 'failed',
          error: message,
          startedAt,
          finishedAt: new Date().toISOString(),
        });
        process.exitCode = 1;
        throw error;
      }
    }

    console.log(`${LOG_PREFIX} demo complete`);
  } catch (error) {
    if (!process.exitCode) {
      const message = error instanceof Error ? error.message : String(error);
      console.error(`${LOG_PREFIX} ${message}`);
      summary.steps.push({
        id: 'pipeline',
        name: 'pipeline',
        status: 'failed',
        error: message,
        finishedAt: new Date().toISOString(),
      });
      process.exitCode = 1;
    }
  } finally {
    ensureSummaryDir();
    fs.writeFileSync(summaryPath, JSON.stringify(summary, null, 2));
    console.log(`${LOG_PREFIX} wrote ${summaryPath}`);
  }
};

run();
