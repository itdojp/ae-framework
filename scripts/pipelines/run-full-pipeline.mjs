#!/usr/bin/env node

import { spawn } from 'child_process';

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
const mutationTargetArg = args.find((arg) => arg.startsWith('--mutation-target='));
const dryRun = args.includes('--dry-run');

const mutationTarget = mutationTargetArg ? mutationTargetArg.split('=')[1] : undefined;

const steps = [
  {
    name: 'verify:lite',
    identifier: 'verify:lite',
    command: ['pnpm', 'verify:lite'],
  },
  {
    name: 'pact contracts',
    identifier: 'pact',
    command: ['pnpm', 'pipelines:pact'],
  },
  {
    name: 'api fuzz',
    identifier: 'api-fuzz',
    command: ['pnpm', 'pipelines:api-fuzz'],
  },
  {
    name: mutationTarget ? `mutation quick (${mutationTarget})` : 'mutation quick',
    identifier: 'mutation',
    command: mutationTarget
      ? ['pnpm', 'pipelines:mutation:quick', '--', '--mutate', mutationTarget]
      : ['pnpm', 'pipelines:mutation:quick'],
  },
];

const LOG_PREFIX = '\u001b[36m[pipelines]\u001b[0m';

const run = async () => {
  for (const step of steps) {
    if (skipSteps.has(step.identifier)) {
      console.log(`${LOG_PREFIX} skip ${step.name}`);
      continue;
    }

    console.log(`${LOG_PREFIX} start ${step.name}`);
    if (dryRun) {
      console.log(`${LOG_PREFIX} dry-run: ${step.command.join(' ')}`);
      continue;
    }

    await new Promise((resolve, reject) => {
      const child = spawn(step.command[0], step.command.slice(1), {
        stdio: 'inherit',
      });

      child.on('close', (code) => {
        if (code === 0) {
          resolve();
        } else {
          reject(new Error(`${step.name} failed with exit code ${code}`));
        }
      });
    });
  }

  console.log(`${LOG_PREFIX} pipeline complete`);
};

run().catch((error) => {
  console.error(`${LOG_PREFIX}`, error.message);
  process.exitCode = 1;
});
