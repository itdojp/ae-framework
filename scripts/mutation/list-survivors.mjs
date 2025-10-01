#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export function parseArgs(argv) {
  const args = { report: 'reports/mutation/mutation.json', limit: Infinity };
  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    if ((current === '--report' || current === '-r') && argv[i + 1]) {
      args.report = argv[i + 1];
      i += 1;
    } else if ((current === '--limit' || current === '-l') && argv[i + 1]) {
      const rawLimit = Number(argv[i + 1]);
      args.limit = Number.isNaN(rawLimit) ? Infinity : rawLimit;
      i += 1;
    }
  }
  return args;
}

export function collectSurvivors(fileEntries) {
  const survivors = [];
  for (const entry of fileEntries) {
    const mutants = entry.mutants ?? [];
    for (const mutant of mutants) {
      if (mutant.status === 'Survived') {
        survivors.push({
          file: entry.path ?? 'unknown',
          mutator: mutant.mutatorName,
          location: mutant.location ?? null,
        });
      }
    }
  }
  return survivors;
}

export async function readMutationReport(reportPath) {
  const content = await readFile(reportPath, 'utf8');
  return JSON.parse(content);
}

export function limitSurvivors(survivors, limit) {
  if (!Number.isFinite(limit)) {
    return survivors;
  }
  return survivors.slice(0, Math.max(0, limit));
}

export async function listSurvivors({ report, limit } = {}) {
  const reportPath = resolve(report ?? 'reports/mutation/mutation.json');
  const mutationReport = await readMutationReport(reportPath);
  const fileEntries = Object.values(mutationReport.files ?? {});
  const survivors = collectSurvivors(fileEntries);
  return limitSurvivors(survivors, limit ?? Infinity);
}

export async function main(argv = process.argv) {
  const args = parseArgs(argv);
  try {
    const survivors = await listSurvivors({ report: args.report, limit: args.limit });
    console.log(JSON.stringify(survivors, null, 2));
  } catch (error) {
    if (error.code === 'ENOENT') {
      console.error(`No mutation report found at ${args.report}`);
      console.log('[]');
    } else {
      console.error('Failed to read mutation report:', error.message);
      process.exitCode = 1;
    }
  }
}

const invokedDirectly = (() => {
  try {
    return resolve(process.argv[1] ?? '') === fileURLToPath(import.meta.url);
  } catch (error) {
    return false;
  }
})();

if (invokedDirectly) {
  await main();
}
