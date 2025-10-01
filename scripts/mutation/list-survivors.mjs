#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';

function parseArgs(argv) {
  const args = { report: 'reports/mutation/mutation.json', limit: Infinity };
  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    if ((current === '--report' || current === '-r') && argv[i + 1]) {
      args.report = argv[i + 1];
      i += 1;
    } else if ((current === '--limit' || current === '-l') && argv[i + 1]) {
      args.limit = Number(argv[i + 1]);
      i += 1;
    }
  }
  return args;
}

function collectSurvivors(fileEntries) {
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

async function main() {
  const args = parseArgs(process.argv);
  try {
    const reportPath = resolve(args.report);
    const content = await readFile(reportPath, 'utf8');
    const report = JSON.parse(content);
    const survivors = collectSurvivors(Object.values(report.files ?? {}));
    const limited = Number.isFinite(args.limit) ? survivors.slice(0, args.limit) : survivors;
    console.log(JSON.stringify(limited, null, 2));
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

await main();
