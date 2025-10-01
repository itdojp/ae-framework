#!/usr/bin/env node
import { basename, resolve } from 'node:path';
import { collectSurvivors, limitSurvivors, readMutationReport } from './list-survivors.mjs';

function parseArgs(argv) {
  const args = { report: 'reports/mutation/mutation.json', limit: 5 };
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

function computeMetrics(fileEntries) {
  let killed = 0;
  let survived = 0;
  let timeout = 0;
  let noCover = 0;
  let errors = 0;

  for (const entry of fileEntries) {
    const mutants = entry.mutants || [];
    for (const mutant of mutants) {
      switch (mutant.status) {
        case 'Killed':
          killed += 1;
          break;
        case 'Survived':
          survived += 1;
          break;
        case 'Timeout':
          timeout += 1;
          break;
        case 'NoCoverage':
          noCover += 1;
          break;
        case 'CompileError':
        case 'RuntimeError':
        case 'Ignored':
          errors += 1;
          break;
        default:
          errors += 1;
          break;
      }
    }
  }

  const totalTested = killed + survived + timeout;
  const mutationScore = totalTested === 0 ? 0 : (killed / totalTested) * 100;
  return { killed, survived, timeout, noCover, errors, mutationScore };
}

async function main() {
  const args = parseArgs(process.argv);
  const reportPath = resolve(args.report);
  let report;
  try {
    report = await readMutationReport(reportPath);
  } catch (error) {
    console.error(`Unable to read mutation report at ${reportPath}:`, error.message);
    process.exitCode = 1;
    return;
  }

  const fileEntries = Object.values(report.files ?? {});
  const metrics = computeMetrics(fileEntries);
  const topSurvivors = limitSurvivors(collectSurvivors(fileEntries), args.limit);

  const title = `Mutation Quick Summary — ${basename(reportPath)}`;
  console.log(`# ${title}`);
  console.log();
  console.log(`- Location: \
	t${reportPath}`);
  console.log(`- Score: ${metrics.mutationScore.toFixed(2)}% (killed ${metrics.killed}, survived ${metrics.survived}, timeout ${metrics.timeout}, no-cover ${metrics.noCover}, errors ${metrics.errors})`);

  if (topSurvivors.length > 0) {
    console.log();
    console.log('## Top surviving mutants');
    for (const survivor of topSurvivors) {
      const line = survivor.location?.start?.line;
      const location = line ? `:${line}` : '';
      console.log(`- \	${survivor.file}${location} — ${survivor.mutator}`);
    }
  }
}

await main();
