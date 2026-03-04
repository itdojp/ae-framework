import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';

function relDiff(a, b) { return Math.abs(a - b) / Math.max(a, b); }

function printUsage() {
  console.error('Usage: compare-bench.mjs <file1> <file2> [tolerance] [--out-json <path>] [--tolerance <value>]');
}

function parseTolerance(rawValue, label) {
  if (rawValue === undefined || rawValue === null || String(rawValue).trim() === '') {
    return undefined;
  }
  const parsed = Number(rawValue);
  if (!Number.isFinite(parsed) || parsed < 0) {
    throw new Error(`${label} must be a non-negative number`);
  }
  return parsed;
}

function parseArgs(argv) {
  let outJsonPath = null;
  let toleranceFromOption;
  const positional = [];

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      printUsage();
      process.exit(0);
    }
    if (arg === '--out-json') {
      const next = argv[index + 1];
      if (!next || next.startsWith('--')) {
        throw new Error('--out-json requires a value');
      }
      outJsonPath = path.resolve(next);
      index += 1;
      continue;
    }
    if (arg === '--tolerance') {
      const next = argv[index + 1];
      if (!next || next.startsWith('--')) {
        throw new Error('--tolerance requires a value');
      }
      toleranceFromOption = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--')) {
      throw new Error(`Unknown option: ${arg}`);
    }
    positional.push(arg);
  }

  if (positional.length < 2 || positional.length > 3) {
    throw new Error('Usage: compare-bench.mjs <file1> <file2> [tolerance] [--out-json <path>] [--tolerance <value>]');
  }
  if (typeof toleranceFromOption === 'string' && positional.length === 3) {
    throw new Error('Specify tolerance either as positional argument or --tolerance, not both');
  }

  return {
    file1: positional[0],
    file2: positional[1],
    toleranceRaw: toleranceFromOption ?? positional[2],
    outJsonPath,
  };
}

function extractSummary(data, filePath) {
  // Handle array format
  if (Array.isArray(data)) {
    return data;
  }
  
  // Handle object format - extract summary
  if (typeof data === 'object' && data !== null) {
    if (data.summary && Array.isArray(data.summary)) {
      return data.summary;
    }
    // Check if object itself contains benchmark data
    if (data.name && typeof data.meanMs === 'number' && typeof data.hz === 'number') {
      return [data];
    }
  }
  
  throw new Error(`Invalid bench data format in "${filePath}": expected array or object with 'summary' key, got ${typeof data}`);
}

function validateSummaryItem(item, filePath, index) {
  const errors = [];
  
  if (!item || typeof item !== 'object') {
    errors.push(`item at index ${index} is not an object`);
  } else {
    if (typeof item.name !== 'string') {
      errors.push(`item at index ${index} missing required field 'name' (string)`);
    }
    if (typeof item.meanMs !== 'number') {
      errors.push(`item at index ${index} missing required field 'meanMs' (number) - check bench output schema`);
    }
    if (typeof item.hz !== 'number') {
      errors.push(`item at index ${index} missing required field 'hz' (number) - check bench output schema`);
    }
  }
  
  if (errors.length > 0) {
    throw new Error(`❌ Bench schema validation failed in "${filePath}":\n  ${errors.join('\n  ')}\n\nExpected format: {"summary":[{"name":string,"meanMs":number,"hz":number}],"meta":{...}}`);
  }
}

async function main() {
  const { file1: f1, file2: f2, toleranceRaw: tolStr, outJsonPath } = parseArgs(process.argv.slice(2));
  
  // tol の決定: env > arg > default
  const tolFromEnv = parseTolerance(process.env.BENCH_TOLERANCE, 'BENCH_TOLERANCE');
  const tolFromArg = parseTolerance(tolStr, 'tolerance');
  const tol = Number.isFinite(tolFromEnv) ? tolFromEnv
            : Number.isFinite(tolFromArg) ? tolFromArg
            : 0.05;
  const tolSource = Number.isFinite(tolFromEnv) ? 'env' : Number.isFinite(tolFromArg) ? 'arg' : 'default';
  
  let j1, j2;
  try {
    j1 = JSON.parse(await readFile(f1, 'utf8'));
  } catch (e) {
    throw new Error(`Failed to read/parse "${f1}": ${e.message}`);
  }
  
  try {
    j2 = JSON.parse(await readFile(f2, 'utf8'));
  } catch (e) {
    throw new Error(`Failed to read/parse "${f2}": ${e.message}`);
  }
  
  const summary1 = extractSummary(j1, f1);
  const summary2 = extractSummary(j2, f2);
  
  // Validate summary items
  summary1.forEach((item, i) => validateSummaryItem(item, f1, i));
  summary2.forEach((item, i) => validateSummaryItem(item, f2, i));
  
  const map = new Map(summary1.map(s => [s.name, s]));
  let ok = true; const rows = [];
  
  for (const s2 of summary2) {
    const s1 = map.get(s2.name);
    if (!s1) continue;
    const dMean = relDiff(s1.meanMs, s2.meanMs);
    const dHz = relDiff(s1.hz, s2.hz);
    const pass = dMean <= tol && dHz <= tol;
    rows.push({ name: s2.name, mean1: s1.meanMs, mean2: s2.meanMs, dMean, hz1: s1.hz, hz2: s2.hz, dHz, pass });
    if (!pass) ok = false;
  }
  
  const payload = { ok, tol, tolSource, rows };
  if (outJsonPath) {
    await mkdir(path.dirname(outJsonPath), { recursive: true });
    await writeFile(outJsonPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
  }

  console.log('[bench-compare]', JSON.stringify(payload, null, 2));
  process.exit(ok ? 0 : 1);
}

main().catch(e => { 
  console.error(`[bench-compare] ERROR: ${e.message}`); 
  process.exit(2); 
});
