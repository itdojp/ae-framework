import { readFile } from 'node:fs/promises';

function relDiff(a, b) { return Math.abs(a - b) / Math.max(a, b); }

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
  const [f1, f2, tolStr] = process.argv.slice(2);
  
  if (!f1 || !f2) {
    throw new Error('Usage: compare-bench.mjs <file1> <file2> [tolerance]');
  }
  
  // tol の決定: env > arg > default
  const tolFromEnv = process.env.BENCH_TOLERANCE ? Number(process.env.BENCH_TOLERANCE) : undefined;
  const tolFromArg = Number(tolStr ?? '');
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
  
  console.log('[bench-compare]', JSON.stringify({ tol, tolSource, rows }, null, 2));
  process.exit(ok ? 0 : 1);
}

main().catch(e => { 
  console.error(`[bench-compare] ERROR: ${e.message}`); 
  process.exit(2); 
});