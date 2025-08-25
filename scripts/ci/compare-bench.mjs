import { readFile } from 'node:fs/promises';

function relDiff(a, b) { return Math.abs(a - b) / Math.max(a, b); }

async function main() {
  const [f1, f2, tolStr] = process.argv.slice(2);
  
  // tol の決定: env > arg > default
  const tolFromEnv = process.env.BENCH_TOLERANCE ? Number(process.env.BENCH_TOLERANCE) : undefined;
  const tolFromArg = Number(tolStr ?? '');
  const tol = Number.isFinite(tolFromEnv) ? tolFromEnv
            : Number.isFinite(tolFromArg) ? tolFromArg
            : 0.05;
  const tolSource = Number.isFinite(tolFromEnv) ? 'env' : Number.isFinite(tolFromArg) ? 'arg' : 'default';
  
  const j1 = JSON.parse(await readFile(f1, 'utf8'));
  const j2 = JSON.parse(await readFile(f2, 'utf8'));
  const map = new Map(j1.summary.map(s => [s.name, s]));
  let ok = true; const rows = [];
  for (const s2 of j2.summary) {
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
main().catch(e => { console.error(e); process.exit(2); });