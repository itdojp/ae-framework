#!/usr/bin/env node
import { promises as fs } from 'fs';
import path from 'path';

const repoRoot = process.cwd();

function slug(s) {
  return s.toLowerCase().trim().replace(/[^a-z0-9]+/g, '-');
}

async function readFileSafe(p) {
  try { return await fs.readFile(p, 'utf8'); } catch { return ''; }
}

async function walk(dir, filter = () => true) {
  const out = [];
  async function rec(d) {
    let ents; try { ents = await fs.readdir(d, { withFileTypes: true }); } catch { return; }
    for (const e of ents) {
      const p = path.join(d, e.name);
      if (e.isDirectory()) await rec(p);
      else if (filter(p)) out.push(p);
    }
  }
  await rec(dir);
  return out;
}

async function findFeatureFiles() {
  const dir = path.join(repoRoot, 'specs', 'bdd', 'features');
  return await walk(dir, (p) => p.endsWith('.feature'));
}

async function parseFeatures(files) {
  const scenarios = [];
  for (const f of files) {
    const text = await readFileSafe(f);
    const lines = text.split(/\r?\n/);
    let pendingTags = [];
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      if (line.startsWith('@')) {
        const tags = line.split(/\s+/).filter(Boolean);
        pendingTags = [...pendingTags, ...tags];
        continue;
      }
      const m = line.match(/^Scenario:\s*(.+)$/i);
      if (m) {
        const name = m[1].trim();
        const id = slug(name);
        scenarios.push({ file: path.relative(repoRoot, f), name, id, tags: pendingTags });
        pendingTags = [];
      }
      // Note: Do not reset tags on blank lines; in Gherkin, tags persist until applied to a Scenario/Feature
    }
  }
  return scenarios;
}

async function firstMatch(files, needles) {
  for (const p of files) {
    const text = await readFileSafe(p);
    for (const n of needles) {
      if (n && text.includes(n)) return path.relative(repoRoot, p);
    }
  }
  return 'N/A';
}

async function main() {
  const featureFiles = await findFeatureFiles();
  const scenarios = await parseFeatures(featureFiles);
  // Candidate search spaces
  const testFiles = await walk(path.join(repoRoot, 'tests'), (p) => /\.(test|spec)\.[tj]sx?$/.test(p));
  const implFiles = await walk(path.join(repoRoot, 'src'), (p) => /\.[tj]sx?$/.test(p));
  const tlaFiles = [];
  for (const dir of ['specs', 'artifacts', path.join('docs', 'formal')]) {
    const base = path.join(repoRoot, dir);
    tlaFiles.push(...await walk(base, (p) => p.endsWith('.tla') || p.endsWith('.als')));
  }

  const rows = [];
  let coveredTests = 0, coveredImpl = 0, coveredFormal = 0;
  for (const sc of scenarios) {
    const needles = [sc.name, sc.id, ...(sc.tags || [])];
    const test = await firstMatch(testFiles, needles);
    const impl = await firstMatch(implFiles, needles);
    const formal = await firstMatch(tlaFiles, needles);
    if (test !== 'N/A') coveredTests++;
    if (impl !== 'N/A') coveredImpl++;
    if (formal !== 'N/A') coveredFormal++;
    rows.push({ scenario: sc.name, id: sc.id, tags: (sc.tags || []).join(' '), test, impl, formal });
  }

  const csvLines = ['Scenario,Id,Tags,Test,Implementation,Formal'];
  for (const r of rows) {
    const esc = (s) => (s.includes(',') ? '"' + s.replace(/"/g, '""') + '"' : s);
    csvLines.push([r.scenario, r.id, r.tags, r.test, r.impl, r.formal].map((v) => esc(String(v))).join(','));
  }

  const outCsv = path.join(repoRoot, 'traceability.csv');
  await fs.writeFile(outCsv, csvLines.join('\n'), 'utf8');

  const summary = {
    total: scenarios.length,
    testsLinked: coveredTests,
    implLinked: coveredImpl,
    formalLinked: coveredFormal,
    rows,
  };
  const outJson = path.join(repoRoot, 'traceability.json');
  await fs.writeFile(outJson, JSON.stringify(summary, null, 2), 'utf8');
  console.log('Generated traceability.csv and traceability.json');
}

main().catch((e) => { console.error('traceability build failed', e); process.exit(1); });
