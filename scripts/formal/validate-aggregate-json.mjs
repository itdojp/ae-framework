import fs from 'node:fs';

function warn(msg){
  // GitHub Actions warning annotation
  console.log(`::warning::${msg}`);
}

try {
  const p = 'artifacts/formal/formal-aggregate.json';
  if (!fs.existsSync(p)) {
    warn('formal-aggregate.json not found (skipping schema check)');
    process.exit(0);
  }
  const j = JSON.parse(fs.readFileSync(p,'utf-8'));
  const keys = ['tlc','alloy','tla','smt','apalache','conformance','info'];
  for (const k of keys){ if (!(k in j)) warn(`missing top-level key: ${k}`); }
  if (!j.info || !j.info.present) warn('info.present missing');
  if (j.info && typeof j.info.presentCount !== 'number') warn('info.presentCount not a number');
  if (j.info && j.info.ranOk && j.info.ranOk.apalache){
    const r = j.info.ranOk.apalache;
    if (typeof r.ran !== 'boolean') warn('ranOk.apalache.ran not boolean');
    if (!(r.ok === true || r.ok === false || r.ok === null)) warn('ranOk.apalache.ok not boolean|null');
  }
  // Non-blocking by design
} catch (e) {
  warn(`aggregate schema check failed: ${String(e && e.message || e)}`);
}

