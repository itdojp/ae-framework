import { describe, it, expect } from 'vitest';
import { chmodSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const scriptPath = resolve('scripts/formal/verify-csp.mjs');

function writeFakeCspx(binDir: string) {
  const p = join(binDir, 'cspx');
  const script = `#!/usr/bin/env node
const fs = require('node:fs');
const path = require('node:path');

const args = process.argv.slice(2);
if (args.includes('--version')) {
  console.log('cspx 0.1.0');
  process.exit(0);
}

const cmd = args[0] || '';
const file = [...args].reverse().find((a) => String(a).endsWith('.cspm')) || 'UNKNOWN.cspm';
const outIdx = args.indexOf('--output');
const outPath = outIdx >= 0 ? args[outIdx + 1] : null;

const status = cmd === 'typecheck' ? 'pass' : (cmd === 'check' ? 'fail' : 'error');
const exit_code = status === 'pass' ? 0 : (status === 'fail' ? 1 : 2);

const payload = {
  schema_version: '0.1',
  tool: { name: 'cspx', version: '0.1.0', git_sha: 'UNKNOWN' },
  invocation: { command: cmd || 'n/a', args: [file], format: 'json', timeout_ms: null, memory_mb: null, seed: 0 },
  inputs: [{ path: file, sha256: 'TEST' }],
  status,
  exit_code,
  started_at: '1970-01-01T00:00:00Z',
  finished_at: '1970-01-01T00:00:00Z',
  duration_ms: 0,
  checks: [
    {
      name: cmd === 'typecheck' ? 'typecheck' : (cmd === 'check' ? 'check' : 'n/a'),
      model: null,
      target: cmd === 'check' ? 'deadlock free' : null,
      status,
      counterexample: null,
      stats: { states: 1, transitions: 0 }
    }
  ]
};

if (outPath) {
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, JSON.stringify(payload, null, 2));
} else {
  console.log(JSON.stringify(payload));
}
process.exit(exit_code);
`;
  writeFileSync(p, script, { encoding: 'utf8' });
  chmodSync(p, 0o755);
  return p;
}

function writeFakeCspxWithoutSummaryJson(binDir: string) {
  const p = join(binDir, 'cspx');
  const script = `#!/usr/bin/env node
const args = process.argv.slice(2);
if (args.includes('--version')) {
  console.log('cspx 0.1.0');
  process.exit(0);
}
if (args.includes('--summary-json')) {
  console.error(\"error: unexpected argument '--summary-json' found\\n\\nUsage: cspx typecheck --format <FORMAT> --output <OUTPUT> <FILE>\\n\");
  process.exit(2);
}
console.log('ok');
process.exit(0);
`;
  writeFileSync(p, script, { encoding: 'utf8' });
  chmodSync(p, 0o755);
  return p;
}

function runVerifyCsp(cwd: string, args: string[], env: Record<string, string>) {
  return spawnSync('node', [scriptPath, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env },
  });
}

describe('verify-csp (cspx backend)', () => {
  it('uses cspx when available (typecheck)', () => {
    const dir = mkdtempSync(join(tmpdir(), 'verify-csp-cspx-'));
    const specDir = join(dir, 'spec', 'csp');
    mkdirSync(specDir, { recursive: true });
    writeFileSync(join(specDir, 'ok.cspm'), 'SYSTEM = STOP\n', 'utf8');

    const binDir = join(dir, 'bin');
    mkdirSync(binDir, { recursive: true });
    writeFakeCspx(binDir);

    const result = runVerifyCsp(
      dir,
      ['--file', 'spec/csp/ok.cspm', '--mode', 'typecheck'],
      { PATH: `${binDir}:${process.env.PATH || ''}` },
    );
    expect(result.status).toBe(0);

    const sumPath = join(dir, 'artifacts', 'hermetic-reports', 'formal', 'csp-summary.json');
    const sum = JSON.parse(readFileSync(sumPath, 'utf8'));
    expect(sum.backend).toBe('cspx:typecheck');
    expect(sum.status).toBe('ran');
    expect(sum.resultStatus).toBe('pass');
    expect(sum.exitCode).toBe(0);

    const detailsPath = join(dir, 'artifacts', 'hermetic-reports', 'formal', 'cspx-result.json');
    const details = JSON.parse(readFileSync(detailsPath, 'utf8'));
    expect(details.schema_version).toBe('0.1');
    expect(details.status).toBe('pass');

    rmSync(dir, { recursive: true, force: true });
  });

  it('maps cspx fail to summary failed (assertions)', () => {
    const dir = mkdtempSync(join(tmpdir(), 'verify-csp-cspx-fail-'));
    const specDir = join(dir, 'spec', 'csp');
    mkdirSync(specDir, { recursive: true });
    writeFileSync(join(specDir, 'ok.cspm'), 'SYSTEM = STOP\n', 'utf8');

    const binDir = join(dir, 'bin');
    mkdirSync(binDir, { recursive: true });
    writeFakeCspx(binDir);

    const result = runVerifyCsp(
      dir,
      ['--file', 'spec/csp/ok.cspm', '--mode', 'assertions'],
      { PATH: `${binDir}:${process.env.PATH || ''}` },
    );
    expect(result.status).toBe(0);

    const sumPath = join(dir, 'artifacts', 'hermetic-reports', 'formal', 'csp-summary.json');
    const sum = JSON.parse(readFileSync(sumPath, 'utf8'));
    expect(sum.backend).toBe('cspx:assertions');
    expect(sum.status).toBe('failed');
    expect(sum.resultStatus).toBe('fail');
    expect(sum.exitCode).toBe(1);

    rmSync(dir, { recursive: true, force: true });
  });

  it('reports unsupported when cspx lacks --summary-json', () => {
    const dir = mkdtempSync(join(tmpdir(), 'verify-csp-cspx-nosummary-'));
    const specDir = join(dir, 'spec', 'csp');
    mkdirSync(specDir, { recursive: true });
    writeFileSync(join(specDir, 'ok.cspm'), 'SYSTEM = STOP\n', 'utf8');

    const binDir = join(dir, 'bin');
    mkdirSync(binDir, { recursive: true });
    writeFakeCspxWithoutSummaryJson(binDir);

    const result = runVerifyCsp(
      dir,
      ['--file', 'spec/csp/ok.cspm', '--mode', 'typecheck'],
      { PATH: `${binDir}:${process.env.PATH || ''}` },
    );
    expect(result.status).toBe(0);

    const sumPath = join(dir, 'artifacts', 'hermetic-reports', 'formal', 'csp-summary.json');
    const sum = JSON.parse(readFileSync(sumPath, 'utf8'));
    expect(sum.backend).toBe('cspx:typecheck');
    expect(sum.status).toBe('unsupported');
    expect(sum.ok).toBe(false);
    expect(sum.exitCode).toBe(2);
    expect(String(sum.output || '')).toMatch(/--summary-json/);

    rmSync(dir, { recursive: true, force: true });
  });
});
