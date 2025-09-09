#!/usr/bin/env node
import { promises as fs } from 'fs';
import path from 'path';
import { spawn } from 'child_process';

const repoRoot = process.cwd();
const outDir = path.join(repoRoot, 'artifacts', 'codex');
const toolsDir = path.join(repoRoot, '.cache', 'tools');
const tlaJar = path.join(toolsDir, 'tla2tools.jar');
const alloyJar = process.env.ALLOY_JAR || path.join(toolsDir, 'alloy.jar');
const alloyRunCmd = process.env.ALLOY_RUN_CMD || null; // e.g. 'java -jar $ALLOY_JAR -f {file}'

async function ensureDir(dir) {
  await fs.mkdir(dir, { recursive: true });
}

async function findFiles(globs) {
  const results = [];
  async function walk(dir) {
    const entries = await fs.readdir(dir, { withFileTypes: true });
    for (const e of entries) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) await walk(p);
      else results.push(p);
    }
  }
  for (const g of globs) {
    const abs = path.isAbsolute(g) ? g : path.join(repoRoot, g);
    try {
      const stat = await fs.stat(abs).catch(() => null);
      if (!stat) continue;
      if (stat.isDirectory()) await walk(abs);
      else results.push(abs);
    } catch {}
  }
  return results;
}

async function download(url, dest) {
  await ensureDir(path.dirname(dest));
  await new Promise((resolve, reject) => {
    const curl = spawn('curl', ['-L', '-sS', url, '-o', dest], { stdio: 'inherit' });
    curl.on('exit', (code) => (code === 0 ? resolve() : reject(new Error(`curl exit ${code}`))));
  });
}

async function runTLC(modulePath) {
  const moduleDir = path.dirname(modulePath);
  const moduleName = path.basename(modulePath, '.tla');
  const logPath = path.join(outDir, `${moduleName}.tlc.log.txt`);
  await ensureDir(outDir);
  const args = ['-XX:+UseSerialGC', '-Xmx512m', '-cp', tlaJar, 'tlc2.TLC', '-deadlock', '-workers', '2', moduleName];
  return await new Promise((resolve) => {
    const proc = spawn('java', args, { cwd: moduleDir });
    let out = '';
    let err = '';
    const timer = setTimeout(() => {
      proc.kill('SIGKILL');
    }, 5 * 60 * 1000);
    proc.stdout.on('data', (d) => (out += d.toString()));
    proc.stderr.on('data', (d) => (err += d.toString()));
    proc.on('exit', async (code) => {
      clearTimeout(timer);
      await fs.writeFile(logPath, out + (err ? `\n[stderr]\n${err}` : ''), 'utf8');
      // naive summary parsing
      const ok = out.includes('Model checking completed. No error has been found.') || out.includes('No error has been found');
      resolve({ module: moduleName, ok: code === 0 && ok, code, log: path.relative(repoRoot, logPath) });
    });
  });
}

async function main() {
  const summary = { tlc: { results: [], skipped: [], errors: [] }, alloy: { results: [], skipped: [], errors: [] } };
  const tlaCandidates = await findFiles([
    'artifacts/codex',
    'artifacts',
    'specs/formal',
    'specs',
    'docs/formal',
  ]);
  const tlaFiles = tlaCandidates.filter((f) => f.endsWith('.tla'));
  if (tlaFiles.length === 0) {
    console.log('No TLA+ modules found. Skipping TLC.');
    summary.tlc.skipped.push('No .tla found');
  } else {
    // Ensure TLC jar
    try {
      await fs.stat(tlaJar);
    } catch {
      const url = process.env.TLA_TOOLS_URL || 'https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar';
      console.log(`Downloading TLA+ tools from ${url} ...`);
      await download(url, tlaJar);
    }
    for (const f of tlaFiles) {
      try {
        const res = await runTLC(f);
        summary.tlc.results.push({ module: res.module, ok: res.ok, code: res.code, log: res.log });
      } catch (e) {
        summary.tlc.errors.push({ file: path.relative(repoRoot, f), error: String(e) });
      }
    }
  }
  // Alloy (optional, scaffold)
  const alloyCandidates = await findFiles(['artifacts', 'specs', 'docs/formal']);
  const alsFiles = alloyCandidates.filter((f) => f.endsWith('.als'));
  if (alsFiles.length === 0) {
    summary.alloy.skipped.push('No .als found');
  } else {
    // Optional execution via ALLOY_RUN_CMD (with {file} placeholder)
    let haveJar = false;
    try { await fs.stat(alloyJar); haveJar = true; } catch {}
    if (!alloyRunCmd) {
      // Safe default: if ALLOY_JAR is available, run `java -jar $ALLOY_JAR {file}`
      if (haveJar) {
        const timeoutMs = parseInt(process.env.ALLOY_TIMEOUT_MS || '', 10) || (3 * 60 * 1000);
        for (const f of alsFiles) {
          const name = path.basename(f, '.als');
          const logPath = path.join(outDir, `${name}.alloy.log.txt`);
          try {
            await ensureDir(outDir);
            const res = await new Promise((resolve) => {
              const args = ['-jar', alloyJar, f];
              const addArgsJson = (process.env.ALLOY_CMD_JSON || '').trim();
              const addArgs = (process.env.ALLOY_CMD_ARGS || '').trim();
              if (addArgsJson) {
                try {
                  const arr = JSON.parse(addArgsJson);
                  if (Array.isArray(arr)) args.push(...arr.map(String));
                } catch (err) {
                  console.warn(`[run-model-checks] Warning: Invalid JSON in ALLOY_CMD_JSON: ${addArgsJson}`);
                  console.warn(`[run-model-checks] Error: ${err?.message ?? String(err)}`);
                  console.warn('[run-model-checks] Falling back to ALLOY_CMD_ARGS or no extra arguments.');
                }
              } else if (addArgs) {
                // Fallback: simple whitespace split (avoid quotes/escaping); prefer ALLOY_CMD_JSON
                args.push(...addArgs.split(/\s+/));
              }
              const sh = spawn('java', args, { cwd: repoRoot });
              let out = ''; let err = '';
              let terminated = false;
              const timer = setTimeout(() => {
                if (!terminated && sh.exitCode === null) {
                  sh.kill('SIGTERM');
                  setTimeout(() => { if (!terminated && sh.exitCode === null) sh.kill('SIGKILL'); }, 10 * 1000);
                }
              }, timeoutMs);
              sh.stdout.on('data', d => out += d.toString());
              sh.stderr.on('data', d => err += d.toString());
              sh.on('exit', async (code, signal) => {
                terminated = true;
                clearTimeout(timer);
                await fs.writeFile(logPath, out + (err ? `\n[stderr]\n${err}` : ''), 'utf8');
                const timeout = code === null && signal === 'SIGKILL';
                const failRegex = new RegExp(process.env.ALLOY_FAIL_REGEX || 'Exception|ERROR|FAILED', 'i');
                const okHeuristic = code === 0 && !timeout && !failRegex.test(out + err);
                resolve({ ok: okHeuristic, code, signal, timeout, log: path.relative(repoRoot, logPath) });
              });
            });
            summary.alloy.results.push({ file: path.relative(repoRoot, f), ok: res.ok, code: res.code, signal: res.signal, timeout: res.timeout, log: res.log });
          } catch (e) {
            summary.alloy.errors.push({ file: path.relative(repoRoot, f), error: String(e) });
          }
        }
      } else {
        summary.alloy.skipped.push('No ALLOY_RUN_CMD; detection only.');
        for (const f of alsFiles) summary.alloy.results.push({ file: path.relative(repoRoot, f), ok: null });
      }
    } else {
      for (const f of alsFiles) {
        const name = path.basename(f, '.als');
        const logPath = path.join(outDir, `${name}.alloy.log.txt`);
        const cmd = alloyRunCmd.replace('{file}', f).replace('$ALLOY_JAR', alloyJar);
        try {
          await ensureDir(outDir);
          const res = await new Promise((resolve) => {
            const timeoutMs = parseInt(process.env.ALLOY_TIMEOUT_MS || '', 10) || (3 * 60 * 1000);
            const sh = spawn(cmd, { shell: true, cwd: repoRoot });
            let out = ''; let err = '';
            let terminated = false;
            const timer = setTimeout(() => {
              if (!terminated && sh.exitCode === null) {
                sh.kill('SIGTERM');
                setTimeout(() => { if (!terminated && sh.exitCode === null) sh.kill('SIGKILL'); }, 10 * 1000);
              }
            }, timeoutMs);
            sh.stdout.on('data', d => out += d.toString());
            sh.stderr.on('data', d => err += d.toString());
            sh.on('exit', async (code, signal) => {
              terminated = true;
              clearTimeout(timer);
              await fs.writeFile(logPath, out + (err ? `\n[stderr]\n${err}` : ''), 'utf8');
              const timeout = code === null && signal === 'SIGKILL';
              resolve({ ok: code === 0 && !timeout, code, signal, timeout, log: path.relative(repoRoot, logPath) });
            });
          });
          summary.alloy.results.push({ file: path.relative(repoRoot, f), ok: res.ok, code: res.code, signal: res.signal, timeout: res.timeout, log: res.log });
        } catch (e) {
          summary.alloy.errors.push({ file: path.relative(repoRoot, f), error: String(e) });
        }
      }
    }
  }
  await ensureDir(outDir);
  const out = path.join(outDir, 'model-check.json');
  await fs.writeFile(out, JSON.stringify(summary, null, 2), 'utf8');
  console.log('Model check summary written to', path.relative(repoRoot, out));
}

main().catch((e) => {
  console.error('run-model-checks failed:', e);
  // Intentionally do not fail the build for now (report-only mode).
  // This behavior may change once formal checks are made gating.
  process.exit(0);
});
