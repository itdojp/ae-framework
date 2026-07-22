#!/usr/bin/env node
import { promises as fs } from 'fs';
import path from 'path';
import { spawn } from 'child_process';
import { createHash } from 'crypto';

const repoRoot = process.cwd();
const outDir = path.join(repoRoot, 'artifacts', 'codex');
const toolsDir = path.join(repoRoot, '.cache', 'tools');
const tlaJar = path.join(toolsDir, 'tla2tools.jar');
const alloyJar = process.env.ALLOY_JAR || path.join(toolsDir, 'alloy.jar');
const defaultTlaToolsUrl = 'https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar';

async function ensureDir(dir) {
  await fs.mkdir(dir, { recursive: true });
}

async function statFile(p) {
  try {
    const st = await fs.stat(p);
    return st.isFile() ? st : null;
  } catch {
    return null;
  }
}

async function sha256File(filePath) {
  const content = await fs.readFile(filePath);
  return createHash('sha256').update(content).digest('hex');
}

function inferVersionFromUrl(url) {
  const match = String(url || '').match(/\/v([^/]+)\//u);
  return match?.[1] || null;
}

async function buildToolDescriptor({ name, artifactPath, version }) {
  return {
    name,
    version: String(version || '').trim() || 'unknown',
    artifactPath: path.relative(repoRoot, artifactPath),
    artifactSha256: await sha256File(artifactPath),
  };
}

function uniqueAbs(paths) {
  const seen = new Set();
  const out = [];
  for (const p of paths) {
    const abs = path.resolve(p);
    if (seen.has(abs)) continue;
    seen.add(abs);
    out.push(abs);
  }
  return out;
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
    let settled = false;
    const settle = (error) => {
      if (settled) return;
      settled = true;
      if (error) reject(error);
      else resolve();
    };
    curl.on('error', (error) => settle(error));
    curl.on('exit', (code) => settle(code === 0 ? null : new Error(`curl exit ${code}`)));
  });
}

function parseAlloyArgTemplate() {
  const jsonTemplate = (process.env.ALLOY_CMD_JSON || '').trim();
  const rawTemplate = (process.env.ALLOY_CMD_ARGS || '').trim();
  if (jsonTemplate) {
    try {
      const parsed = JSON.parse(jsonTemplate);
      if (!Array.isArray(parsed)) {
        console.warn(`[run-model-checks] Warning: ALLOY_CMD_JSON is valid JSON but not an array. Value: ${jsonTemplate}`);
      } else {
        return parsed.map(String);
      }
    } catch (err) {
      console.warn(`[run-model-checks] Warning: Invalid JSON in ALLOY_CMD_JSON: ${jsonTemplate}`);
      console.warn(`[run-model-checks] Error: ${err?.message ?? String(err)}`);
    }
    console.warn('[run-model-checks] Falling back to ALLOY_CMD_ARGS or default argv template.');
  }
  if (rawTemplate) {
    return rawTemplate.split(/\s+/u).filter(Boolean);
  }
  return ['exec', '-q', '-o', '-', '-f', '{file}'];
}

function buildAlloyJavaArgs(file) {
  const template = parseAlloyArgTemplate();
  const rendered = template.map((arg) => (arg === '{file}' ? file : arg));
  if (!template.includes('{file}')) {
    rendered.push(file);
  }
  return ['-jar', alloyJar, ...rendered];
}

async function resolveTlaConfig(modulePath) {
  const moduleName = path.basename(modulePath, '.tla');
  const moduleDir = path.dirname(modulePath);
  const candidates = [
    path.join(moduleDir, `${moduleName}.cfg`),
    path.join(repoRoot, 'spec', 'formal', 'configs', `${moduleName}.cfg`),
    path.join(repoRoot, 'spec', 'formal', 'tla+', `${moduleName}.cfg`),
    path.join(repoRoot, 'spec', 'formal', `${moduleName}.cfg`),
    path.join(repoRoot, 'spec', 'tla', `${moduleName}.cfg`),
  ];
  for (const cfg of candidates) {
    if (await statFile(cfg)) return cfg;
  }
  return null;
}

async function runTLC(modulePath, configPath) {
  const moduleDir = path.dirname(modulePath);
  const moduleName = path.basename(modulePath, '.tla');
  const logPath = path.join(outDir, `${moduleName}.tlc.log.txt`);
  await ensureDir(outDir);
  const args = ['-XX:+UseSerialGC', '-Xmx512m', '-cp', tlaJar, 'tlc2.TLC', '-deadlock', '-workers', '2'];
  if (configPath) {
    args.push('-config', configPath);
  }
  args.push(moduleName);
  return await new Promise((resolve) => {
    const proc = spawn('java', args, { cwd: moduleDir });
    let out = '';
    let err = '';
    let settled = false;
    let timedOut = false;
    const settle = async (result) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      await fs.writeFile(logPath, out + (err ? `\n[stderr]\n${err}` : ''), 'utf8');
      resolve(result);
    };
    const timer = setTimeout(() => {
      timedOut = true;
      proc.kill('SIGKILL');
    }, 5 * 60 * 1000);
    proc.stdout.on('data', (d) => (out += d.toString()));
    proc.stderr.on('data', (d) => (err += d.toString()));
    proc.on('error', (error) => {
      err += `${err ? '\n' : ''}${error instanceof Error ? error.message : String(error)}`;
      void settle({
        module: moduleName,
        ok: false,
        code: null,
        signal: null,
        timeout: false,
        toolError: error instanceof Error ? error.message : String(error),
        log: path.relative(repoRoot, logPath),
      });
    });
    proc.on('exit', (code, signal) => {
      // naive summary parsing
      const ok = out.includes('Model checking completed. No error has been found.') || out.includes('No error has been found');
      void settle({
        module: moduleName,
        ok: !timedOut && code === 0 && ok,
        code,
        signal,
        timeout: timedOut,
        toolError: null,
        log: path.relative(repoRoot, logPath),
      });
    });
  });
}

async function main() {
  const summary = {
    schemaVersion: 'model-check-report/v1',
    artifactStatus: 'execution-report',
    status: 'not-run',
    ok: null,
    generatedAtUtc: new Date().toISOString(),
    producer: 'scripts/verify/run-model-checks.mjs',
    tlc: { results: [], skipped: [], errors: [] },
    alloy: { results: [], skipped: [], errors: [] },
  };
  const tlaCandidates = await findFiles([
    'artifacts/codex',
    'artifacts',
    'spec/formal',
    'spec',
    'specs',
    'docs/formal',
  ]);
  const tlaFiles = uniqueAbs(tlaCandidates.filter((f) => f.endsWith('.tla')));
  if (tlaFiles.length === 0) {
    console.log('No TLA+ modules found. Skipping TLC.');
    summary.tlc.skipped.push('No .tla found');
  } else {
    // Ensure TLC jar
    let tlaToolsUrl = null;
    let tlaTool = null;
    try {
      try {
        await fs.stat(tlaJar);
      } catch {
        tlaToolsUrl = process.env.TLA_TOOLS_URL || defaultTlaToolsUrl;
        console.log(`Downloading TLA+ tools from ${tlaToolsUrl} ...`);
        await download(tlaToolsUrl, tlaJar);
      }
      tlaTool = await buildToolDescriptor({
        name: 'TLC',
        artifactPath: tlaJar,
        version: process.env.TLA_TOOLS_VERSION || inferVersionFromUrl(tlaToolsUrl),
      });
    } catch (error) {
      summary.tlc.errors.push({
        file: path.relative(repoRoot, tlaJar),
        error: error instanceof Error ? error.message : String(error),
      });
    }
    if (tlaTool) {
      for (const f of tlaFiles) {
        try {
          const moduleName = path.basename(f, '.tla');
          const configPath = await resolveTlaConfig(f);
          if (!configPath) {
            summary.tlc.skipped.push(`${moduleName} (${path.relative(repoRoot, f)}): no .cfg found`);
            continue;
          }
          const res = await runTLC(f, configPath);
          const executionStatus = res.timeout ? 'timeout' : res.toolError ? 'tool-error' : 'executed';
          summary.tlc.results.push({
            module: res.module,
            ok: res.ok,
            code: res.code,
            log: res.log,
            config: path.relative(repoRoot, configPath),
            executionStatus,
            evidence: {
              tool: tlaTool,
              input: {
                specification: path.relative(repoRoot, f),
                configuration: path.relative(repoRoot, configPath),
              },
              result: {
                outcome: res.timeout ? 'timeout' : res.toolError ? 'tool-error' : res.ok ? 'pass' : 'fail',
                exitCode: res.code,
                signal: res.signal,
                ...(res.toolError ? { error: res.toolError } : {}),
                log: res.log,
              },
              scope: {
                kind: 'tla-module',
                identifier: res.module,
                properties: 'declared by the TLA+ module and TLC configuration',
              },
              assumptions: [
                'The result applies only to the supplied TLA+ module and TLC configuration.',
                'The result does not establish correctness of implementation code outside the model.',
              ],
            },
          });
        } catch (e) {
          summary.tlc.errors.push({ file: path.relative(repoRoot, f), error: String(e) });
        }
      }
    }
  }
  // Alloy (optional, scaffold)
  const alloyCandidates = await findFiles(['artifacts', 'spec/formal', 'spec', 'specs', 'docs/formal']);
  const alsFiles = uniqueAbs(alloyCandidates.filter((f) => f.endsWith('.als')));
  if (alsFiles.length === 0) {
    summary.alloy.skipped.push('No .als found');
  } else {
    if (process.env.ALLOY_RUN_CMD) {
      console.warn('[run-model-checks] Warning: ALLOY_RUN_CMD shell templates are ignored. Use ALLOY_CMD_JSON/ALLOY_CMD_ARGS for argv-safe Alloy arguments.');
    }
    let haveJar = false;
    try { await fs.stat(alloyJar); haveJar = true; } catch {}
    if (haveJar) {
      let alloyTool = null;
      try {
        alloyTool = await buildToolDescriptor({
          name: 'Alloy',
          artifactPath: alloyJar,
          version: process.env.ALLOY_VERSION,
        });
      } catch (error) {
        summary.alloy.errors.push({
          file: path.relative(repoRoot, alloyJar),
          error: error instanceof Error ? error.message : String(error),
        });
      }
      const timeoutMs = parseInt(process.env.ALLOY_TIMEOUT_MS || '', 10) || (3 * 60 * 1000);
      for (const f of alloyTool ? alsFiles : []) {
        const name = path.basename(f, '.als');
        const logPath = path.join(outDir, `${name}.alloy.log.txt`);
        try {
          await ensureDir(outDir);
          const res = await new Promise((resolve) => {
            const args = buildAlloyJavaArgs(f);
            const sh = spawn('java', args, { cwd: repoRoot });
            let out = ''; let err = '';
            let terminated = false;
            let settled = false;
            let timedOut = false;
            const settle = async (result) => {
              if (settled) return;
              settled = true;
              terminated = true;
              clearTimeout(timer);
              await fs.writeFile(logPath, out + (err ? `\n[stderr]\n${err}` : ''), 'utf8');
              resolve(result);
            };
            const timer = setTimeout(() => {
              if (!terminated && sh.exitCode === null) {
                timedOut = true;
                sh.kill('SIGTERM');
                setTimeout(() => { if (!terminated && sh.exitCode === null) sh.kill('SIGKILL'); }, 10 * 1000);
              }
            }, timeoutMs);
            sh.stdout.on('data', d => out += d.toString());
            sh.stderr.on('data', d => err += d.toString());
            sh.on('error', (error) => {
              const message = error instanceof Error ? error.message : String(error);
              err += `${err ? '\n' : ''}${message}`;
              void settle({ ok: false, code: null, signal: null, timeout: false, toolError: message, log: path.relative(repoRoot, logPath) });
            });
            sh.on('exit', (code, signal) => {
              const timeout = timedOut;
              let failRegex;
              try {
                failRegex = new RegExp(process.env.ALLOY_FAIL_REGEX || 'Exception|ERROR|FAILED|Counterexample|assertion', 'i');
              } catch {
                console.warn(`[run-model-checks] Warning: Invalid ALLOY_FAIL_REGEX '${process.env.ALLOY_FAIL_REGEX}'. Using default.`);
                failRegex = /Exception|ERROR|FAILED|Counterexample|assertion/i;
              }
              const okHeuristic = code === 0 && !timeout && !failRegex.test(out + err);
              void settle({ ok: okHeuristic, code, signal, timeout, toolError: null, log: path.relative(repoRoot, logPath) });
            });
          });
          const inputFile = path.relative(repoRoot, f);
          const executionStatus = res.timeout ? 'timeout' : res.toolError ? 'tool-error' : 'executed';
          summary.alloy.results.push({
            file: inputFile,
            ok: res.ok,
            code: res.code,
            signal: res.signal,
            timeout: res.timeout,
            log: res.log,
            executionStatus,
            evidence: {
              tool: alloyTool,
              input: { specification: inputFile, configuration: null },
              result: {
                outcome: res.timeout ? 'timeout' : res.toolError ? 'tool-error' : res.ok ? 'pass' : 'fail',
                exitCode: res.code,
                signal: res.signal,
                ...(res.toolError ? { error: res.toolError } : {}),
                log: res.log,
              },
              scope: {
                kind: 'alloy-model',
                identifier: path.basename(f, '.als'),
                properties: 'commands and assertions declared by the supplied Alloy model',
              },
              assumptions: [
                'The result applies only to the bounds and commands declared by the supplied Alloy model.',
                'The result does not establish correctness of implementation code outside the model.',
              ],
            },
          });
        } catch (e) {
          summary.alloy.errors.push({ file: path.relative(repoRoot, f), error: String(e) });
        }
      }
    } else {
      summary.alloy.skipped.push('No Alloy jar available; detection only.');
    }
  }
  const executedResults = [...summary.tlc.results, ...summary.alloy.results];
  const errorCount = summary.tlc.errors.length + summary.alloy.errors.length;
  if (executedResults.length > 0) {
    const actualExecutions = executedResults.filter((result) => result.executionStatus === 'executed');
    const onlyToolErrors = actualExecutions.length === 0
      && executedResults.every((result) => result.executionStatus === 'tool-error');
    if (onlyToolErrors) {
      summary.status = 'tool-error';
      summary.ok = null;
    } else {
      summary.ok = errorCount === 0 && executedResults.every((result) => result.ok === true);
      summary.status = summary.ok ? 'executed' : 'failed';
    }
  } else if (errorCount > 0) {
    summary.status = 'tool-error';
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
