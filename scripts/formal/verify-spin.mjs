#!/usr/bin/env node
// Lightweight SPIN runner (Promela): generates pan, compiles, runs, and records semantic result evidence. Non-blocking.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { buildFormalRunnerOutput, buildLegacyFormalExecutionEvidence, extractToolVersion } from './execution-evidence.mjs';

function normalizeProperty(value) {
  const normalized = String(value ?? '').trim();
  return normalized || null;
}

function normalizeMaxDepth(value, fallback = 10000) {
  const parsed = Number(value);
  return Number.isFinite(parsed) && parsed >= 1 ? Math.floor(parsed) : fallback;
}

function collectIntegerMatches(output, pattern) {
  return Array.from(String(output ?? '').matchAll(pattern), (match) => Number(match[1]))
    .filter((value) => Number.isSafeInteger(value) && value >= 0);
}

function collectSelectedProperties(output) {
  const properties = Array.from(
    String(output ?? '').matchAll(/^\s*never[- ]claim\s+\+\s+\(([^)\r\n]+)\)\s*$/gimu),
    (match) => normalizeProperty(match[1]),
  ).filter((value) => value !== null);
  return [...new Set(properties)];
}

function parsePanOptions(options) {
  const maxDepths = [];
  const properties = [];
  for (let i = 0; i < options.length; i += 1) {
    const option = options[i];
    const inlineDepth = option.match(/^-m(\d+)$/u);
    const inlineProperty = option.match(/^-N(.+)$/u);
    if (inlineDepth) {
      maxDepths.push(Number(inlineDepth[1]));
    } else if (option === '-m' && /^\d+$/u.test(options[i + 1] ?? '')) {
      maxDepths.push(Number(options[i + 1]));
      i += 1;
    } else if (inlineProperty) {
      const property = normalizeProperty(inlineProperty[1]);
      if (property) properties.push(property);
    } else if (option === '-N' && normalizeProperty(options[i + 1])) {
      properties.push(normalizeProperty(options[i + 1]));
      i += 1;
    }
  }
  return {
    maxDepth: maxDepths.length === 1 ? maxDepths[0] : null,
    property: properties.length === 1 ? properties[0] : null,
    ambiguous: maxDepths.length > 1 || properties.length > 1,
  };
}

/** Parse the stable Pan summary fields and bind them to the requested run options. */
export function parseSpinSemanticResult({
  output = '',
  requestedProperty = null,
  requestedMaxDepth = 10000,
  options = [],
  trailPresent = false,
  timeout = false,
} = {}) {
  const text = String(output ?? '');
  const requested = normalizeProperty(requestedProperty);
  const requestedDepth = normalizeMaxDepth(requestedMaxDepth);
  const normalizedOptions = (Array.isArray(options) ? options : [options])
    .map((option) => String(option ?? '').trim())
    .filter(Boolean);
  const recordedOptions = normalizedOptions.length > 0 ? normalizedOptions : ['unavailable'];
  const parsedOptions = parsePanOptions(normalizedOptions);

  const errorMatches = collectIntegerMatches(text, /\berrors:\s*(\d+)\b/gimu);
  const depthMatches = collectIntegerMatches(text, /\bdepth reached\s+(\d+)\b/gimu);
  const errors = errorMatches.length === 1 ? errorMatches[0] : null;
  const depthReached = depthMatches.length === 1 ? depthMatches[0] : null;

  const reportedProperties = collectSelectedProperties(text);
  const reportedProperty = reportedProperties.length === 1 ? reportedProperties[0] : null;
  const selectedProperty = reportedProperty ?? parsedOptions.property;
  const propertyMatched = requested === null
    ? parsedOptions.property === null && reportedProperty === null
    : parsedOptions.property === requested && reportedProperty === requested;

  const outputReportsTrail = /\bwrote\b[^\r\n]*\.trail\b/iu.test(text);
  const hasTrail = trailPresent === true || outputReportsTrail;
  const counterexampleMarker = /\b(?:acceptance cycle|assertion violated|invalid end state|end state in claim reached)\b/iu.test(text);
  const counterexamplePresent = hasTrail || (errors !== null && errors > 0) || counterexampleMarker;
  const incompleteSearch = /\b(?:Search not completed|max search depth too small|out of memory|search truncated|aborting)\b/iu.test(text);
  const fullSearchReported = /\bFull statespace search for:\s*/iu.test(text);
  const searchCompleted = timeout !== true
    && fullSearchReported
    && !incompleteSearch
    && errors === 0
    && !counterexamplePresent;
  const boundsMatched = parsedOptions.maxDepth === requestedDepth
    && depthReached !== null
    && depthReached <= requestedDepth;
  const parsed = errorMatches.length === 1
    && depthMatches.length === 1
    && reportedProperties.length <= 1
    && !parsedOptions.ambiguous
    && parsedOptions.maxDepth !== null
    && (requested === null || selectedProperty !== null);

  return {
    domain: 'spin',
    parsed,
    errors,
    trailPresent: hasTrail,
    counterexamplePresent,
    searchCompleted,
    requestedProperty: requested,
    selectedProperty,
    requestedMaxDepth: requestedDepth,
    depthReached,
    options: recordedOptions,
    propertyMatched,
    boundsMatched,
    timeout: timeout === true,
  };
}

export function isSpinSemanticSuccess(semanticResult) {
  return semanticResult?.domain === 'spin'
    && semanticResult.parsed === true
    && semanticResult.errors === 0
    && semanticResult.trailPresent === false
    && semanticResult.counterexamplePresent === false
    && semanticResult.searchCompleted === true
    && semanticResult.propertyMatched === true
    && semanticResult.boundsMatched === true
    && semanticResult.timeout === false;
}

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === '--help' || a === '-h') args.help = true;
    else if (a === '--file' && next) { args.file = next; i += 1; }
    else if (a.startsWith('--file=')) { args.file = a.slice(7); }
    else if (a === '--ltl' && next) { args.ltl = next; i += 1; }
    else if (a.startsWith('--ltl=')) { args.ltl = a.slice(6); }
    else if (a === '--timeout' && next) { args.timeout = next; i += 1; }
    else if (a.startsWith('--timeout=')) { args.timeout = a.slice(10); }
    else if (a === '--max-depth' && next) { args.maxDepth = next; i += 1; }
    else if (a.startsWith('--max-depth=')) { args.maxDepth = a.slice(12); }
    else { args._.push(a); }
  }
  return args;
}

function commandExists(cmd) {
  const result = spawnSync(cmd, [], { stdio: 'ignore' });
  if (result.error && result.error.code === 'ENOENT') return false;
  return true;
}

function runCommand(cmd, cmdArgs, options = {}) {
  const result = spawnSync(cmd, cmdArgs, { encoding: 'utf8', cwd: options.cwd });
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  const output = `${stdout}${stderr}`;
  if (result.error) {
    return { available: false, status: result.status ?? null, stdout, stderr, output: output || (result.error.message ?? ''), errorCode: result.error.code ?? null };
  }
  return { available: true, status: result.status ?? null, stdout, stderr, output, errorCode: null };
}

function clamp(value, length = 4000) {
  const text = String(value || '');
  return text.length > length ? `${text.slice(0, length)}…` : text;
}

export function runSpinVerification(argv = process.argv) {
  const args = parseArgs(argv);
  if (args.help) {
    console.log('Usage: node scripts/formal/verify-spin.mjs [--file spec/spin/sample.pml] [--ltl p_done] [--timeout <ms>] [--max-depth <n>]');
    return null;
  }

  const repoRoot = process.cwd();
  const file = args.file || path.join('spec', 'spin', 'sample.pml');
  const absFile = path.resolve(repoRoot, file);
  const ltl = normalizeProperty(args.ltl);
  const timeoutMs = Number.isFinite(Number(args.timeout)) ? Number(args.timeout) : 0;
  const timeoutSec = timeoutMs > 0 ? Math.max(1, Math.floor(timeoutMs / 1000)) : 0;
  const maxDepth = normalizeMaxDepth(args.maxDepth);
  const panArgs = ['-a', `-m${maxDepth}`];
  if (ltl) panArgs.push('-N', ltl);

  const outDir = path.join(repoRoot, 'artifacts', 'hermetic-reports', 'formal');
  const outFile = path.join(outDir, 'spin-summary.json');
  const outLog = path.join(outDir, 'spin-output.txt');
  fs.mkdirSync(outDir, { recursive: true });

  let ran = false;
  let status = 'n/a';
  let output = '';
  let outputFull = '';
  const tool = 'spin';
  let exitCode = null;
  let ok = null;
  let timeMs = null;
  let toolVersion = '';
  let versionSource = 'unavailable';
  let semanticResult = parseSpinSemanticResult({
    requestedProperty: ltl,
    requestedMaxDepth: maxDepth,
    options: panArgs,
  });

  if (!fs.existsSync(absFile)) {
    status = 'file_not_found';
    outputFull = `Promela file not found: ${absFile}`;
    output = outputFull;
  } else if (!commandExists('spin')) {
    status = 'tool_not_available';
    outputFull = "SPIN not found. Install 'spin' (and gcc) to run Promela checks.";
    output = outputFull;
  } else if (!commandExists('gcc')) {
    toolVersion = extractToolVersion(runCommand('spin', ['-V']).output);
    versionSource = toolVersion ? 'cli' : 'unavailable';
    status = 'compile_not_available';
    outputFull = "gcc not found. Install 'gcc' to compile pan.c generated by SPIN.";
    output = outputFull;
  } else {
    toolVersion = extractToolVersion(runCommand('spin', ['-V']).output);
    versionSource = toolVersion ? 'cli' : 'unavailable';
    const t0 = Date.now();
    const tmpRoot = path.join(repoRoot, '.codex-local', 'tmp');
    fs.mkdirSync(tmpRoot, { recursive: true });
    const tmp = fs.mkdtempSync(path.join(tmpRoot, 'spin-'));
    try {
      const modelName = path.basename(absFile);
      const tmpModel = path.join(tmp, modelName);
      fs.copyFileSync(absFile, tmpModel);

      const gen = runCommand('spin', ['-a', tmpModel], { cwd: tmp });
      if (!gen.available || gen.status !== 0) {
        status = 'gen_failed';
        outputFull = gen.output || 'spin -a failed';
        output = clamp(outputFull);
      } else if (!fs.existsSync(path.join(tmp, 'pan.c'))) {
        status = 'gen_failed';
        outputFull = 'spin -a succeeded but pan.c was not generated';
        output = outputFull;
      } else {
        const cc = runCommand('gcc', ['-O2', '-o', 'pan', 'pan.c'], { cwd: tmp });
        if (!cc.available || cc.status !== 0) {
          status = 'compile_failed';
          outputFull = [gen.output, cc.output].filter(Boolean).join('\n');
          output = clamp(outputFull);
        } else {
          const haveTimeout = commandExists('timeout');
          const runSpec = (timeoutSec > 0 && haveTimeout)
            ? { cmd: 'timeout', args: [`${timeoutSec}s`, './pan', ...panArgs] }
            : { cmd: './pan', args: panArgs };
          const pan = runCommand(runSpec.cmd, runSpec.args, { cwd: tmp });
          ran = pan.available;
          exitCode = pan.status;
          if (!pan.available) {
            status = 'tool_not_available';
            outputFull = pan.output || 'Failed to execute pan';
            output = clamp(outputFull);
          } else {
            const timedOut = timeoutSec > 0 && haveTimeout && pan.status === 124;
            const trailPresent = fs.readdirSync(tmp).some((entry) => entry.endsWith('.trail'));
            semanticResult = parseSpinSemanticResult({
              output: pan.output,
              requestedProperty: ltl,
              requestedMaxDepth: maxDepth,
              options: panArgs,
              trailPresent,
              timeout: timedOut,
            });
            status = timedOut ? 'timeout' : (pan.status === 0 ? 'ran' : 'failed');
            ok = status === 'ran' ? isSpinSemanticSuccess(semanticResult) : (status === 'failed' ? false : null);
            outputFull = [gen.output, cc.output, pan.output].filter(Boolean).join('\n');
            output = clamp(outputFull);
          }
        }
      }
    } finally {
      try { fs.rmSync(tmp, { recursive: true, force: true }); } catch {}
    }
    timeMs = Date.now() - t0;
  }

  try { fs.writeFileSync(outLog, outputFull || output, 'utf-8'); } catch {}

  const relativeInput = path.relative(repoRoot, absFile);
  const relativeLog = path.relative(repoRoot, outLog);
  const executionEvidence = buildLegacyFormalExecutionEvidence({
    runner: 'spin',
    toolName: 'SPIN',
    toolVersion,
    versionSource,
    inputPaths: [relativeInput],
    status,
    ok,
    ran,
    attempted: ['gen_failed', 'compile_failed'].includes(status),
    exitCode,
    logPath: relativeLog,
    scope: `SPIN/Promela verification of ${relativeInput}${ltl ? ` with LTL property ${ltl}` : ''}`,
    assumptions: [
      'The result applies only to the supplied Promela model, generated pan verifier, selected property, and depth bound.',
    ],
    semanticResult,
  });

  const summary = {
    tool,
    file: relativeInput,
    ltl,
    ran,
    status,
    ok,
    exitCode,
    timeMs,
    timestamp: new Date().toISOString(),
    output,
    outputFile: relativeLog,
    semanticResult,
    runnerResult: buildFormalRunnerOutput({ runner: 'spin', executionEvidence }),
  };
  fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
  console.log(`SPIN summary written: ${path.relative(repoRoot, outFile)}`);
  console.log(`- file=${summary.file} status=${status}${ltl ? ` ltl=${ltl}` : ''} errors=${semanticResult.errors ?? 'unparsed'}`);
  return summary;
}

const isDirectRun = process.argv[1]
  && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url);
if (isDirectRun) {
  runSpinVerification();
  // Deliberately non-blocking: consumers enforce the recorded evidence contract.
  process.exit(0);
}
