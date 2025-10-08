#!/usr/bin/env node
// Conformance check with optional KvOnce trace pipeline integration
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import yaml from 'yaml';
import Ajv from 'ajv';
import addFormats from 'ajv-formats';
import { appendSection } from '../ci/step-summary.mjs';
import { collectTraceIdsFromNdjson, buildTempoLinks } from '../trace/tempo-link-utils.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');
const DEFAULT_TRACE_DIR = path.join('hermetic-reports', 'trace');

function readYaml(p) {
  return yaml.parse(fs.readFileSync(p, 'utf8'));
}
function readJson(p) {
  return JSON.parse(fs.readFileSync(p, 'utf8'));
}
function writeJson(p, obj) {
  fs.mkdirSync(path.dirname(p), { recursive: true });
  fs.writeFileSync(p, JSON.stringify(obj, null, 2));
}

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if (arg === '--help' || arg === '-h') {
      args.help = true;
    } else if ((arg === '--in' || arg === '-i') && next) {
      args.in = next;
      i += 1;
    } else if (arg.startsWith('--in=')) {
      args.in = arg.slice(5);
    } else if ((arg === '--out') && next) {
      args.out = next;
      i += 1;
    } else if (arg.startsWith('--out=')) {
      args.out = arg.slice(6);
    } else if ((arg === '--schema') && next) {
      args.schema = next;
      i += 1;
    } else if (arg.startsWith('--schema=')) {
      args.schema = arg.slice(9);
    } else if ((arg === '--disable-invariants' || arg === '--disable') && next) {
      args.disable = next;
      i += 1;
    } else if (arg.startsWith('--disable-invariants=')) {
      args.disable = arg.slice(21);
    } else if ((arg === '--onhand-min') && next) {
      args.onhandMin = next;
      i += 1;
    } else if (arg.startsWith('--onhand-min=')) {
      args.onhandMin = arg.slice(13);
    } else if ((arg === '--trace' || arg === '--envelope') && next) {
      args.trace = next;
      i += 1;
    } else if (arg.startsWith('--trace=')) {
      args.trace = arg.slice(8);
    } else if (arg === '--trace-format' && next) {
      args.traceFormat = next;
      i += 1;
    } else if (arg.startsWith('--trace-format=')) {
      args.traceFormat = arg.slice(15);
    } else if (arg === '--trace-output' && next) {
      args.traceOutput = next;
      i += 1;
    } else if (arg.startsWith('--trace-output=')) {
      args.traceOutput = arg.slice(15);
    } else if (arg === '--trace-skip-replay' || arg === '--trace-no-replay') {
      args.traceSkipReplay = true;
    } else if ((arg === '--from-envelope' || arg === '--from') && next) {
      args.fromEnvelope = next;
      i += 1;
    } else if (arg.startsWith('--from-envelope=')) {
      args.fromEnvelope = arg.slice(16);
    } else {
      args._.push(arg);
    }
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/formal/verify-conformance.mjs [options]

Options:
  -i, --in <file>                Input events JSON (default: samples/conformance/sample-traces.json)
  --schema <file>                Trace schema YAML (default: observability/trace-schema.yaml)
  --out <file>                   Output summary JSON (default: hermetic-reports/conformance/summary.json)
  --from-envelope <file>         Load summary / trace metadata from report envelope JSON
  --disable-invariants <list>    Comma-separated invariants to disable (allocated_le_onhand,onhand_min)
  --onhand-min <number>          Minimum onHand for onhand_min invariant (default: 0)
  --trace <file>                 KvOnce trace (NDJSON or OTLP JSON) to project/validate
  --trace-format <fmt>           Trace format (ndjson|otlp|auto, default auto)
  --trace-output <dir>           Trace artifacts output directory (default: hermetic-reports/trace)
  --trace-skip-replay            Skip TLC replay step
  -h, --help                     Show this help
`);
}

function runProcess(command, args, options = {}) {
  return new Promise((resolve) => {
    const child = spawn(command, args, {
      cwd: options.cwd ?? repoRoot,
      env: { ...process.env, ...options.env },
      stdio: ['inherit', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    child.stdout.on('data', (data) => {
      stdout += data.toString();
      if (!options.quiet) process.stdout.write(data);
    });
    child.stderr.on('data', (data) => {
      stderr += data.toString();
      if (!options.quiet) process.stderr.write(data);
    });
    child.on('close', (code) => {
      resolve({ code: code ?? 0, stdout, stderr });
    });
  });
}

async function ensureNdjson(tracePath, format, outputDir) {
  const resolvedTrace = path.resolve(repoRoot, tracePath);
  const resolvedOutputDir = path.resolve(repoRoot, outputDir ?? DEFAULT_TRACE_DIR);
  fs.mkdirSync(resolvedOutputDir, { recursive: true });
  let finalFormat = format && format !== 'auto' ? format : undefined;
  if (!finalFormat) {
    finalFormat = resolvedTrace.endsWith('.ndjson') ? 'ndjson' : 'otlp';
  }
  const ndjsonPath = path.join(resolvedOutputDir, 'kvonce-events.ndjson');

  if (finalFormat === 'otlp') {
    const convertScript = path.join(repoRoot, 'scripts', 'trace', 'convert-otlp-kvonce.mjs');
    const result = await runProcess(process.execPath, [convertScript, '--input', resolvedTrace, '--output', ndjsonPath]);
    if (result.code === 2) {
      return { status: 'no_events', format: finalFormat };
    }
    if (result.code !== 0) {
      const stderr = result.stderr?.trim();
      const hint = stderr ? `: ${stderr}` : '';
      throw new Error(`convert-otlp-kvonce.mjs failed (exit ${result.code})${hint}`);
    }
    return { status: 'ok', format: finalFormat, ndjsonPath, sourcePath: ndjsonPath };
  }
  if (finalFormat === 'ndjson') {
    const resolvedNdjson = path.resolve(repoRoot, ndjsonPath);
    if (resolvedTrace !== resolvedNdjson) {
      fs.copyFileSync(resolvedTrace, resolvedNdjson);
    }
    return { status: 'ok', format: finalFormat, ndjsonPath: resolvedNdjson, sourcePath: resolvedNdjson };
  }
  throw new Error(`Unsupported trace format: ${finalFormat}`);
}

async function runTracePipeline({ tracePath, format, outputDir, skipReplay }) {
  const summary = {
    input: path.relative(repoRoot, path.resolve(repoRoot, tracePath)),
    outputDir: path.relative(repoRoot, path.resolve(repoRoot, outputDir ?? DEFAULT_TRACE_DIR)),
    format: format || 'auto',
    status: 'pending',
  };

  if (!fs.existsSync(path.resolve(repoRoot, tracePath))) {
    summary.status = 'missing_input';
    return summary;
  }

  try {
    const ensured = await ensureNdjson(tracePath, format, outputDir);
    if (ensured.status === 'no_events') {
      summary.status = 'no_events';
      return summary;
    }
    summary.format = ensured.format;
    summary.ndjson = path.relative(repoRoot, ensured.ndjsonPath);

    const targetDir = path.resolve(repoRoot, outputDir ?? DEFAULT_TRACE_DIR);
    const projectionPath = path.join(targetDir, 'kvonce-projection.json');
    const validationPath = path.join(targetDir, 'kvonce-validation.json');

    const projectorScript = path.join(repoRoot, 'scripts', 'trace', 'projector-kvonce.mjs');
    const projectorResult = await runProcess(process.execPath, [projectorScript, '--input', ensured.sourcePath, '--output', projectionPath]);
    if (projectorResult.code !== 0) {
      summary.status = 'projection_failed';
      const stderr = projectorResult.stderr?.trim();
      summary.projection = stderr ? { exitCode: projectorResult.code, stderr } : { exitCode: projectorResult.code };
      return summary;
    }
    const projection = JSON.parse(fs.readFileSync(projectionPath, 'utf8'));
    summary.projection = {
      path: path.relative(repoRoot, projectionPath),
      events: projection.eventCount ?? (Array.isArray(projection.events) ? projection.events.length : 0),
      keys: Object.keys(projection.perKey ?? {}).length,
    };
    if (projection.stats) {
      summary.projection.stats = projection.stats;
      if (typeof projection.stats.stateSequenceLength === 'number') {
        summary.projection.stateSequenceLength = projection.stats.stateSequenceLength;
      }
    }
    const stateOutput = projection.outputs?.stateSequence;
    if (stateOutput) {
      summary.projection.stateSequence = stateOutput;
    } else if (Array.isArray(projection.stateSequence)) {
      const projectedDir = path.join(targetDir, 'projected');
      fs.mkdirSync(projectedDir, { recursive: true });
      const sequencePath = path.join(projectedDir, 'kvonce-state-sequence.json');
      fs.writeFileSync(sequencePath, JSON.stringify(projection.stateSequence, null, 2));
      summary.projection.stateSequence = path.relative(repoRoot, sequencePath);
    }

    const validatorScript = path.join(repoRoot, 'scripts', 'trace', 'validate-kvonce.mjs');
    const validatorResult = await runProcess(process.execPath, [validatorScript, '--input', projectionPath, '--output', validationPath]);
    const validation = JSON.parse(fs.readFileSync(validationPath, 'utf8'));
    summary.validation = {
      path: path.relative(repoRoot, validationPath),
      exitCode: validatorResult.code,
      valid: Boolean(validation.valid),
      issues: Array.isArray(validation.issues) ? validation.issues.length : 0,
    };
    if (validatorResult.code !== 0) {
      summary.status = 'validation_failed';
      return summary;
    }
    if (!summary.validation.valid) {
      summary.status = 'invalid';
    } else {
      summary.status = 'valid';
    }

    if (!skipReplay) {
      const tlcResult = await runProcess('pnpm', ['run', 'spec:kv-once:tlc']);
      summary.replay = {
        exitCode: tlcResult.code,
        status: tlcResult.code === 0 ? 'ran' : 'failed',
      };
      const tlaSummaryPath = path.join(repoRoot, 'hermetic-reports', 'formal', 'tla-summary.json');
      if (fs.existsSync(tlaSummaryPath)) {
        const replayTarget = path.join(targetDir, 'tla-summary.json');
        fs.copyFileSync(tlaSummaryPath, replayTarget);
        summary.replay.summaryPath = path.relative(repoRoot, replayTarget);
        try {
          const tlaSummary = JSON.parse(fs.readFileSync(replayTarget, 'utf8'));
          summary.replay.status = tlaSummary.status ?? summary.replay.status;
          summary.replay.engine = tlaSummary.engine;
        } catch (error) {
          summary.replay.summaryError = error.message;
        }
      }
    } else {
      summary.replay = { status: 'skipped' };
    }

    const traceIds = collectTraceIdsFromNdjson(ensured.ndjsonPath);
    if (traceIds.length > 0) {
      summary.traceIds = traceIds;
    }
    const tempoLinks = buildTempoLinks(traceIds);
    if (tempoLinks.length > 0) {
      summary.tempoLinks = tempoLinks;
    }
  } catch (error) {
    summary.status = 'error';
    summary.error = error.message;
  }

  return summary;
}

function appendStepSummary(summary) {
  const lines = [
    `- events: ${summary.events ?? 'n/a'}`,
    `- schema errors: ${summary.schemaErrors ?? 'n/a'}`,
    `- invariant violations: ${summary.invariantViolations ?? 'n/a'}`,
  ];
  if (summary.trace) {
    lines.push('- trace:');
    lines.push(`  - status: ${summary.trace.status}`);
    if (summary.trace.validation) {
      lines.push(`  - validation: valid=${summary.trace.validation.valid} issues=${summary.trace.validation.issues}`);
    }
    if (summary.trace.replay) {
      lines.push(`  - replay: ${summary.trace.replay.status}`);
    }

    const traceIds = Array.isArray(summary.trace.traceIds)
      ? summary.trace.traceIds
      : Array.isArray(summary.traceIds)
        ? summary.traceIds
        : [];
    if (traceIds.length > 0) {
      lines.push(`  - trace ids: ${traceIds.join(', ')}`);
    }

    const artifactsUrl = (() => {
      const server = process.env.GITHUB_SERVER_URL ?? 'https://github.com';
      const repo = process.env.GITHUB_REPOSITORY;
      const runId = process.env.GITHUB_RUN_ID;
      if (!repo || !runId) return null;
      return `${server}/${repo}/actions/runs/${runId}?check_suite_focus=true#artifacts`;
    })();

    const formatArtifact = (label, value) => {
      if (!value) return null;
      if (artifactsUrl) {
        return `    - ${label}: \`${value}\` ([Artifacts](${artifactsUrl}))`;
      }
      return `    - ${label}: ${value}`;
    };

    const artifactLines = [];
    const ndjsonPath = summary.trace.ndjson ?? summary.ndjson;
    if (ndjsonPath) artifactLines.push(formatArtifact('ndjson', ndjsonPath));
    if (summary.projection?.path) artifactLines.push(formatArtifact('projection', summary.projection.path));
    if (summary.projection?.stateSequence) artifactLines.push(formatArtifact('state sequence', summary.projection.stateSequence));
    if (summary.validation?.path) artifactLines.push(formatArtifact('validation', summary.validation.path));
    if (summary.replay?.summaryPath) artifactLines.push(formatArtifact('replay summary', summary.replay.summaryPath));
    const renderedArtifacts = artifactLines.filter(Boolean);
    if (renderedArtifacts.length > 0) {
      lines.push('  - artifacts:');
      lines.push(...renderedArtifacts);
    }

    const tempoLinks = Array.isArray(summary.tempoLinks) && summary.tempoLinks.length > 0
      ? summary.tempoLinks
      : buildTempoLinks(traceIds);
    if (tempoLinks.length > 0) {
      lines.push('  - tempo links:');
      tempoLinks.forEach((link) => {
        lines.push(`    - ${link}`);
      });
    }
  }
  appendSection('Verify Conformance', lines);
}

async function main() {
  const args = parseArgs(process.argv);
  if (args.help) {
    printHelp();
    return;
  }

  const schemaPath = path.resolve(repoRoot, args.schema || path.join('observability', 'trace-schema.yaml'));
  const dataPath = path.resolve(repoRoot, args.in || path.join('samples', 'conformance', 'sample-traces.json'));
  const envelopePath = args.fromEnvelope ? path.resolve(repoRoot, args.fromEnvelope) : null;
  const outFile = path.resolve(repoRoot, args.out || path.join('hermetic-reports', 'conformance', 'summary.json'));

  if (envelopePath && !fs.existsSync(envelopePath)) {
    console.error(`Envelope not found: ${envelopePath}`);
    process.exit(1);
  }

  if (envelopePath && (args.trace || args.traceFormat || args.traceOutput || args.traceSkipReplay)) {
    console.warn('[verify:conformance] ignoring --trace options because --from-envelope was provided');
  }

  let summary;

  if (envelopePath) {
    const envelope = readJson(envelopePath);
    if (!envelope || typeof envelope !== 'object' || typeof envelope.summary !== 'object') {
      throw new Error(`Envelope ${envelopePath} does not contain summary field`);
    }
    summary = { ...envelope.summary };
    summary.envelopePath = path.relative(repoRoot, envelopePath);
    summary.timestamp = summary.timestamp ?? new Date().toISOString();
    if (!summary.input) {
      summary.input = '(from envelope)';
    }
  } else {
    const haveSchema = fs.existsSync(schemaPath);
    const haveData = fs.existsSync(dataPath);
    if (!haveSchema) {
      console.error(`Schema not found: ${schemaPath}`);
    }
    if (!haveData) {
      console.error(`Data not found: ${dataPath}`);
    }

    const disableList = (args.disable || '').split(',').map((s) => s.trim()).filter(Boolean);
    const disableSet = new Set(disableList);
    const onhandMin = Number.isFinite(Number(args.onhandMin)) ? Number(args.onhandMin) : 0;
    const missingNotes = [];
    if (!haveSchema) missingNotes.push('schema missing');
    if (!haveData) missingNotes.push('input data missing');

    if (haveSchema && haveData) {
      const schema = readYaml(schemaPath);
      const data = readJson(dataPath);
      const events = Array.isArray(data) ? data : [data];

    const ajv = new Ajv({ allErrors: true, strict: false });
    addFormats(ajv);
    const schemaConfig = {
      $id: 'TraceEvent',
      type: 'object',
      properties: schema.properties || {},
      required: schema.required || [],
      additionalProperties: true,
    };
    if (schema.definitions) {
      schemaConfig.definitions = schema.definitions;
    }
    if (schema.$defs) {
      schemaConfig.$defs = schema.$defs;
    }
    const validate = ajv.compile(schemaConfig);

    const schemaErrors = [];
    const invariantViolations = [];
    const byType = { onhand_min: 0, allocated_le_onhand: 0 };

    for (let i = 0; i < events.length; i += 1) {
      const ev = events[i];
      const ok = validate(ev);
      if (!ok) {
        for (const err of validate.errors || []) {
          schemaErrors.push({ index: i, path: err.instancePath, message: err.message });
        }
      }
      const st = ev && ev.state;
      if (st && typeof st === 'object') {
        const hasOnHand = typeof st.onHand === 'number';
        const hasAllocated = typeof st.allocated === 'number';
        if (!disableSet.has('onhand_min') && hasOnHand && st.onHand < onhandMin) {
          invariantViolations.push({ index: i, type: 'onhand_min', invariant: `onHand >= ${onhandMin}`, actual: st.onHand });
          byType.onhand_min += 1;
        }
        if (!disableSet.has('allocated_le_onhand') && hasOnHand && hasAllocated && st.allocated > st.onHand) {
          invariantViolations.push({ index: i, type: 'allocated_le_onhand', invariant: 'allocated <= onHand', actual: { allocated: st.allocated, onHand: st.onHand } });
          byType.allocated_le_onhand += 1;
        }
      }
    }

      const totalEvents = events.length || 0;
      const invCount = invariantViolations.length;
      const violationRate = totalEvents > 0 ? +(invCount / totalEvents).toFixed(3) : 0;
      const details = { schemaErrors, invariantViolations, options: { disable: disableList, onhandMin } };
      if (missingNotes.length) details.notes = missingNotes;
      summary = {
        input: path.relative(repoRoot, dataPath),
        events: totalEvents,
        schemaErrors: schemaErrors.length,
        invariantViolations: invCount,
        violationRate,
        timestamp: new Date().toISOString(),
        firstInvariantViolation: invariantViolations[0] || null,
        firstSchemaError: schemaErrors[0] || null,
        byType,
        details,
      };
    } else {
      const details = { schemaErrors: [], invariantViolations: [], options: { disable: disableList, onhandMin } };
      if (missingNotes.length) details.notes = missingNotes;
      summary = {
        input: haveData ? path.relative(repoRoot, dataPath) : '(missing)',
        events: 0,
        schemaErrors: 0,
        invariantViolations: 0,
        violationRate: 0,
        timestamp: new Date().toISOString(),
        firstInvariantViolation: null,
        firstSchemaError: null,
        byType: { onhand_min: 0, allocated_le_onhand: 0 },
        details,
      };
    }

    if (args.trace) {
      summary.trace = await runTracePipeline({
        tracePath: args.trace,
        format: args.traceFormat,
        outputDir: args.traceOutput,
        skipReplay: Boolean(args.traceSkipReplay),
      });
    }
  }

  writeJson(outFile, summary);
  console.log(`Conformance summary written: ${path.relative(repoRoot, outFile)}`);
  if (envelopePath) {
    console.log(`- envelope=${summary.envelopePath}`);
  } else {
    console.log(`- input=${summary.input} schema=${path.relative(repoRoot, schemaPath)}`);
    console.log(`- events=${summary.events} schemaErrors=${summary.schemaErrors} invariantViolations=${summary.invariantViolations}`);
  }
  if (summary.trace) {
    const outputInfo = summary.trace.outputDir ? ` (output=${summary.trace.outputDir})` : '';
    console.log(`- trace status=${summary.trace.status}${outputInfo}`);
  }

  appendStepSummary(summary);
}

main()
  .then(() => {
    process.exit(0);
  })
  .catch((error) => {
    console.error('[verify:conformance] unexpected error', error);
    process.exit(1);
  });
