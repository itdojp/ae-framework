#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function parseArgs() {
  const args = process.argv.slice(2);
  const result = { input: null, output: null, stateOutput: null };
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if ((arg === '--input' || arg === '-i') && args[i + 1]) {
      result.input = args[++i];
    } else if ((arg === '--output' || arg === '-o') && args[i + 1]) {
      result.output = args[++i];
    } else if ((arg === '--state-output' || arg === '--states') && args[i + 1]) {
      result.stateOutput = args[++i];
    }
  }
  if (!result.input) {
    console.error('Usage: projector-kvonce --input <ndjson> [--output <json>] [--state-output <json>]');
    process.exit(1);
  }
  return result;
}

function readNdjson(file) {
  const content = fs.readFileSync(file, 'utf8');
  return content
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean)
    .map((line, index) => {
      try {
        return JSON.parse(line);
      } catch (error) {
        throw new Error(`Invalid JSON on line ${index + 1}: ${error.message}`);
      }
    });
}

function initialEntry() {
  return {
    successCount: 0,
    retries: 0,
    failureReasons: [],
    retryContexts: [],
    successContexts: [],
    failureContexts: [],
    value: null,
    firstTimestamp: null,
    lastTimestamp: null,
    lastType: null,
    lastFailureReason: null,
  };
}

function initialKeyState() {
  return {
    written: false,
    value: null,
    retries: 0,
    failures: 0,
    lastFailureReason: null,
    lastSuccessAt: null,
  };
}

function cloneStateMap(map) {
  return Object.fromEntries(
    Array.from(map.entries()).map(([key, value]) => [key, { ...value }]),
  );
}

function buildProjection(events) {
  const perKey = new Map();
  const stateByKey = new Map();
  const stateSequence = [];
  const notes = [];

  let successCount = 0;
  let retryCount = 0;
  let failureCount = 0;
  let unknownTypeCount = 0;

  const duplicateKeys = new Set();
  const failureKeys = new Set();

  events.forEach((event, index) => {
    const key = event.key ?? 'unknown';
    const type = event.type ?? 'unknown';
    if (!perKey.has(key)) {
      perKey.set(key, initialEntry());
    }
    const entry = perKey.get(key);
    if (!stateByKey.has(key)) {
      stateByKey.set(key, initialKeyState());
    }
    const keyState = stateByKey.get(key);

    entry.firstTimestamp ??= event.timestamp ?? null;
    if (event.timestamp) {
      entry.lastTimestamp = event.timestamp;
    }
    entry.lastType = type;

    switch (type) {
      case 'success':
        entry.successCount += 1;
        successCount += 1;
        entry.value = event.value ?? entry.value ?? null;
        if (event.context !== undefined) {
          entry.successContexts.push(event.context);
        }
        keyState.written = true;
        if (event.value !== undefined) {
          keyState.value = event.value;
        }
        keyState.lastSuccessAt = event.timestamp ?? keyState.lastSuccessAt;
        break;
      case 'retry':
        entry.retries += 1;
        retryCount += 1;
        if (event.context !== undefined) {
          entry.retryContexts.push(event.context);
        }
        keyState.retries += 1;
        break;
      case 'failure':
        failureCount += 1;
        failureKeys.add(key);
        entry.failureReasons.push(event.reason ?? 'unknown');
        if ((event.reason ?? '').toLowerCase() === 'duplicate') {
          duplicateKeys.add(key);
        }
        if (event.context !== undefined) {
          entry.failureContexts.push(event.context);
        }
        entry.lastFailureReason = event.reason ?? entry.lastFailureReason;
        keyState.failures += 1;
        keyState.lastFailureReason = event.reason ?? keyState.lastFailureReason;
        break;
      default:
        unknownTypeCount += 1;
        notes.push({ index, issue: 'unknown_event_type', type, key });
        break;
    }

    keyState.value ??= null;

    const storeSnapshot = cloneStateMap(stateByKey);
    const totals = {
      success: successCount,
      retry: retryCount,
      failure: failureCount,
    };

    stateSequence.push({
      index,
      timestamp: event.timestamp ?? null,
      type,
      key,
      event,
      store: storeSnapshot,
      totals,
    });
  });

  const stats = {
    totalEvents: events.length,
    uniqueKeys: perKey.size,
    byType: {
      success: successCount,
      retry: retryCount,
      failure: failureCount,
      unknown: unknownTypeCount,
    },
    keysWithSuccess: Array.from(perKey.entries()).filter(([, value]) => (value.successCount ?? 0) > 0).length,
    keysWithRetries: Array.from(perKey.entries()).filter(([, value]) => (value.retries ?? 0) > 0).length,
    keysWithFailures: failureKeys.size,
    duplicateFailureKeys: duplicateKeys.size,
  };
  stats.successRate = stats.totalEvents > 0 ? +(stats.byType.success / stats.totalEvents).toFixed(3) : 0;

  const projection = {
    schemaVersion: 'kvonce/v1',
    generatedAt: new Date().toISOString(),
    eventCount: events.length,
    events,
    perKey: Object.fromEntries(perKey.entries()),
    stats,
  };

  if (notes.length > 0) {
    projection.notes = notes;
  }

  return { projection, stateSequence };
}

const { input, output, stateOutput } = parseArgs();
const events = readNdjson(input);
const { projection, stateSequence } = buildProjection(events);

const resolvedStateOutput = stateOutput ? path.resolve(stateOutput) : null;
if (resolvedStateOutput) {
  fs.mkdirSync(path.dirname(resolvedStateOutput), { recursive: true });
  fs.writeFileSync(resolvedStateOutput, JSON.stringify(stateSequence, null, 2));
  projection.outputs = {
    ...(projection.outputs ?? {}),
    stateSequence: path.relative(process.cwd(), resolvedStateOutput),
  };
  projection.stats.stateSequenceLength = stateSequence.length;
} else {
  projection.stateSequence = stateSequence;
  projection.stats.stateSequenceLength = stateSequence.length;
}

const json = JSON.stringify(projection, null, 2);
if (output) {
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, json);
} else {
  process.stdout.write(json);
}
