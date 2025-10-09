#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function parseArgs() {
  const args = process.argv.slice(2);
  const opts = { input: null, output: null, stateOutput: null };
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    const next = args[i + 1];
    if ((arg === '--input' || arg === '-i') && next) {
      opts.input = next;
      i += 1;
    } else if ((arg === '--output' || arg === '-o') && next) {
      opts.output = next;
      i += 1;
    } else if ((arg === '--state-output' || arg === '--states') && next) {
      opts.stateOutput = next;
      i += 1;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node scripts/trace/projector-inventory.mjs --input <ndjson> [--output <json>] [--state-output <json>]

Options:
  -i, --input <file>          Inventory NDJSON trace (required)
  -o, --output <file>         Projection summary JSON (default: stdout)
      --state-output <file>   Detailed state sequence JSON
  -h, --help                  Show this message
`);
      process.exit(0);
    }
  }

  if (!opts.input) {
    console.error('Usage: projector-inventory --input <ndjson> [--output <json>] [--state-output <json>]');
    process.exit(1);
  }
  return opts;
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

const isNumber = (value) => typeof value === 'number' && Number.isFinite(value);

function initialState() {
  return { onHand: 0, allocated: 0, available: 0 };
}

function cloneState(state) {
  return {
    onHand: state.onHand ?? 0,
    allocated: state.allocated ?? 0,
    available: state.available ?? Math.max((state.onHand ?? 0) - (state.allocated ?? 0), 0),
  };
}

function normalizeState(state) {
  const next = cloneState(state);
  if (!isNumber(next.available)) {
    if (isNumber(next.onHand) && isNumber(next.allocated)) {
      next.available = next.onHand - next.allocated;
    } else {
      next.available = 0;
    }
  }
  return next;
}

function inferDelta(delta) {
  if (delta == null) return null;
  if (isNumber(delta)) return delta;
  if (typeof delta === 'object' && delta.allocated != null) {
    const value = Number(delta.allocated);
    return Number.isFinite(value) ? value : null;
  }
  return null;
}

function applyEvent(prevState, event) {
  const notes = [];
  let nextState = cloneState(prevState);

  const stateFromEvent = event && typeof event.state === 'object' ? event.state : null;
  if (stateFromEvent) {
    if (isNumber(stateFromEvent.onHand)) nextState.onHand = stateFromEvent.onHand;
    if (isNumber(stateFromEvent.allocated)) nextState.allocated = stateFromEvent.allocated;
    if (isNumber(stateFromEvent.available)) {
      nextState.available = stateFromEvent.available;
    }
  } else {
    const delta = inferDelta(event.delta);
    switch (event.type) {
      case 'projection':
        notes.push('projection_without_state');
        break;
      case 'allocation':
        if (delta != null) {
          nextState.allocated += delta;
        } else {
          notes.push('allocation_missing_delta');
        }
        break;
      case 'release':
        if (delta != null) {
          nextState.allocated += delta;
        } else {
          notes.push('release_missing_delta');
        }
        break;
      case 'validation':
        notes.push('validation_without_state');
        break;
      default:
        notes.push('unknown_event_without_state');
        break;
    }
  }

  if (!isNumber(nextState.available)) {
    nextState.available = nextState.onHand - nextState.allocated;
  }

  return { nextState: normalizeState(nextState), notes };
}

function buildProjection(events) {
  const traceIds = new Set();
  const stateSequence = [];
  const issues = [];
  const metrics = {
    projectionEvents: 0,
    allocationEvents: 0,
    releaseEvents: 0,
    validationEvents: 0,
  };

  let state = initialState();
  let firstTimestamp = null;
  let lastTimestamp = null;

  const orderSummaries = new Map();
  const validationResults = [];

  events.forEach((event, index) => {
    const type = event.type ?? 'unknown';
    const timestamp = event.timestamp ?? null;
    if (event.traceId) traceIds.add(event.traceId);

    if (timestamp && firstTimestamp == null) firstTimestamp = timestamp;
    if (timestamp) lastTimestamp = timestamp;

    if (type === 'projection') metrics.projectionEvents += 1;
    else if (type === 'allocation') metrics.allocationEvents += 1;
    else if (type === 'release') metrics.releaseEvents += 1;
    else if (type === 'validation') metrics.validationEvents += 1;

    const { nextState, notes } = applyEvent(state, event);

    if (notes.length > 0) {
      for (const note of notes) {
        issues.push({ index, type: note, key: event.key ?? null });
      }
    }

    if (type === 'allocation' || type === 'release') {
      const delta = inferDelta(event.delta);
      const key = event.key ?? 'unknown';
      const record = orderSummaries.get(key) ?? {
        key,
        allocationEvents: 0,
        releaseEvents: 0,
        totalAllocated: 0,
        totalReleased: 0,
        netAllocated: 0,
        lastTimestamp: null,
      };
      if (type === 'allocation') {
        record.allocationEvents += 1;
        if (delta != null) {
          record.totalAllocated += delta;
          record.netAllocated += delta;
        }
      } else if (type === 'release') {
        record.releaseEvents += 1;
        if (delta != null) {
          record.totalReleased += Math.abs(delta);
          record.netAllocated += delta;
        }
      }
      record.lastTimestamp = timestamp ?? record.lastTimestamp;
      orderSummaries.set(key, record);
    }

    if (type === 'validation') {
      const checks = event.checks && typeof event.checks === 'object' ? event.checks : {};
      const failures = Object.entries(checks)
        .filter(([, value]) => value === false)
        .map(([name]) => name);
      const result = (event.result ?? 'unknown').toLowerCase();
      validationResults.push({
        index,
        timestamp,
        key: event.key ?? null,
        result,
        failures,
        checks,
      });
      if (result !== 'pass') {
        issues.push({ index, type: 'validation_result', detail: result });
      }
      for (const failure of failures) {
        issues.push({ index, type: 'validation_failure', detail: failure });
      }
    }

    const timelineEntry = {
      index,
      traceId: event.traceId ?? null,
      timestamp,
      type,
      key: event.key ?? null,
      state: nextState,
    };
    if (event.delta !== undefined) timelineEntry.delta = event.delta;
    if (event.context !== undefined) timelineEntry.context = event.context;
    if (event.result !== undefined) timelineEntry.result = event.result;
    if (event.checks !== undefined) timelineEntry.checks = event.checks;

    stateSequence.push(timelineEntry);
    state = nextState;
  });

  const orders = Array.from(orderSummaries.values()).filter((order) => order.key && order.key !== 'inventory');
  orders.sort((a, b) => a.key.localeCompare(b.key));

  const projection = {
    schemaVersion: 'inventory/v1',
    generatedAt: new Date().toISOString(),
    eventCount: events.length,
    traceIds: Array.from(traceIds),
    metrics,
    finalState: state,
    orders,
    validation: {
      count: validationResults.length,
      passes: validationResults.filter((entry) => entry.result === 'pass').length,
      failures: validationResults.filter((entry) => entry.result !== 'pass').length,
      lastResult: validationResults.length > 0 ? validationResults[validationResults.length - 1] : null,
    },
    stats: {
      firstTimestamp,
      lastTimestamp,
      orderCount: orders.length,
    },
  };

  if (validationResults.length > 0) {
    projection.validation.events = validationResults;
  }
  if (issues.length > 0) {
    projection.issues = issues;
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
  projection.metrics.stateSequenceLength = stateSequence.length;
} else {
  projection.stateSequence = stateSequence;
  projection.metrics.stateSequenceLength = stateSequence.length;
}

const json = JSON.stringify(projection, null, 2);
if (output) {
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, json);
} else {
  process.stdout.write(json);
}
