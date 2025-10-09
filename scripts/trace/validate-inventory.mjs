#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const opts = {
    input: null,
    output: null,
    state: null,
    onhandMin: 0,
    disable: new Set(),
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    switch (arg) {
      case '--input':
      case '-i':
        if (!next) {
          console.error('[inventory-validate] --input requires a value');
          process.exit(1);
        }
        opts.input = next;
        i += 1;
        break;
      case '--output':
      case '-o':
        if (!next) {
          console.error('[inventory-validate] --output requires a value');
          process.exit(1);
        }
        opts.output = next;
        i += 1;
        break;
      case '--state':
        if (!next) {
          console.error('[inventory-validate] --state requires a value');
          process.exit(1);
        }
        opts.state = next;
        i += 1;
        break;
      case '--onhand-min':
        if (!next) {
          console.error('[inventory-validate] --onhand-min requires a value');
          process.exit(1);
        }
        opts.onhandMin = Number(next);
        if (!Number.isFinite(opts.onhandMin)) {
          console.error(`[inventory-validate] invalid number for --onhand-min: ${next}`);
          process.exit(1);
        }
        i += 1;
        break;
      case '--disable':
        if (!next) {
          console.error('[inventory-validate] --disable requires a value');
          process.exit(1);
        }
        next
          .split(',')
          .map((value) => value.trim())
          .filter(Boolean)
          .forEach((value) => opts.disable.add(value));
        i += 1;
        break;
      case '--help':
      case '-h':
        console.log(`Usage: node scripts/trace/validate-inventory.mjs --input <projection.json> [options]

Options:
  -i, --input <file>        Projection JSON output from projector-inventory (required)
  -o, --output <file>       Validation report JSON (default: stdout)
      --state <file>        Optional state sequence JSON. If omitted, uses projection.stateSequence or outputs.stateSequence.
      --onhand-min <num>    Minimum allowed onHand (default: 0)
      --disable <list>      Comma-separated invariant ids to skip (allocated_le_onhand,onhand_min,available_consistency)
  -h, --help                Show this help message
`);
        process.exit(0);
        break;
      default:
        console.error(`[inventory-validate] unknown argument: ${arg}`);
        process.exit(1);
    }
  }

  if (!opts.input) {
    console.error('Usage: validate-inventory --input <projection.json> [options]');
    process.exit(1);
  }

  return opts;
}

function readJson(file, fatal = true) {
  try {
    return JSON.parse(fs.readFileSync(file, 'utf8'));
  } catch (error) {
    if (!fatal) return null;
    console.error(`[inventory-validate] failed to read ${file}: ${error.message}`);
    process.exit(1);
  }
}

function resolveStateSequence(projection, opts) {
  if (opts.state) {
    const resolved = path.resolve(opts.state);
    if (!fs.existsSync(resolved)) {
      console.error(`[inventory-validate] state sequence file not found: ${resolved}`);
      process.exit(1);
    }
    return { sequence: readJson(resolved), source: resolved };
  }

  if (Array.isArray(projection?.stateSequence)) {
    return { sequence: projection.stateSequence, source: 'projection.stateSequence' };
  }

  const outputPath = projection?.outputs?.stateSequence;
  if (outputPath && typeof outputPath === 'string') {
    const resolved = path.resolve(outputPath);
    if (fs.existsSync(resolved)) {
      return { sequence: readJson(resolved), source: resolved };
    }
  }

  return { sequence: [], source: null };
}

function asNumber(value) {
  const num = Number(value);
  return Number.isFinite(num) ? num : null;
}

function checkState(state, context, config) {
  const issues = [];
  const onHand = asNumber(state?.onHand);
  const allocated = asNumber(state?.allocated);
  const available = asNumber(state?.available);
  const ctx = {};
  if (context.index != null) ctx.index = context.index;
  if (context.source) ctx.source = context.source;

  const addIssue = (type, message, severity = 'error') => {
    issues.push({ type, message, severity, ...ctx });
  };

  if (!config.disable.has('allocated_le_onhand')) {
    if (onHand == null || allocated == null) {
      addIssue('allocated_le_onhand:data_missing', 'allocated/onHand missing for invariant check', 'warning');
    } else if (allocated > onHand) {
      addIssue('allocated_le_onhand', `allocated ${allocated} exceeds onHand ${onHand}`);
    }
  }

  if (!config.disable.has('onhand_min')) {
    if (onHand == null) {
      addIssue('onhand_min:data_missing', 'onHand missing for minimum check', 'warning');
    } else if (onHand < config.onhandMin) {
      addIssue('onhand_min', `onHand ${onHand} below minimum ${config.onhandMin}`);
    }
  }

  if (!config.disable.has('available_consistency')) {
    if (onHand != null && allocated != null) {
      const expected = onHand - allocated;
      if (available != null && Math.abs(expected - available) > 1e-9) {
        addIssue('available_consistency', `available ${available} inconsistent with onHand - allocated = ${expected}`);
      }
    }
  }

  return issues;
}

function buildReport(projection, stateInfo, config) {
  const issues = [];
  const checks = new Set();

  const addIssues = (list) => {
    for (const issue of list) issues.push(issue);
  };

  const finalStateIssues = checkState(projection?.finalState ?? {}, { source: 'finalState' }, config);
  checks.add('finalState');
  addIssues(finalStateIssues);

  const stateSequence = Array.isArray(stateInfo.sequence) ? stateInfo.sequence : [];
  if (stateSequence.length > 0) {
    checks.add('stateSequence');
  }
  stateSequence.forEach((entry, index) => {
    const seqIssues = checkState(entry?.state ?? entry, { index, source: stateInfo.source ?? 'stateSequence' }, config);
    addIssues(seqIssues);
  });

  if (Array.isArray(projection?.orders)) {
    checks.add('orders');
    projection.orders.forEach((order) => {
      if (!order || typeof order !== 'object') return;
      const key = order.key ?? 'unknown';
      const net = asNumber(order.netAllocated);
      if (net != null && net < 0) {
        issues.push({ type: 'order_net_negative', message: `order ${key} netAllocated ${net} below zero`, severity: 'warning' });
      }
      const released = asNumber(order.totalReleased);
      const allocated = asNumber(order.totalAllocated);
      if (released != null && allocated != null && released > allocated + 1e-9) {
        issues.push({ type: 'order_released_gt_allocated', message: `order ${key} released ${released} exceeds allocated ${allocated}`, severity: 'warning' });
      }
    });
  }

  const validationEvents = projection?.validation?.events;
  if (Array.isArray(validationEvents)) {
    checks.add('embeddedValidation');
    validationEvents.forEach((entry) => {
      const result = typeof entry?.result === 'string' ? entry.result.toLowerCase() : 'unknown';
      const context = {};
      if (entry?.index != null) context.index = entry.index;
      context.source = 'validation.events';
      if (result !== 'pass') {
        issues.push({ type: 'validation_event_result', message: `validation result=${result}`, severity: 'error', ...context });
      }
      if (Array.isArray(entry?.failures)) {
        entry.failures.forEach((name) => {
          issues.push({ type: 'validation_event_failure', message: `validation failure: ${name}`, severity: 'error', ...context });
        });
      }
    });
  } else if (projection?.validation?.failures > 0) {
    checks.add('embeddedValidation');
    issues.push({ type: 'validation_summary_failures', message: `validation failures reported: ${projection.validation.failures}`, severity: 'error' });
  } else if (projection?.validation) {
    checks.add('embeddedValidation');
  }

  const report = {
    schemaVersion: 'inventory/validation/v1',
    generatedAt: new Date().toISOString(),
    valid: issues.some((item) => item.severity === 'error') ? false : true,
    issues,
    config: {
      onhandMin: config.onhandMin,
      disabled: Array.from(config.disable),
      stateSequenceSource: stateInfo.source,
    },
    metrics: {
      statesChecked: stateSequence.length + 1,
      checksRun: Array.from(checks),
    },
    traceIds: Array.isArray(projection?.traceIds) ? projection.traceIds : [],
    finalState: projection?.finalState ?? null,
  };

  return report;
}

const opts = parseArgs(process.argv);
const projection = readJson(opts.input);
const stateInfo = resolveStateSequence(projection, opts);
const config = {
  onhandMin: Number.isFinite(opts.onhandMin) ? opts.onhandMin : 0,
  disable: opts.disable,
};

const report = buildReport(projection, stateInfo, config);
const json = JSON.stringify(report, null, 2);

if (opts.output) {
  fs.mkdirSync(path.dirname(opts.output), { recursive: true });
  fs.writeFileSync(opts.output, json);
} else {
  process.stdout.write(json);
}

if (!report.valid) {
  process.exitCode = 1;
}
