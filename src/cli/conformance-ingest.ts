import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { toMessage } from '../utils/error-utils.js';

export type TraceRedactionAction = 'remove' | 'mask' | 'hash';

export interface TraceRedactionRule {
  jsonPath: string;
  action: TraceRedactionAction;
}

export interface ParsedTraceRedactionRule {
  ok: boolean;
  rule?: TraceRedactionRule;
  error?: string;
}

export interface ConformanceIngestOptions {
  inputPath: string;
  outputPath: string;
  summaryOutputPath: string;
  sourceEnv?: string;
  sourceService?: string;
  sourceTimeStart?: string;
  sourceTimeEnd?: string;
  sourceBuildId?: string;
  sourceGitSha?: string;
  sampleRate?: number;
  maxEvents?: number;
  redactRules?: TraceRedactionRule[];
}

interface TraceEventRecord {
  traceId: string;
  timestamp: string;
  actor: string;
  event: string;
  [key: string]: unknown;
}

interface TraceBundle {
  schemaVersion: 'ae-trace-bundle/v1';
  generatedAt: string;
  source: {
    environment: string;
    service: string;
    buildId?: string;
    gitSha?: string;
    input: {
      path: string;
      format: 'ndjson' | 'json-array' | 'json-events';
    };
    timeWindow: {
      start: string;
      end: string;
    };
  };
  events: TraceEventRecord[];
  grouping: {
    by: 'traceId';
    traceCount: number;
    traces: Array<{
      traceId: string;
      eventCount: number;
      firstTimestamp: string;
      lastTimestamp: string;
    }>;
  };
  redaction: {
    rules: TraceRedactionRule[];
    redactedFieldCount: number;
  };
  summary: {
    rawEventCount: number;
    validEventCount: number;
    invalidEventCount: number;
    sampledOutCount: number;
    emittedEventCount: number;
  };
}

interface TraceBundleSummary {
  schemaVersion: 'ae-trace-bundle-summary/v1';
  generatedAt: string;
  input: {
    path: string;
    format: TraceBundle['source']['input']['format'];
  };
  output: {
    bundlePath: string;
    summaryPath: string;
  };
  counts: {
    rawEventCount: number;
    validEventCount: number;
    invalidEventCount: number;
    sampledOutCount: number;
    emittedEventCount: number;
    traceCount: number;
    redactedFieldCount: number;
  };
  sampling: {
    sampleRate: number;
    maxEvents: number;
  };
  redaction: {
    rules: TraceRedactionRule[];
  };
}

const REDACTION_MASK = '[REDACTED]';
const RFC3339_DATE_TIME =
  /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$/;

const toNormalizedSampleRate = (value: number | undefined): number => {
  if (!Number.isFinite(value)) {
    return 1;
  }
  return Math.min(1, Math.max(0, Number(value)));
};

const toNormalizedMaxEvents = (value: number | undefined): number => {
  if (!Number.isFinite(value) || Number(value) <= 0) {
    return 0;
  }
  return Math.trunc(Number(value));
};

const isPlainObject = (value: unknown): value is Record<string, unknown> =>
  typeof value === 'object' && value !== null && !Array.isArray(value);

const isNonEmptyString = (value: unknown): value is string =>
  typeof value === 'string' && value.trim().length > 0;

const toRelativePath = (filePath: string): string =>
  path.relative(process.cwd(), filePath) || '.';

const parseSimpleJsonPath = (jsonPath: string): string[] | null => {
  if (!jsonPath.startsWith('$.')) {
    return null;
  }
  const tokens = jsonPath.slice(2).split('.').map((segment) => segment.trim()).filter(Boolean);
  if (tokens.length === 0) {
    return null;
  }
  if (tokens.some((segment) => segment.includes('*') || segment.includes('[') || segment.includes(']'))) {
    return null;
  }
  return tokens;
};

const applyRedactionRule = (event: Record<string, unknown>, rule: TraceRedactionRule): number => {
  const pathTokens = parseSimpleJsonPath(rule.jsonPath);
  if (!pathTokens) {
    return 0;
  }

  let cursor: unknown = event;
  for (let index = 0; index < pathTokens.length - 1; index += 1) {
    const token = pathTokens[index];
    if (!token) {
      return 0;
    }
    if (!isPlainObject(cursor) || !(token in cursor)) {
      return 0;
    }
    cursor = cursor[token];
  }

  if (!isPlainObject(cursor)) {
    return 0;
  }

  const leaf = pathTokens[pathTokens.length - 1];
  if (!leaf) {
    return 0;
  }
  if (!(leaf in cursor)) {
    return 0;
  }

  if (rule.action === 'remove') {
    delete cursor[leaf];
    return 1;
  }

  if (rule.action === 'mask') {
    cursor[leaf] = REDACTION_MASK;
    return 1;
  }

  const digest = createHash('sha256').update(String(cursor[leaf])).digest('hex');
  cursor[leaf] = `sha256:${digest}`;
  return 1;
};

const toStableHashRatio = (event: TraceEventRecord): number => {
  const key = `${event.traceId}|${event.timestamp}|${event.actor}|${event.event}`;
  const digest = createHash('sha256').update(key).digest();
  const numerator = digest.readUInt32BE(0);
  return numerator / 0x1_0000_0000;
};

const toTimestampMs = (value: string): number => Date.parse(value);

const shouldKeepEvent = (event: TraceEventRecord, sampleRate: number): boolean => {
  if (sampleRate >= 1) {
    return true;
  }
  if (sampleRate <= 0) {
    return false;
  }
  return toStableHashRatio(event) < sampleRate;
};

const toSortedEvents = (events: TraceEventRecord[]): TraceEventRecord[] =>
  [...events].sort((left, right) => {
    const leftEpoch = toTimestampMs(left.timestamp);
    const rightEpoch = toTimestampMs(right.timestamp);
    if (leftEpoch !== rightEpoch) return leftEpoch - rightEpoch;
    const byTraceId = left.traceId.localeCompare(right.traceId);
    if (byTraceId !== 0) return byTraceId;
    return left.event.localeCompare(right.event);
  });

const parseEventRecord = (raw: unknown): TraceEventRecord | null => {
  if (!isPlainObject(raw)) {
    return null;
  }
  if (!isNonEmptyString(raw['traceId'])) return null;
  if (!isNonEmptyString(raw['timestamp'])) return null;
  if (!isNonEmptyString(raw['actor'])) return null;
  if (!isNonEmptyString(raw['event'])) return null;

  const timestamp = raw['timestamp'];
  if (!RFC3339_DATE_TIME.test(timestamp)) {
    return null;
  }

  const ts = new Date(timestamp);
  if (Number.isNaN(ts.getTime())) {
    return null;
  }

  return JSON.parse(JSON.stringify(raw)) as TraceEventRecord;
};

const parseNdjson = (content: string): unknown[] => {
  const rawLines = content.split('\n').map((line) => line.trim()).filter(Boolean);
  return rawLines.map((line, index) => {
    try {
      return JSON.parse(line);
    } catch (error: unknown) {
      throw new Error(`invalid NDJSON at line ${index + 1}: ${toMessage(error)}`);
    }
  });
};

const readRawEvents = (
  inputPath: string,
): { format: 'ndjson' | 'json-array' | 'json-events'; events: unknown[] } => {
  const content = readFileSync(inputPath, 'utf-8');
  const ext = path.extname(inputPath).toLowerCase();

  if (ext === '.ndjson') {
    return { format: 'ndjson', events: parseNdjson(content) };
  }

  const parsed = JSON.parse(content) as unknown;
  if (Array.isArray(parsed)) {
    return { format: 'json-array', events: parsed };
  }

  if (isPlainObject(parsed) && Array.isArray(parsed['events'])) {
    return { format: 'json-events', events: parsed['events'] };
  }

  throw new Error('input must be NDJSON, JSON array, or object with events[]');
};

const buildTraceGrouping = (events: TraceEventRecord[]): TraceBundle['grouping'] => {
  const stats = new Map<string, { eventCount: number; firstTimestamp: string; lastTimestamp: string }>();
  for (const event of events) {
    const current = stats.get(event.traceId);
    if (!current) {
      stats.set(event.traceId, {
        eventCount: 1,
        firstTimestamp: event.timestamp,
        lastTimestamp: event.timestamp,
      });
      continue;
    }

    current.eventCount += 1;
    if (toTimestampMs(event.timestamp) < toTimestampMs(current.firstTimestamp)) {
      current.firstTimestamp = event.timestamp;
    }
    if (toTimestampMs(event.timestamp) > toTimestampMs(current.lastTimestamp)) {
      current.lastTimestamp = event.timestamp;
    }
  }

  const traces = [...stats.entries()]
    .map(([traceId, entry]) => ({ traceId, ...entry }))
    .sort((left, right) => left.traceId.localeCompare(right.traceId));

  return {
    by: 'traceId',
    traceCount: traces.length,
    traces,
  };
};

const resolveTimeWindowFromSortedEvents = (
  events: TraceEventRecord[],
  sourceTimeStart?: string,
  sourceTimeEnd?: string,
): { start: string; end: string } => {
  const fallbackStart = events[0]?.timestamp ?? new Date(0).toISOString();
  const fallbackEnd = events[events.length - 1]?.timestamp ?? new Date(0).toISOString();
  return {
    start: sourceTimeStart || fallbackStart,
    end: sourceTimeEnd || fallbackEnd,
  };
};

const parseRedactionRule = (ruleSpec: string): ParsedTraceRedactionRule => {
  const separator = ruleSpec.lastIndexOf(':');
  if (separator <= 0 || separator === ruleSpec.length - 1) {
    return { ok: false, error: `invalid redaction rule "${ruleSpec}" (expected <jsonPath>:<action>)` };
  }
  const jsonPath = ruleSpec.slice(0, separator).trim();
  const action = ruleSpec.slice(separator + 1).trim() as TraceRedactionAction;
  if (!['remove', 'mask', 'hash'].includes(action)) {
    return { ok: false, error: `invalid redaction action "${action}" in "${ruleSpec}"` };
  }
  if (!parseSimpleJsonPath(jsonPath)) {
    return { ok: false, error: `unsupported redaction path "${jsonPath}" (supported: $.a.b.c)` };
  }
  return {
    ok: true,
    rule: { jsonPath, action },
  };
};

export const parseTraceRedactionRule = parseRedactionRule;

export const runConformanceIngest = (options: ConformanceIngestOptions): {
  bundle: TraceBundle;
  summary: TraceBundleSummary;
} => {
  const inputPath = path.resolve(options.inputPath);
  const outputPath = path.resolve(options.outputPath);
  const summaryOutputPath = path.resolve(options.summaryOutputPath);
  const sampleRate = toNormalizedSampleRate(options.sampleRate);
  const maxEvents = toNormalizedMaxEvents(options.maxEvents);
  const redactRules = options.redactRules ?? [];

  const { format, events: rawEvents } = readRawEvents(inputPath);
  const parsedEvents = rawEvents.map(parseEventRecord);
  const validEvents = parsedEvents.filter((event): event is TraceEventRecord => event !== null);
  const invalidEventCount = rawEvents.length - validEvents.length;

  const sampledEvents = validEvents.filter((event) => shouldKeepEvent(event, sampleRate));
  const sampledOutCount = validEvents.length - sampledEvents.length;
  const boundedEvents = maxEvents > 0 ? sampledEvents.slice(0, maxEvents) : sampledEvents;
  const sortedEvents = toSortedEvents(boundedEvents);

  let redactedFieldCount = 0;
  for (const event of sortedEvents) {
    redactedFieldCount += redactRules.reduce((count, rule) => count + applyRedactionRule(event, rule), 0);
  }

  const generatedAt = new Date().toISOString();
  const grouping = buildTraceGrouping(sortedEvents);
  const bundle: TraceBundle = {
    schemaVersion: 'ae-trace-bundle/v1',
    generatedAt,
    source: {
      environment: options.sourceEnv || 'unknown',
      service: options.sourceService || 'unknown',
      ...(options.sourceBuildId ? { buildId: options.sourceBuildId } : {}),
      ...(options.sourceGitSha ? { gitSha: options.sourceGitSha } : {}),
      input: {
        path: toRelativePath(inputPath),
        format,
      },
      timeWindow: resolveTimeWindowFromSortedEvents(sortedEvents, options.sourceTimeStart, options.sourceTimeEnd),
    },
    events: sortedEvents,
    grouping,
    redaction: {
      rules: redactRules,
      redactedFieldCount,
    },
    summary: {
      rawEventCount: rawEvents.length,
      validEventCount: validEvents.length,
      invalidEventCount,
      sampledOutCount,
      emittedEventCount: sortedEvents.length,
    },
  };

  const summary: TraceBundleSummary = {
    schemaVersion: 'ae-trace-bundle-summary/v1',
    generatedAt,
    input: {
      path: toRelativePath(inputPath),
      format,
    },
    output: {
      bundlePath: toRelativePath(outputPath),
      summaryPath: toRelativePath(summaryOutputPath),
    },
    counts: {
      rawEventCount: rawEvents.length,
      validEventCount: validEvents.length,
      invalidEventCount,
      sampledOutCount,
      emittedEventCount: sortedEvents.length,
      traceCount: grouping.traceCount,
      redactedFieldCount,
    },
    sampling: {
      sampleRate,
      maxEvents,
    },
    redaction: {
      rules: redactRules,
    },
  };

  mkdirSync(path.dirname(outputPath), { recursive: true });
  writeFileSync(outputPath, `${JSON.stringify(bundle, null, 2)}\n`);
  mkdirSync(path.dirname(summaryOutputPath), { recursive: true });
  writeFileSync(summaryOutputPath, `${JSON.stringify(summary, null, 2)}\n`);

  return { bundle, summary };
};
