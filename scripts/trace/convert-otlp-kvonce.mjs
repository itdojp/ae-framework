#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const EXIT_NO_EVENTS = 2;
const NANOS_PER_MILLI = 1_000_000n;

function parseArgs() {
  const args = process.argv.slice(2);
  const result = { input: null, output: null };
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if ((arg === '--input' || arg === '-i') && args[i + 1]) {
      result.input = args[++i];
    } else if ((arg === '--output' || arg === '-o') && args[i + 1]) {
      result.output = args[++i];
    }
  }
  if (!result.input) {
    console.error('Usage: convert-otlp-kvonce --input <otlp.json> [--output <ndjson>]');
    process.exit(1);
  }
  return result;
}

function readOtlp(file) {
  try {
    const content = fs.readFileSync(file, 'utf8');
    return JSON.parse(content);
  } catch (error) {
    throw new Error(`Failed to read OTLP payload: ${error.message}`);
  }
}

function extractAttributeValue(value) {
  if (value == null || typeof value !== 'object') return value;
  if ('stringValue' in value) return value.stringValue;
  if ('intValue' in value) return Number(value.intValue);
  if ('doubleValue' in value) return value.doubleValue;
  if ('boolValue' in value) return value.boolValue;
  if ('arrayValue' in value && Array.isArray(value.arrayValue?.values)) {
    return value.arrayValue.values.map(extractAttributeValue);
  }
  if ('mapValue' in value && Array.isArray(value.mapValue?.fields)) {
    return Object.fromEntries(
      value.mapValue.fields.map(({ key, value: v }) => [key, extractAttributeValue(v)])
    );
  }
  // Unknown OTLP attribute value types fall back to undefined so callers can
  // decide whether the attribute is optional or should trigger validation.
  for (const key of Object.keys(value)) {
    if (value[key] != null) {
      return value[key];
    }
  }
  return undefined;
}

function attrsToRecord(attributes = []) {
  const record = {};
  for (const attr of attributes || []) {
    record[attr.key] = extractAttributeValue(attr.value);
  }
  return record;
}

function toTimestamp(nanoString) {
  if (!nanoString) return new Date().toISOString();
  try {
    const nanos = BigInt(nanoString);
    const millisBigInt = nanos / NANOS_PER_MILLI;
    const max = BigInt(Number.MAX_SAFE_INTEGER);
    const min = BigInt(Number.MIN_SAFE_INTEGER);
    if (millisBigInt > max || millisBigInt < min) {
      return new Date().toISOString();
    }
    const millis = Number(millisBigInt);
    return new Date(millis).toISOString();
  } catch (error) {
    return new Date().toISOString();
  }
}

function extractEvents(otlp) {
  const events = [];
  for (const resourceSpan of otlp?.resourceSpans || []) {
    for (const scopeSpan of resourceSpan.scopeSpans || []) {
      for (const span of scopeSpan.spans || []) {
        const attrs = attrsToRecord(span.attributes);
        const type = attrs['kvonce.event.type'];
        const key = attrs['kvonce.event.key'];
        if (!type || !key) continue;
        const event = {
          timestamp: toTimestamp(span.startTimeUnixNano),
          type,
          key,
        };
        if (attrs['kvonce.event.value'] !== undefined) {
          event.value = attrs['kvonce.event.value'];
        }
        if (attrs['kvonce.event.reason'] !== undefined) {
          event.reason = attrs['kvonce.event.reason'];
        }
        if (attrs['kvonce.event.context'] !== undefined) {
          event.context = attrs['kvonce.event.context'];
        }
        events.push(event);
      }
    }
  }
  return events;
}

function toNdjson(events) {
  if (events.length === 0) {
    return '';
  }
  return events.map((event) => JSON.stringify(event)).join('\n') + '\n';
}

const { input, output } = parseArgs();
const otlp = readOtlp(input);
const events = extractEvents(otlp);

if (events.length === 0) {
  console.error('No kvonce events found in OTLP payload.');
  process.exit(EXIT_NO_EVENTS);
}

const ndjson = toNdjson(events);
if (output) {
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, ndjson, 'utf8');
} else {
  process.stdout.write(ndjson);
}
