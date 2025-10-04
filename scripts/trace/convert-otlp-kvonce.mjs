#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

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

function toJsValue(value) {
  if (!value || typeof value !== 'object') return undefined;
  if ('stringValue' in value) return value.stringValue;
  if ('boolValue' in value) return value.boolValue;
  if ('intValue' in value) return Number(value.intValue);
  if ('doubleValue' in value) return value.doubleValue;
  if ('arrayValue' in value) {
    return (value.arrayValue.values || []).map(toJsValue);
  }
  if ('mapValue' in value) {
    const map = {};
    for (const { key, value: v } of value.mapValue.fields || []) {
      map[key] = toJsValue(v);
    }
    return map;
  }
  return undefined;
}

function attrsToRecord(attributes = []) {
  const record = {};
  for (const attr of attributes) {
    record[attr.key] = toJsValue(attr.value);
  }
  return record;
}

function toTimestamp(nanoString) {
  if (!nanoString) return new Date().toISOString();
  try {
    const nanos = BigInt(nanoString);
    const millis = Number(nanos / 1000000n);
    return new Date(millis).toISOString();
  } catch (error) {
    return new Date().toISOString();
  }
}

function extractEvents(otlp) {
  const events = [];
  const resourceSpans = otlp?.resourceSpans || [];
  for (const resourceSpan of resourceSpans) {
    const scopeSpans = resourceSpan.scopeSpans || [];
    for (const scopeSpan of scopeSpans) {
      const spans = scopeSpan.spans || [];
      for (const span of spans) {
        const attrs = attrsToRecord(span.attributes);
        const type = attrs['kvonce.event.type'];
        const key = attrs['kvonce.event.key'];
        if (!type || !key) continue;
        const event = {
          timestamp: toTimestamp(span.startTimeUnixNano),
          type,
          key,
        };
        if (type === 'success') {
          if (attrs['kvonce.event.value'] !== undefined) {
            event.value = attrs['kvonce.event.value'];
          }
        }
        if (type === 'failure') {
          if (attrs['kvonce.event.reason'] !== undefined) {
            event.reason = attrs['kvonce.event.reason'];
          }
        }
        if (attrs['kvonce.event.context']) {
          event.context = attrs['kvonce.event.context'];
        }
        events.push(event);
      }
    }
  }
  return events;
}

function toNdjson(events) {
  return events.map((event) => JSON.stringify(event)).join('\n') + '\n';
}

const { input, output } = parseArgs();
const otlp = readOtlp(input);
const events = extractEvents(otlp);

if (events.length === 0) {
  console.error('No kvonce events found in OTLP payload.');
  process.exit(2);
}

const ndjson = toNdjson(events);
if (output) {
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, ndjson, 'utf8');
} else {
  process.stdout.write(ndjson);
}
