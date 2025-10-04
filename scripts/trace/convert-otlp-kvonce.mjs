#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";

const EXIT_NO_EVENTS = 2;

function parseArgs() {
  const args = process.argv.slice(2);
  const result = { input: null, output: null };
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if ((arg === "--input" || arg === "-i") && args[i + 1]) {
      result.input = args[++i];
    } else if ((arg === "--output" || arg === "-o") && args[i + 1]) {
      result.output = args[++i];
    }
  }
  if (!result.input) {
    console.error("Usage: convert-otlp-kvonce --input <otlp.json> [--output <ndjson>]");
    process.exit(1);
  }
  return result;
}

function readOtlp(file) {
  try {
    const content = fs.readFileSync(file, "utf8");
    return JSON.parse(content);
  } catch (error) {
    throw new Error(`Failed to read OTLP payload: ${error.message}`);
  }
}

function extractAttributeValue(attrValue) {
  if (attrValue == null || typeof attrValue !== "object") {
    return attrValue;
  }
  if ("stringValue" in attrValue) return attrValue.stringValue;
  if ("intValue" in attrValue) return Number(attrValue.intValue);
  if ("doubleValue" in attrValue) return attrValue.doubleValue;
  if ("boolValue" in attrValue) return attrValue.boolValue;
  if ("arrayValue" in attrValue && Array.isArray(attrValue.arrayValue?.values)) {
    return attrValue.arrayValue.values.map(extractAttributeValue);
  }
  if ("mapValue" in attrValue && Array.isArray(attrValue.mapValue?.fields)) {
    return Object.fromEntries(
      attrValue.mapValue.fields.map(({ key, value }) => [key, extractAttributeValue(value)])
    );
  }
  for (const key of Object.keys(attrValue)) {
    if (attrValue[key] != null) {
      return attrValue[key];
    }
  }
  return undefined;
}

function attrsToRecord(attributes = []) {
  const record = {};
  for (const attribute of attributes || []) {
    record[attribute.key] = extractAttributeValue(attribute.value);
  }
  return record;
}

function toTimestamp(nanoString) {
  if (!nanoString) return new Date().toISOString();
  try {
    const nanos = BigInt(nanoString);
    const millisBigInt = nanos / 1_000_000n;
    if (millisBigInt > BigInt(Number.MAX_SAFE_INTEGER) || millisBigInt < BigInt(Number.MIN_SAFE_INTEGER)) {
      return new Date().toISOString();
    }
    return new Date(Number(millisBigInt)).toISOString();
  } catch {
    return new Date().toISOString();
  }
}

function extractEvents(otlp) {
  const events = [];
  for (const resourceSpan of otlp?.resourceSpans || []) {
    for (const scopeSpan of resourceSpan.scopeSpans || []) {
      for (const span of scopeSpan.spans || []) {
        const attrs = attrsToRecord(span.attributes);
        const type = attrs["kvonce.event.type"];
        const key = attrs["kvonce.event.key"];
        if (!type || !key) continue;
        const event = {
          timestamp: toTimestamp(span.startTimeUnixNano),
          type,
          key,
        };
        const value = attrs["kvonce.event.value"];
        if (value !== undefined) event.value = value;
        const reason = attrs["kvonce.event.reason"];
        if (reason !== undefined) event.reason = reason;
        events.push(event);
      }
    }
  }
  return events;
}

function toNdjson(events) {
  return events.map((event) => JSON.stringify(event)).join("\n") + "\n";
}

const { input, output } = parseArgs();
const otlp = readOtlp(input);
const events = extractEvents(otlp);

if (events.length === 0) {
  console.error("No kvonce events found in OTLP payload.");
  process.exit(EXIT_NO_EVENTS);
}

const ndjson = toNdjson(events);
if (output) {
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, ndjson, "utf8");
} else {
  process.stdout.write(ndjson);
}
