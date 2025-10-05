#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";

const NANOS_PER_MILLI = 1_000_000n;
const EXIT_NO_EVENTS = 2;
const MAX_DATE_MILLIS = 8_640_000_000_000_000n;
const MIN_DATE_MILLIS = -MAX_DATE_MILLIS;

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
      attrValue.mapValue.fields.map(({ key = "", value } = {}) => [
        key,
        extractAttributeValue(value),
      ])
    );
  }
  // Unsupported OTLP value representations fall back to undefined so the caller can decide whether validation should fail.
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
    const millisBigInt = nanos / NANOS_PER_MILLI;
    if (millisBigInt > MAX_DATE_MILLIS || millisBigInt < MIN_DATE_MILLIS) {
      console.warn(
        `Invalid timestamp ${nanoString} (millis ${millisBigInt}) exceeds Date range [` +
          `${MIN_DATE_MILLIS} to ${MAX_DATE_MILLIS}]; using current time.`
      );
      return new Date().toISOString();
    }
    const millis = Number(millisBigInt);
    return new Date(millis).toISOString();
  } catch (error) {
    console.warn(`Failed to convert timestamp ${nanoString}: ${error.message}`);
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
        const context = attrs["kvonce.event.context"];
        if (context !== undefined) event.context = context;
        events.push(event);
      }
    }
  }
  return events;
}

function toNdjson(events) {
  if (events.length === 0) {
    return "";
  }
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
