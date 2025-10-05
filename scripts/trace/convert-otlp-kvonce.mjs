#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";

const NANOS_PER_MILLI = 1_000_000n;
const MAX_DATE_MILLIS = BigInt(Number.MAX_SAFE_INTEGER);
const MIN_DATE_MILLIS = BigInt(Number.MIN_SAFE_INTEGER);
const EXIT_NO_EVENTS = 2;

function parseArgs() {
  const args = process.argv.slice(2);
  const result = { input: null, output: null };
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "--input" || arg === "-i") {
      if (i + 1 >= args.length || args[i + 1].startsWith("-")) {
        console.error("Error: --input requires a value.");
        process.exit(1);
      }
      result.input = args[++i];
    } else if (arg === "--output" || arg === "-o") {
      if (i + 1 >= args.length || args[i + 1].startsWith("-")) {
        console.error("Error: --output requires a value.");
        process.exit(1);
      }
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
      attrValue.mapValue.fields.map(({ key = "", value = null } = {}) => [
        key,
        extractAttributeValue(value),
      ])
    );
  }
  console.warn(
    "[convert-otlp-kvonce] unsupported OTLP attribute representation encountered; returning undefined",
    attrValue
  );
  // Unsupported OTLP value representations (bytesValue, kvlistValue, or vendor extensions)
  // fall back to undefined. attrsToRecord preserves the key so downstream validators can
  // decide whether the payload should fail or emit a warning.
  return undefined;
}

/**
 * Flattens OTLP span attributes into a plain object. Keys with unsupported value
 * representations remain present with an explicit `undefined` value so that
 * downstream validators can decide whether to treat them as errors or warnings.
 */
function attrsToRecord(attributes = []) {
  const record = {};
  for (const attribute of attributes || []) {
    record[attribute.key] = extractAttributeValue(attribute.value);
  }
  return record;
}

function toTimestamp(nanoString) {
  if (!nanoString) {
    console.warn("[convert-otlp-kvonce] missing span timestamp; skipping event");
    return null;
  }
  try {
    const nanos = BigInt(nanoString);
    const millisBigInt = nanos / NANOS_PER_MILLI;
    if (millisBigInt > MAX_DATE_MILLIS || millisBigInt < MIN_DATE_MILLIS) {
      console.warn(
        `Invalid timestamp ${nanoString} (millis ${millisBigInt}) exceeds Date range [${MIN_DATE_MILLIS} to ${MAX_DATE_MILLIS}]; skipping event.`
      );
      return null;
    }
    const millis = Number(millisBigInt);
    return new Date(millis).toISOString();
  } catch (error) {
    console.warn(`Failed to convert timestamp ${nanoString}: ${error.message}`);
    return null;
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
        const timestamp = toTimestamp(span.startTimeUnixNano);
        if (!timestamp) {
          console.warn(
            `[convert-otlp-kvonce] span ${span.name ?? 'unknown'} missing usable timestamp; event dropped`
          );
          continue;
        }
        const event = {
          timestamp,
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
  console.error(
    "No kvonce events found in OTLP payload. A kvonce event must include 'kvonce.event.type' and 'kvonce.event.key' attributes."
  );
  process.exit(EXIT_NO_EVENTS);
}

const ndjson = toNdjson(events);
if (output) {
  const dir = path.dirname(output);
  if (dir && dir !== "." && dir !== path.parse(dir).root) {
    fs.mkdirSync(dir, { recursive: true });
  }
  fs.writeFileSync(output, ndjson, "utf8");
} else {
  process.stdout.write(ndjson);
}
