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

function toTimestamp(nanoString) {
  if (!nanoString) return new Date().toISOString();
  try {
    const nanos = BigInt(nanoString);
    const millisBigInt = nanos / 1000000n;
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
  const resourceSpans = otlp?.resourceSpans || [];
  for (const resourceSpan of resourceSpans) {
    const scopeSpans = resourceSpan.scopeSpans || [];
    for (const scopeSpan of scopeSpans) {
      const spans = scopeSpan.spans || [];
      for (const span of spans) {
        const attrs = {};
        for (const attribute of span.attributes || []) {
          attrs[attribute.key] = attribute.value;
        }
        const type = attrs["kvonce.event.type"]?.stringValue;
        const key = attrs["kvonce.event.key"]?.stringValue;
        if (!type || !key) continue;
        const event = {
          timestamp: toTimestamp(span.startTimeUnixNano),
          type,
          key,
        };
        if (attrs["kvonce.event.value"]?.stringValue !== undefined) {
          event.value = attrs["kvonce.event.value"].stringValue;
        }
        if (attrs["kvonce.event.reason"]?.stringValue !== undefined) {
          event.reason = attrs["kvonce.event.reason"].stringValue;
        }
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
