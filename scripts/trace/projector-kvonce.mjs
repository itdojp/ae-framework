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
    console.error('Usage: projector-kvonce --input <ndjson> [--output <json>]');
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

function buildProjection(events) {
  const perKey = new Map();
  for (const event of events) {
    const key = event.key ?? 'unknown';
    if (!perKey.has(key)) {
    perKey.set(key, {
      successCount: 0,
      retries: 0,
      failureReasons: [],
      retryContexts: [],
      successContexts: [],
      failureContexts: [],
    });
  }
  const entry = perKey.get(key);
  if (event.type === 'success') {
    entry.successCount += 1;
    entry.value = event.value ?? null;
    if (event.context !== undefined) {
      entry.successContexts.push(event.context);
    }
  }
  if (event.type === 'retry') {
    entry.retries += 1;
    if (event.context !== undefined) {
      entry.retryContexts.push(event.context);
    }
  }
  if (event.type === 'failure') {
    entry.failureReasons.push(event.reason ?? 'unknown');
    if (event.context !== undefined) {
      entry.failureContexts.push(event.context);
    }
  }
  }

  return {
    generatedAt: new Date().toISOString(),
    eventCount: events.length,
    events,
    perKey: Object.fromEntries(perKey.entries()),
  };
}

const { input, output } = parseArgs();
const events = readNdjson(input);
const projection = buildProjection(events);

const json = JSON.stringify(projection, null, 2);
if (output) {
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, json);
} else {
  process.stdout.write(json);
}
