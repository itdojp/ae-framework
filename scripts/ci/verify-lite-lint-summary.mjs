#!/usr/bin/env node
import { createInterface } from 'node:readline';
import { stdin, stdout } from 'node:process';

const rl = createInterface({ input: stdin, crlfDelay: Infinity });
const summary = new Map();
let total = 0;

for await (const line of rl) {
  const match = line.match(/^\s*(?:\d+:\d+\s+)?(warning|error)\s+([^\s]+)\s+(.+)$/);
  if (match) {
    const [, level, rule, message] = match;
    total++;
    const key = `${rule}`;
    const entry = summary.get(key) ?? { rule, level, count: 0, samples: [] };
    entry.count += 1;
    if (entry.samples.length < 3) {
      entry.samples.push(message.trim());
    }
    summary.set(key, entry);
  }
}

const output = {
  total,
  rules: Array.from(summary.values())
    .sort((a, b) => b.count - a.count)
    .map(({ rule, level, count, samples }) => ({ rule, level, count, samples }))
};

stdout.write(JSON.stringify(output, null, 2));
