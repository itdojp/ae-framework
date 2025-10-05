#!/usr/bin/env node
import fs from "node:fs";
import fsp from "node:fs/promises";
import path from "node:path";
import { createHash } from "node:crypto";

const args = process.argv.slice(2);
const options = { target: null, artifactDir: null, url: null, explicit: null, sourceType: null, sourceDetail: null };
for (let i = 0; i < args.length; i++) {
  const arg = args[i];
  if ((arg === "--target" || arg === "-t") && args[i + 1]) {
    options.target = args[++i];
  } else if ((arg === "--artifact-dir" || arg === "-a") && args[i + 1]) {
    options.artifactDir = args[++i];
  } else if ((arg === "--url" || arg === "-u") && args[i + 1]) {
    options.url = args[++i];
  } else if ((arg === "--explicit" || arg === "-e") && args[i + 1]) {
    options.explicit = args[++i];
  } else if ((arg === "--source-type" || arg === "-y") && args[i + 1]) {
    options.sourceType = args[++i];
  } else if ((arg === "--source-detail" || arg === "-s") && args[i + 1]) {
    options.sourceDetail = args[++i];
  }
}

if (!options.target) {
  console.error('[fetch-otlp-payload] usage: fetch-otlp-payload.mjs --target <file> [--artifact-dir <dir>] [--url <https://...>] [--explicit <file>]');
  process.exit(1);
}

const targetPath = path.resolve(options.target);
await fsp.mkdir(path.dirname(targetPath), { recursive: true });

let sourceType = options.sourceType ?? 'unknown';
let sourceDetail = options.sourceDetail ?? 'n/a';

async function copyFile(source) {
  await fsp.copyFile(source, targetPath);
  sourceDetail = source;
}

if (options.explicit) {
  await copyFile(options.explicit);
  sourceType = 'explicit';
} else if (options.artifactDir) {
  const dir = path.resolve(options.artifactDir);
  const candidates = (await fsp.readdir(dir)).filter((name) => name.endsWith('.json'));
  const candidate = candidates.find((name) => name === 'kvonce-otlp.json') ?? candidates[0];
  if (!candidate) {
    console.error(`[fetch-otlp-payload] no JSON files found under ${dir}`);
    process.exit(1);
  }
  await copyFile(path.join(dir, candidate));
  sourceType = 'artifact';
} else if (options.url) {
  const response = await fetch(options.url);
  if (!response.ok) {
    console.error(`[fetch-otlp-payload] failed to download ${options.url}: ${response.status}`);
    process.exit(1);
  }
  const buffer = Buffer.from(await response.arrayBuffer());
  await fsp.writeFile(targetPath, buffer);
  sourceType = 'url';
  sourceDetail = options.url;
} else if (!options.sourceType && !options.sourceDetail) {
  console.error('[fetch-otlp-payload] no source provided (artifact, url, or explicit).');
  process.exit(1);
}

const payload = await fsp.readFile(targetPath);
const hash = createHash('sha256').update(payload).digest('hex');
const metadata = {
  sourceType,
  sourceDetail,
  sha256: hash,
  sizeBytes: payload.length,
};
const metadataPath = path.join(path.dirname(targetPath), '..', 'kvonce-payload-metadata.json');
await fsp.mkdir(path.dirname(metadataPath), { recursive: true });
await fsp.writeFile(metadataPath, JSON.stringify(metadata, null, 2));
