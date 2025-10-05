#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";

const args = process.argv.slice(2);
const options = {};
for (let i = 0; i < args.length; i++) {
  const arg = args[i];
  if ((arg === "--target" || arg === "-t") && args[i + 1]) {
    options.target = args[++i];
  } else if ((arg === "--source-detail" || arg === "-s") && args[i + 1]) {
    options.sourceDetail = args[++i];
  } else if ((arg === "--source-type" || arg === "-y") && args[i + 1]) {
    options.sourceType = args[++i];
  }
}

if (!options.target) {
  console.error('[write-payload-metadata] usage: write-payload-metadata.mjs --target <file> [--source-detail <detail>] [--source-type <type>]');
  process.exit(1);
}

const targetPath = path.resolve(options.target);
const detail = options.sourceDetail ?? 'unknown';
const type = options.sourceType ?? 'sample';

try {
  const payload = fs.readFileSync(targetPath);
  const hash = createHash('sha256').update(payload).digest('hex');
  const metadata = {
    sourceType: type,
    sourceDetail: detail,
    sha256: hash,
    sizeBytes: payload.length,
  };
  const metadataDir = path.dirname(targetPath);
  const metadataPath = path.join(metadataDir, 'kvonce-payload-metadata.json');
  fs.mkdirSync(metadataDir, { recursive: true });
  fs.writeFileSync(metadataPath, JSON.stringify(metadata, null, 2));
} catch (error) {
  console.error(`[write-payload-metadata] failed for ${targetPath}: ${error.message}`);
  process.exit(1);
}
