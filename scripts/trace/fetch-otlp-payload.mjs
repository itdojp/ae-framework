#!/usr/bin/env node
import fs from 'node:fs';
import fsp from 'node:fs/promises';
import path from 'node:path';
import { createHash } from 'node:crypto';

const args = process.argv.slice(2);
const options = { target: null, artifactDir: null, url: null, explicit: null, sourceType: null, sourceDetail: null };
for (let i = 0; i < args.length; i++) {
  const arg = args[i];
  const peek = args[i + 1];
  if ((arg === '--target' || arg === '-t') && peek && !peek.startsWith('-')) {
    options.target = args[++i];
  } else if ((arg === '--artifact-dir' || arg === '-a') && peek && !peek.startsWith('-')) {
    options.artifactDir = args[++i];
  } else if ((arg === '--url' || arg === '-u') && peek && !peek.startsWith('-')) {
    options.url = args[++i];
  } else if ((arg === '--explicit' || arg === '-e') && peek && !peek.startsWith('-')) {
    options.explicit = args[++i];
  } else if ((arg === '--source-type' || arg === '-y') && peek && !peek.startsWith('-')) {
    options.sourceType = args[++i];
  } else if ((arg === '--source-detail' || arg === '-s') && peek && !peek.startsWith('-')) {
    options.sourceDetail = args[++i];
  }
}

if (!options.target) {
  console.error('[fetch-otlp-payload] usage: fetch-otlp-payload.mjs --target <file> [--artifact-dir <dir>] [--url <https://...>] [--explicit <file>]');
  process.exit(1);
}

const targetPath = path.resolve(options.target);
await fsp.mkdir(path.dirname(targetPath), { recursive: true });

const envExplicit =
  process.env.KVONCE_OTLP_PAYLOAD_FILE ??
  process.env.KVONCE_OTLP_PAYLOAD_EXPLICIT ??
  process.env.KVONCE_OTLP_PAYLOAD_LOCAL ??
  null;

const envArtifactDir = process.env.KVONCE_OTLP_ARTIFACT_DIR ?? null;

const envUrl =
  process.env.KVONCE_OTLP_PAYLOAD_URL ??
  process.env.KVONCE_OTLP_URL ??
  process.env.KVONCE_OTLP_PAYLOAD_S3_URL ??
  null;

const envSourceType = process.env.KVONCE_OTLP_SOURCE_TYPE ?? null;
const envSourceDetail = process.env.KVONCE_OTLP_SOURCE_DETAIL ?? null;

if (!options.sourceType && envSourceType) {
  options.sourceType = envSourceType;
}

if (!options.sourceDetail && envSourceDetail) {
  options.sourceDetail = envSourceDetail;
}

// Prefer KVONCE_OTLP_* env fallbacks when CLI flags are omitted.
if (!options.explicit && envExplicit) {
  options.explicit = envExplicit;
  if (!options.sourceType) options.sourceType = 'env-file';
  if (!options.sourceDetail) options.sourceDetail = envExplicit;
}

if (!options.artifactDir && envArtifactDir) {
  options.artifactDir = envArtifactDir;
}

if (!options.url && envUrl) {
  options.url = envUrl;
  if (!options.sourceType) options.sourceType = 'url';
  if (!options.sourceDetail) options.sourceDetail = envUrl;
}

let sourceType = options.sourceType ?? 'unknown';
let sourceDetail = options.sourceDetail ?? 'n/a';

const setSource = (fallbackType, fallbackDetail) => {
  sourceType = options.sourceType ?? fallbackType;
  sourceDetail = options.sourceDetail ?? fallbackDetail;
};

const copyFile = async (source, fallbackType) => {
  const resolved = path.resolve(source);
  await fsp.copyFile(resolved, targetPath);
  setSource(fallbackType, resolved);
};

const writeBuffer = async (buffer, fallbackType, fallbackDetail) => {
  await fsp.writeFile(targetPath, buffer);
  setSource(fallbackType, fallbackDetail);
};

if (options.explicit) {
  await copyFile(options.explicit, 'explicit');
} else if (options.artifactDir) {
  const dir = path.resolve(options.artifactDir);
  const candidates = (await fsp.readdir(dir)).filter((name) => name.endsWith('.json'));
  const candidate = candidates.find((name) => name === 'kvonce-otlp.json') ?? candidates[0];
  if (!candidate) {
    console.error(`[fetch-otlp-payload] no JSON files found under ${dir}`);
    process.exit(1);
  }
  await copyFile(path.join(dir, candidate), 'artifact');
} else if (options.url) {
  const response = await fetch(options.url);
  if (!response.ok) {
    console.error(`[fetch-otlp-payload] failed to download ${options.url}: ${response.status} ${response.statusText ?? ''}`.trim());
    process.exit(1);
  }
  const buffer = Buffer.from(await response.arrayBuffer());
  await writeBuffer(buffer, 'url', options.url);
} else {
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
const metadataDir = path.dirname(targetPath);
await fsp.mkdir(metadataDir, { recursive: true });
const metadataPath = path.join(metadataDir, 'kvonce-payload-metadata.json');
await fsp.writeFile(metadataPath, JSON.stringify(metadata, null, 2));
