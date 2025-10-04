#!/usr/bin/env node
import fs from 'node:fs/promises';
import { createHash } from 'node:crypto';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { gunzipSync } from 'node:zlib';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');

function parseArgs() {
  const args = process.argv.slice(2);
  const result = { target: null, artifactDir: null, url: null, explicit: null };
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    const next = args[i + 1];
    switch (arg) {
      case '--target':
        if (!next) throw new Error('Missing value for --target');
        result.target = args[++i];
        break;
      case '--artifact-dir':
        if (!next) throw new Error('Missing value for --artifact-dir');
        result.artifactDir = args[++i];
        break;
      case '--url':
        if (!next) throw new Error('Missing value for --url');
        result.url = args[++i];
        break;
      case '--explicit':
        if (!next) throw new Error('Missing value for --explicit');
        result.explicit = args[++i];
        break;
      default:
        // ignore unknown args to keep compatibility
        break;
    }
  }
  if (!result.target) {
    throw new Error('Missing required --target option');
  }
  return result;
}

async function pathExists(candidate) {
  if (!candidate) return false;
  try {
    await fs.access(candidate);
    return true;
  } catch {
    return false;
  }
}

async function readFileBuffer(filePath) {
  if (filePath.endsWith('.gz')) {
    const compressed = await fs.readFile(filePath);
    return gunzipSync(compressed);
  }
  return fs.readFile(filePath);
}

async function selectArtifactFile(dir) {
  if (!dir) return null;
  const entries = await fs.readdir(dir, { withFileTypes: true });
  const files = entries.filter((entry) => entry.isFile());
  const preferred = ['kvonce-otlp-payload.json', 'kvonce-otlp.json', 'payload.json'];
  for (const name of preferred) {
    const match = files.find((file) => file.name === name || file.name === `${name}.gz`);
    if (match) return path.join(dir, match.name);
  }
  const json = files.find((file) => file.name.endsWith('.json') || file.name.endsWith('.json.gz'));
  return json ? path.join(dir, json.name) : null;
}

async function downloadUrl(url, destination) {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to download payload: ${response.status} ${response.statusText}`);
  }
  const arrayBuffer = await response.arrayBuffer();
  const buffer = Buffer.from(arrayBuffer);
  await fs.mkdir(path.dirname(destination), { recursive: true });
  await fs.writeFile(destination, buffer);
  return buffer;
}

async function writeBuffer(target, buffer) {
  await fs.mkdir(path.dirname(target), { recursive: true });
  await fs.writeFile(target, buffer);
}

function computeSha256(buffer) {
  return createHash('sha256').update(buffer).digest('hex');
}

async function ensureMetadata(dir, metadata) {
  const metadataPath = path.join(dir, 'kvonce-payload-metadata.json');
  await fs.writeFile(metadataPath, JSON.stringify(metadata, null, 2));
  return metadataPath;
}

async function main() {
  const args = parseArgs();
  const targetPath = path.resolve(args.target);
  const targetDir = path.dirname(targetPath);
  const metadata = {
    sourceType: 'unknown',
    sourceDetail: '',
    sha256: '',
    sizeBytes: 0,
    generatedAt: new Date().toISOString(),
  };

  let buffer = null;

  if (await pathExists(args.explicit)) {
    buffer = await readFileBuffer(args.explicit);
    metadata.sourceType = 'explicit';
    metadata.sourceDetail = args.explicit;
  }

  if (!buffer && args.artifactDir) {
    const candidate = await selectArtifactFile(args.artifactDir);
    if (candidate && (await pathExists(candidate))) {
      buffer = await readFileBuffer(candidate);
      metadata.sourceType = 'artifact';
      metadata.sourceDetail = candidate;
    }
  }

  if (!buffer && args.url) {
    const tempPath = path.join(targetDir, 'kvonce-otlp-download.tmp');
    buffer = await downloadUrl(args.url, tempPath);
    metadata.sourceType = 'url';
    metadata.sourceDetail = args.url;
    await fs.unlink(tempPath).catch(() => {});
  }

  if (!buffer) {
    const sample = path.join(projectRoot, 'samples', 'trace', 'kvonce-otlp.json');
    buffer = await readFileBuffer(sample);
    metadata.sourceType = 'sample';
    metadata.sourceDetail = sample;
  }

  await writeBuffer(targetPath, buffer);
  metadata.sha256 = computeSha256(buffer);
  metadata.sizeBytes = buffer.length;
  await ensureMetadata(targetDir, metadata);
  console.log(`[fetch-otlp-payload] source=${metadata.sourceType} detail=${metadata.sourceDetail}`);
  console.log(`[fetch-otlp-payload] wrote ${buffer.length} bytes to ${targetPath}`);
}

main().catch((error) => {
  console.error('[fetch-otlp-payload] failed:', error.message);
  process.exitCode = 1;
});
