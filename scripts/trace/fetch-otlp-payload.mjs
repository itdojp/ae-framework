#!/usr/bin/env node
import fsp from 'node:fs/promises';
import path from 'node:path';
import { createHash } from 'node:crypto';

const args = process.argv.slice(2);
const options = { target: null, artifactDir: null, url: null, explicit: null, s3Uri: null, sourceType: null, sourceDetail: null };
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
  } else if (arg === '--s3-uri' && peek && !peek.startsWith('-')) {
    options.s3Uri = args[++i];
  } else if ((arg === '--source-type' || arg === '-y') && peek && !peek.startsWith('-')) {
    options.sourceType = args[++i];
  } else if ((arg === '--source-detail' || arg === '-s') && peek && !peek.startsWith('-')) {
    options.sourceDetail = args[++i];
  }
}

if (!options.target) {
  console.error('[fetch-otlp-payload] usage: fetch-otlp-payload.mjs --target <file> [--artifact-dir <dir>] [--url <https://...>] [--explicit <file>] [--s3-uri s3://bucket/key]');
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
  null;

const envS3Uri =
  process.env.KVONCE_OTLP_S3_URI ??
  process.env.KVONCE_OTLP_PAYLOAD_S3_URI ??
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

if (!options.s3Uri && envS3Uri) {
  options.s3Uri = envS3Uri;
}

if (!options.url && envUrl) {
  options.url = envUrl;
  if (!options.sourceType) options.sourceType = 'url';
  if (!options.sourceDetail) options.sourceDetail = envUrl;
}

if (!options.s3Uri && options.url && options.url.startsWith('s3://')) {
  options.s3Uri = options.url;
  options.url = null;
}

if (options.s3Uri) {
  if (!options.sourceType) options.sourceType = 's3';
  if (!options.sourceDetail) options.sourceDetail = options.s3Uri;
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
  await fsp.writeFile(targetPath, buffer); // codeql[js/http-to-file-access] Persisting fetched payloads is an explicit CLI action.
  setSource(fallbackType, fallbackDetail);
};

const parseS3Uri = (uri) => {
  const normalized = uri.replace(/^minio:\/\//i, 's3://');
  const match = normalized.match(/^s3:\/\/([^/]+)\/(.+)$/i);
  if (!match) {
    throw new Error(`invalid s3 uri: ${uri}`);
  }
  return { bucket: match[1], key: match[2] };
};

const streamToBuffer = async (stream) => {
  const chunks = [];
  for await (const chunk of stream) {
    chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk));
  }
  return Buffer.concat(chunks);
};

async function fetchFromS3(uri) {
  const { bucket, key } = parseS3Uri(uri);
  const mockRoot = process.env.KVONCE_OTLP_S3_MOCK_DIR;
  if (mockRoot) {
    const filePath = path.join(path.resolve(mockRoot), bucket, key);
    try {
      return await fsp.readFile(filePath);
    } catch (error) {
      console.error(`[fetch-otlp-payload] mock S3 file not found at ${filePath}: ${error.message}`);
      process.exit(1);
    }
  }

  try {
    const { S3Client, GetObjectCommand } = await import('@aws-sdk/client-s3');
    const region = process.env.KVONCE_OTLP_S3_REGION ?? process.env.AWS_REGION ?? 'us-east-1';
    let endpoint = process.env.KVONCE_OTLP_S3_ENDPOINT ?? undefined;
    const useTls = process.env.KVONCE_OTLP_S3_USE_SSL !== 'false';

    if (endpoint) {
      if (!endpoint.startsWith('http://') && !endpoint.startsWith('https://')) {
        endpoint = `${useTls ? 'https' : 'http'}://${endpoint}`;
      } else if (useTls && endpoint.startsWith('http://')) {
        endpoint = endpoint.replace(/^http:\/\//, 'https://');
      } else if (!useTls && endpoint.startsWith('https://')) {
        endpoint = endpoint.replace(/^https:\/\//, 'http://');
      }
    }

    const AWS_S3_HOST_REGEX = /\.amazonaws\.com(\.cn)?$/i;
    let isAwsEndpoint = false;
    if (endpoint) {
      try {
        const parsed = new URL(endpoint);
        isAwsEndpoint = AWS_S3_HOST_REGEX.test(parsed.hostname);
      } catch {
        isAwsEndpoint = AWS_S3_HOST_REGEX.test(endpoint);
      }
    }

    const forcePathStyle =
      process.env.KVONCE_OTLP_S3_FORCE_PATH_STYLE === 'true' ||
      Boolean(endpoint && !isAwsEndpoint);

    const client = new S3Client({
      region,
      ...(endpoint ? { endpoint } : {}),
      ...(forcePathStyle ? { forcePathStyle: true } : {}),
    });

    const response = await client.send(new GetObjectCommand({ Bucket: bucket, Key: key }));
    if (!response.Body) {
      console.error(`[fetch-otlp-payload] empty S3 object body for ${uri}`);
      process.exit(1);
    }
    return await streamToBuffer(response.Body);
  } catch (error) {
    console.error(`[fetch-otlp-payload] failed to download ${uri}: ${error.message}`);
    process.exit(1);
  }
}

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
} else if (options.s3Uri) {
  const buffer = await fetchFromS3(options.s3Uri);
  await writeBuffer(buffer, 's3', options.s3Uri);
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
