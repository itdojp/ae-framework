#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import https from 'node:https';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');

function parseArgs(argv) {
  const options = {
    envelope: process.env.ENVELOPE_PUBLISH_SOURCE ?? 'artifacts/report-envelope.json',
    bucket: process.env.ENVELOPE_PUBLISH_BUCKET ?? null,
    key: process.env.ENVELOPE_PUBLISH_KEY ?? null,
    expires: Number.parseInt(process.env.ENVELOPE_PUBLISH_EXPIRES ?? '604800', 10),
    slackWebhook: process.env.ENVELOPE_PUBLISH_SLACK_WEBHOOK ?? null,
    slackChannel: process.env.ENVELOPE_PUBLISH_SLACK_CHANNEL ?? null,
    output: process.env.ENVELOPE_PUBLISH_OUTPUT ?? 'artifacts/trace/publish-envelope.json',
    dryRun: false,
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--envelope' || arg === '-e') && next) {
      options.envelope = next;
      i += 1;
    } else if ((arg === '--bucket' || arg === '-b') && next) {
      options.bucket = next;
      i += 1;
    } else if ((arg === '--key' || arg === '-k') && next) {
      options.key = next;
      i += 1;
    } else if (arg === '--expires' && next) {
      options.expires = Number.parseInt(next, 10);
      i += 1;
    } else if (arg === '--slack-webhook' && next) {
      options.slackWebhook = next;
      i += 1;
    } else if (arg === '--slack-channel' && next) {
      options.slackChannel = next;
      i += 1;
    } else if ((arg === '--output' || arg === '-o') && next) {
      options.output = next;
      i += 1;
    } else if (arg === '--dry-run') {
      options.dryRun = true;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node scripts/trace/publish-envelope.mjs [options]
Options:
  -e, --envelope <file>       Envelope JSON (default: artifacts/report-envelope.json)
  -b, --bucket <name>         S3 bucket (required)
  -k, --key <key>             S3 key (default: envelopes/<runId>/<filename>)
      --expires <seconds>     Presigned URL expiration in seconds (default: 604800)
      --slack-webhook <url>   Slack Incoming Webhook URL (optional)
      --slack-channel <name>  Slack channel or conversation label
      --output <file>         Output metadata JSON (default: artifacts/trace/publish-envelope.json)
      --dry-run               Skip upload/presign/slack, emit summary only
      --help                  Show this message
`);
      process.exit(0);
    }
  }
  return options;
}

function readEnvelope(resolvedPath) {
  if (!fs.existsSync(resolvedPath)) {
    console.error(`[publish-envelope] envelope not found: ${resolvedPath}`);
    process.exit(1);
  }
  try {
    return JSON.parse(fs.readFileSync(resolvedPath, 'utf8'));
  } catch (error) {
    console.error(`[publish-envelope] failed to parse envelope: ${resolvedPath}`);
    console.error(error.message);
    process.exit(1);
  }
}

function runUpload(envelopePath, bucket, key) {
  const uploadScript = path.resolve(repoRoot, 'scripts', 'trace', 'upload-envelope.mjs');
  const result = spawnSync(process.execPath, [uploadScript, '--file', envelopePath, '--bucket', bucket, '--key', key], {
    stdio: 'inherit',
    cwd: repoRoot,
  });
  if (result.status !== 0) {
    console.error(`[publish-envelope] upload failed with status ${result.status}`);
    process.exit(result.status ?? 1);
  }
}

function runPresign(bucket, key, expires) {
  const s3Path = `s3://${bucket}/${key}`;
  const result = spawnSync('aws', ['s3', 'presign', s3Path, '--expires', String(expires)], {
    encoding: 'utf8',
    cwd: repoRoot,
  });
  if (result.status !== 0) {
    console.error('[publish-envelope] aws s3 presign failed');
    if (result.stderr) console.error(result.stderr.trim());
    process.exit(result.status ?? 1);
  }
  return result.stdout.trim();
}

function postSlack(webhookUrl, payload) {
  return new Promise((resolve, reject) => {
    const url = new URL(webhookUrl);
    const request = https.request({
      hostname: url.hostname,
      path: `${url.pathname}${url.search}`,
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
    }, (res) => {
      if (res.statusCode && res.statusCode >= 200 && res.statusCode < 300) {
        resolve();
      } else {
        reject(new Error(`Slack webhook failed with status ${res.statusCode}`));
      }
    });
    request.on('error', reject);
    request.write(JSON.stringify(payload));
    request.end();
  });
}

function ensureOutputDir(filePath) {
  const dir = path.dirname(filePath);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
}

async function main() {
  const options = parseArgs(process.argv);
  if (!options.bucket) {
    console.error('[publish-envelope] missing required bucket (--bucket)');
    process.exit(1);
  }

  const envelopePath = path.resolve(options.envelope);
  const envelope = readEnvelope(envelopePath);
  const defaultKey = () => {
    const runId = envelope?.correlation?.runId ?? `run-${Date.now()}`;
    return `envelopes/${runId}/${path.basename(envelopePath)}`;
  };
  const key = options.key ?? defaultKey();

  console.log(`[publish-envelope] envelope=${path.relative(repoRoot, envelopePath)}`);
  console.log(`[publish-envelope] bucket=${options.bucket} key=${key}`);

  let presignedUrl = null;
  const dryRun = Boolean(options.dryRun);

  if (!dryRun) {
    runUpload(path.relative(process.cwd(), envelopePath), options.bucket, key);
    presignedUrl = runPresign(options.bucket, key, options.expires);
    console.log(`[publish-envelope] presigned URL: ${presignedUrl}`);
  } else {
    console.log('[publish-envelope] dry-run mode, skipping upload/presign');
  }

  const tempoLinks = Array.isArray(envelope?.tempoLinks)
    ? envelope.tempoLinks.slice(0, 3)
    : Array.isArray(envelope?.summary?.tempoLinks)
      ? envelope.summary.tempoLinks.slice(0, 3)
      : [];

  const slackPayload = {
    text: 'Envelope uploaded ✅',
    blocks: [
      {
        type: 'section',
        text: {
          type: 'mrkdwn',
          text: `Envelope uploaded ✅\n- workflow: *${envelope?.correlation?.workflow ?? 'n/a'}*\n- branch: *${envelope?.correlation?.branch ?? 'n/a'}*\n- presigned: ${presignedUrl ?? '(dry-run)'}\n- tempo links: ${tempoLinks.length > 0 ? tempoLinks.join(', ') : 'n/a'}`,
        },
      },
    ],
  };

  if (!dryRun && options.slackWebhook) {
    try {
      await postSlack(options.slackWebhook, {
        ...slackPayload,
        ...(options.slackChannel ? { channel: options.slackChannel } : {}),
      });
      console.log('[publish-envelope] posted Slack notification');
    } catch (error) {
      console.error('[publish-envelope] Slack notification failed:', error.message);
      process.exit(1);
    }
  } else if (options.slackWebhook && dryRun) {
    console.log('[publish-envelope] dry-run: Slack payload preview');
    console.log(JSON.stringify(slackPayload, null, 2));
  }

  const metadata = {
    bucket: options.bucket,
    key,
    presignedUrl,
    expires: options.expires,
    slackWebhook: options.slackWebhook ? 'configured' : null,
    slackChannel: options.slackChannel ?? null,
    notified: Boolean(options.slackWebhook && !dryRun),
    dryRun,
    generatedAt: new Date().toISOString(),
  };

  const outputPath = path.resolve(options.output);
  ensureOutputDir(outputPath);
  fs.writeFileSync(outputPath, JSON.stringify(metadata, null, 2));
  console.log(`[publish-envelope] metadata written to ${outputPath}`);
}

main().catch((error) => {
  console.error('[publish-envelope] unexpected error', error);
  process.exit(1);
});
