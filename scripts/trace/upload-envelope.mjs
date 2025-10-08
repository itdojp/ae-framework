#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const options = {
    file: process.env.REPORT_ENVELOPE_OUTPUT ?? 'artifacts/report-envelope.json',
    bucket: process.env.REPORT_ENVELOPE_S3_BUCKET ?? null,
    key: process.env.REPORT_ENVELOPE_S3_KEY ?? null,
    acl: process.env.REPORT_ENVELOPE_S3_ACL ?? 'private',
    profile: process.env.AWS_PROFILE ?? null,
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--file' || arg === '-f') && next) {
      options.file = next;
      i += 1;
    } else if ((arg === '--bucket' || arg === '-b') && next) {
      options.bucket = next;
      i += 1;
    } else if ((arg === '--key' || arg === '-k') && next) {
      options.key = next;
      i += 1;
    } else if (arg === '--acl' && next) {
      options.acl = next;
      i += 1;
    } else if (arg === '--profile' && next) {
      options.profile = next;
      i += 1;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node scripts/trace/upload-envelope.mjs [options]

Options:
  -f, --file <path>     Envelope JSON to upload (default: artifacts/report-envelope.json)
  -b, --bucket <name>   Destination S3 bucket (required)
  -k, --key <key>       S3 object key (default: envelopes/<filename>)
      --acl <acl>       ACL to apply (default: private)
      --profile <name>  AWS profile to use (optional)
  -h, --help            Show this message
`);
      process.exit(0);
    }
  }

  if (!options.bucket) {
    console.error('[upload-envelope] missing required --bucket');
    process.exit(1);
  }

  if (!options.key) {
    const filename = path.basename(options.file);
    options.key = `envelopes/${filename}`;
  }

  return options;
}

function ensureFile(filePath) {
  if (!fs.existsSync(filePath)) {
    console.error(`[upload-envelope] file not found: ${filePath}`);
    process.exit(1);
  }
}

function upload({ file, bucket, key, acl, profile }) {
  ensureFile(file);
  const args = ['s3', 'cp', file, `s3://${bucket}/${key}`, '--acl', acl];
  if (profile) {
    args.unshift('--profile', profile);
  }
  const result = spawnSync('aws', args, { stdio: 'inherit' });
  if (result.status !== 0) {
    console.error(`[upload-envelope] aws s3 cp failed with status ${result.status}`);
    process.exit(result.status ?? 1);
  }
  console.log(`[upload-envelope] uploaded ${file} to s3://${bucket}/${key}`);
}

function main() {
  const options = parseArgs(process.argv);
  upload(options);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}
