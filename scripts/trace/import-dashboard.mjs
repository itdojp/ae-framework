#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const options = {
    host: process.env.GRAFANA_HOST ?? 'http://localhost:3000',
    token: process.env.GRAFANA_API_TOKEN ?? null,
    folderId: process.env.GRAFANA_FOLDER_ID ? Number(process.env.GRAFANA_FOLDER_ID) : 0,
    overwrite: process.env.GRAFANA_OVERWRITE ? process.env.GRAFANA_OVERWRITE === 'true' : true,
    input: process.env.GRAFANA_DASHBOARD_PATH ?? 'docs/trace/grafana/tempo-dashboard.json',
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--host' || arg === '-h') && next) {
      options.host = next;
      i += 1;
    } else if ((arg === '--token' || arg === '-t') && next) {
      options.token = next;
      i += 1;
    } else if ((arg === '--input' || arg === '-i') && next) {
      options.input = next;
      i += 1;
    } else if (arg === '--folder-id' && next) {
      options.folderId = Number(next);
      i += 1;
    } else if (arg === '--no-overwrite') {
      options.overwrite = false;
    } else if (arg === '--help') {
      console.log(`Usage: node scripts/trace/import-dashboard.mjs [options]

Options:
  -i, --input <file>     Dashboard JSON (default: docs/trace/grafana/tempo-dashboard.json)
  -h, --host <url>       Grafana base URL (default: http://localhost:3000)
  -t, --token <token>    Grafana API token with dashboard:write scope
      --folder-id <id>   Target folder ID (default: 0)
      --no-overwrite     Do not overwrite existing dashboards (default: overwrite)
      --help             Show this message
`);
      process.exit(0);
    }
  }

  if (!options.token) {
    console.error('[import-dashboard] missing Grafana API token (--token or GRAFANA_API_TOKEN)');
    process.exit(1);
  }

  return options;
}

function readDashboard(filePath) {
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    console.error(`[import-dashboard] file not found: ${resolved}`);
    process.exit(1);
  }
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

async function importDashboard({ host, token, folderId, overwrite, input }) {
  const payload = readDashboard(input);
  const body = {
    dashboard: payload.dashboard ?? payload,
    folderId,
    overwrite,
  };

  const response = await fetch(new URL('/api/dashboards/db', host), {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      Authorization: `Bearer ${token}`,
    },
    body: JSON.stringify(body),
  });

  if (!response.ok) {
    const text = await response.text();
    throw new Error(`Grafana import failed (${response.status}): ${text}`);
  }

  console.log('[import-dashboard] dashboard imported successfully');
}

async function main() {
  const options = parseArgs(process.argv);
  try {
    await importDashboard(options);
  } catch (error) {
    console.error('[import-dashboard] error:', error.message);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}
