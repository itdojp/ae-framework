#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const options = {
    host: process.env.GRAFANA_HOST ?? 'http://localhost:3000',
    uid: process.env.GRAFANA_DASHBOARD_UID ?? null,
    token: process.env.GRAFANA_API_TOKEN ?? null,
    output: 'docs/trace/grafana/tempo-dashboard.json',
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--host' || arg === '-h') && next) {
      options.host = next;
      i += 1;
    } else if ((arg === '--uid' || arg === '-u') && next) {
      options.uid = next;
      i += 1;
    } else if ((arg === '--token' || arg === '-t') && next) {
      options.token = next;
      i += 1;
    } else if ((arg === '--output' || arg === '-o') && next) {
      options.output = next;
      i += 1;
    } else if (arg === '--help') {
      console.log(`Usage: node scripts/trace/export-dashboard.mjs [options]

Options:
  -h, --host <url>     Grafana base URL (default: http://localhost:3000)
  -u, --uid <uid>      Dashboard UID to export (required)
  -t, --token <token>  Grafana API token with dashboard:read scope
  -o, --output <file>  Output JSON path (default: docs/trace/grafana/tempo-dashboard.json)
      --help           Show this message
`);
      process.exit(0);
    }
  }

  if (!options.uid) {
    console.error('[export-dashboard] missing required --uid');
    process.exit(1);
  }

  return options;
}

async function exportDashboard({ host, uid, token, output }) {
  const url = new URL(`/api/dashboards/uid/${encodeURIComponent(uid)}`, host).toString();
  const headers = { 'Content-Type': 'application/json' };
  if (token) {
    headers.Authorization = `Bearer ${token}`;
  }

  const response = await fetch(url, { headers });
  if (!response.ok) {
    const body = await response.text();
    throw new Error(`Failed to fetch dashboard (${response.status}): ${body}`);
  }

  const data = await response.json();
  const destPath = path.resolve(output);
  fs.mkdirSync(path.dirname(destPath), { recursive: true });
  fs.writeFileSync(destPath, JSON.stringify(data, null, 2));
  console.log(`[export-dashboard] wrote dashboard to ${destPath}`);
}

async function main() {
  const options = parseArgs(process.argv);
  try {
    await exportDashboard(options);
  } catch (error) {
    console.error('[export-dashboard] error:', error.message);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}
