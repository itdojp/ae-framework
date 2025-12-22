#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import YAML from 'yaml';

function parseArgs(argv) {
  const options = {
    host: process.env.GRAFANA_BASE_URL ?? process.env.GRAFANA_HOST ?? 'http://localhost:3000',
    token: process.env.GRAFANA_API_TOKEN ?? null,
    uid: process.env.GRAFANA_DASHBOARD_UID ?? null,
    output: process.env.GRAFANA_DASHBOARD_PATH ?? 'docs/trace/grafana/tempo-dashboard.json',
    config: null,
    dryRun: false,
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
    } else if (arg === '--config' && next) {
      options.config = next;
      i += 1;
    } else if (arg === '--dry-run') {
      options.dryRun = true;
    } else if (arg === '--help') {
      console.log(`Usage: node scripts/trace/export-dashboard.mjs [options]

Options:
  -h, --host <url>     Grafana base URL (default: http://localhost:3000)
  -u, --uid <uid>      Dashboard UID to export (required if --config is absent)
  -t, --token <token>  Grafana API token with dashboard:read scope
  -o, --output <file>  Output JSON path (default: docs/trace/grafana/tempo-dashboard.json)
      --config <file>  YAML config with dashboards: [ { uid, file } ]
      --dry-run        Indicate that changes are validated (still writes files)
      --help           Show this message
`);
      process.exit(0);
    }
  }

  if (!options.config && !options.uid) {
    console.error('[export-dashboard] supply --uid or --config to specify dashboards');
    process.exit(1);
  }

  return options;
}

function loadDashboardConfig(configPath) {
  const resolved = path.resolve(configPath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`[export-dashboard] config not found: ${resolved}`);
  }
  let parsed;
  try {
    const content = fs.readFileSync(resolved, 'utf8');
    parsed = YAML.parse(content);
  } catch (error) {
    throw new Error(`[export-dashboard] failed to read config: ${error.message}`);
  }
  const dashboards = Array.isArray(parsed?.dashboards) ? parsed.dashboards : [];
  if (dashboards.length === 0) {
    throw new Error('[export-dashboard] config contains no dashboards to export');
  }
  return dashboards.map((entry, index) => {
    const uid = entry?.uid;
    const file = entry?.file ?? entry?.path;
    if (!uid) {
      throw new Error(`[export-dashboard] dashboards[${index}] missing uid`);
    }
    if (!file) {
      throw new Error(`[export-dashboard] dashboards[${index}] missing file`);
    }
    return { uid: String(uid), file: String(file) };
  });
}

async function exportDashboard({ host, uid, token, output, dryRun }) {
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
  fs.writeFileSync(destPath, JSON.stringify(data, null, 2)); // codeql[js/http-to-file-access] Exporting dashboards to disk is an explicit CLI action.
  const suffix = dryRun ? ' (dry-run)' : '';
  console.log(`[export-dashboard] dashboard export completed${suffix}`);
}

async function main() {
  const options = parseArgs(process.argv);
  let dashboards = [];
  if (options.config) {
    dashboards = loadDashboardConfig(options.config);
  } else {
    dashboards = [{ uid: options.uid, file: options.output }];
  }

  try {
    for (const dashboard of dashboards) {
      await exportDashboard({
        host: options.host,
        uid: dashboard.uid,
        token: options.token,
        output: dashboard.file,
        dryRun: options.dryRun,
      });
    }
  } catch (error) {
    console.error('[export-dashboard] error:', error.message);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}
