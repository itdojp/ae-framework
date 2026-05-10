#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const DEFAULT_ROOT = process.cwd();

const CHECKS = [
  {
    id: 'schema-governance-migration-rules',
    file: 'docs/reference/SCHEMA-GOVERNANCE.md',
    description: 'Schema governance must document dual-write / dual-validate migration and breaking-change requirements.',
    markers: [
      'Dual-write / dual-validate migration rules',
      'Breaking-change checklist',
      'migration note',
      'contract catalog update'
    ]
  },
  {
    id: 'contract-catalog-route-linkage',
    file: 'docs/reference/CONTRACT-CATALOG.md',
    description: 'Contract catalog must link contract inventory to canonical route states and cleanup markers.',
    markers: [
      'docs/reference/ASSURANCE-CANONICAL-ROUTES.md',
      'Current cleanup markers',
      'preview',
      'legacy',
      'compatibility'
    ]
  },
  {
    id: 'canonical-routes-compatibility-rules',
    file: 'docs/reference/ASSURANCE-CANONICAL-ROUTES.md',
    description: 'Canonical routes must keep compatibility rules and tested cleanup backlog visible.',
    markers: [
      'Compatibility rules',
      'Cleanup backlog',
      'Quality scorecard',
      'Formal evidence status',
      'Counterexample GWT summary',
      'Change package'
    ]
  },
  {
    id: 'current-state-state-legend',
    file: 'docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md',
    description: 'Current-state report must keep the assurance maturity state legend discoverable.',
    markers: [
      '`ready`',
      '`partial`',
      '`preview`',
      '`missing`',
      '`duplicate`',
      '`obsolete`'
    ]
  }
];

function parseArgs(argv) {
  const args = {
    root: DEFAULT_ROOT,
    json: false,
    help: false
  };
  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if (arg === '--root' && next) {
      args.root = next;
      i += 1;
    } else if (arg.startsWith('--root=')) {
      args.root = arg.slice('--root='.length);
    } else if (arg === '--json') {
      args.json = true;
    } else if (arg === '--help' || arg === '-h') {
      args.help = true;
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/assurance/check-contract-governance.mjs [--root <repo>] [--json]

Checks that assurance contract governance docs keep deterministic migration,
compatibility, canonical-route, and current-state markers discoverable.
`);
}

function readText(root, relativePath) {
  const absolutePath = path.resolve(root, relativePath);
  return fs.readFileSync(absolutePath, 'utf8');
}

function evaluateCheck(root, check) {
  let text = '';
  try {
    text = readText(root, check.file);
  } catch (error) {
    return {
      id: check.id,
      file: check.file,
      ok: false,
      missing: check.markers,
      error: `failed to read ${check.file}: ${error instanceof Error ? error.message : String(error)}`
    };
  }

  const missing = check.markers.filter((marker) => !text.includes(marker));
  return {
    id: check.id,
    file: check.file,
    ok: missing.length === 0,
    missing
  };
}

function run(root) {
  const resolvedRoot = path.resolve(root);
  const checks = CHECKS.map((check) => evaluateCheck(resolvedRoot, check));
  const failures = checks.filter((check) => !check.ok);
  return {
    root: resolvedRoot,
    ok: failures.length === 0,
    checks,
    failures
  };
}

function printTextReport(result) {
  console.log('Assurance contract governance check');
  console.log(`- root: ${result.root}`);
  console.log(`- checks: ${result.checks.length}`);
  console.log(`- failures: ${result.failures.length}`);
  for (const check of result.checks) {
    if (check.ok) {
      console.log(`✓ ${check.id}: ${check.file}`);
      continue;
    }
    console.log(`✗ ${check.id}: ${check.file}`);
    if (check.error) console.log(`  - ${check.error}`);
    for (const marker of check.missing) {
      console.log(`  - missing marker: ${marker}`);
    }
  }
}

function main() {
  let args;
  try {
    args = parseArgs(process.argv);
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    return 2;
  }
  if (args.help) {
    printHelp();
    return 0;
  }
  const result = run(args.root);
  if (args.json) {
    console.log(JSON.stringify(result, null, 2));
  } else {
    printTextReport(result);
  }
  return result.ok ? 0 : 1;
}

process.exitCode = main();
