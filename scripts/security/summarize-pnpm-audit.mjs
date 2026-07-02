#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const SCHEMA_VERSION = 'pnpm-audit-classification/v1';
const CONTRACT_ID = 'pnpm-audit-classification.v1';
const DEFAULT_GENERATED_AT = '1970-01-01T00:00:00.000Z';
const DEFAULT_OUTPUT_JSON = 'artifacts/security/pnpm-audit-classification.json';
const DEFAULT_OUTPUT_MD = 'artifacts/security/pnpm-audit-classification.md';
const PRIORITIZED_LIMIT = 30;
const SAMPLE_PATH_LIMIT = 5;
const SEVERITY_ORDER = ['critical', 'high', 'moderate', 'low', 'info', 'unknown'];
const PRODUCTION_SECTIONS = new Set(['dependencies', 'optionalDependencies', 'peerDependencies']);
const TEST_TOOLING_DEPENDENCIES = new Set([
  '@playwright/test',
  '@storybook/test',
  '@vitest/coverage-v8',
  'c8',
  'jest',
  'jsdom',
  'nyc',
  'playwright',
  'tsd',
  'vitest',
]);

function readRequiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (!value || value.startsWith('--')) {
    throw new Error(`missing value for ${option}`);
  }
  return value;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    repoRoot: process.cwd(),
    input: null,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    generatedAt: DEFAULT_GENERATED_AT,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '--repo-root') {
      options.repoRoot = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--input' || arg === '-i') {
      options.input = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  if (!options.help && !options.input) {
    throw new Error('--input is required');
  }

  if (!Number.isNaN(Date.parse(options.generatedAt))) {
    options.generatedAt = new Date(options.generatedAt).toISOString();
  } else if (!options.help) {
    throw new Error(`--generated-at must be an ISO date-time: ${options.generatedAt}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/security/summarize-pnpm-audit.mjs --input <audit-json> [options]\n\nOptions:\n  --repo-root <dir>       repository root (default: current working directory)\n  --input, -i <path>      pnpm audit --json output to classify (required)\n  --output-json <path>    JSON output path (default: ${DEFAULT_OUTPUT_JSON})\n  --output-md <path>      Markdown output path (default: ${DEFAULT_OUTPUT_MD})\n  --generated-at <iso>    artifact timestamp (default: ${DEFAULT_GENERATED_AT} for deterministic output)\n  --help, -h              show this help\n`);
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function writeFile(filePath, content) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, content);
}

function writeJson(filePath, payload) {
  writeFile(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function toPosix(inputPath) {
  return inputPath.split(path.sep).join('/');
}

function resolveFromRoot(repoRoot, inputPath) {
  return path.isAbsolute(inputPath) ? inputPath : path.join(repoRoot, inputPath);
}

function relativeFromRoot(repoRoot, targetPath) {
  const relativePath = path.relative(repoRoot, targetPath);
  if (!relativePath || relativePath.startsWith('..')) {
    return toPosix(targetPath);
  }
  return toPosix(relativePath);
}

function normalizeWorkspaceRoot(token) {
  return token.replaceAll('__', '/');
}

export function stripPackageVersion(token) {
  const clean = token.trim();
  if (!clean) {
    return '';
  }
  if (clean.startsWith('@')) {
    const slashIndex = clean.indexOf('/');
    const versionIndex = clean.lastIndexOf('@');
    return slashIndex >= 0 && versionIndex > slashIndex ? clean.slice(0, versionIndex) : clean;
  }
  const versionIndex = clean.lastIndexOf('@');
  return versionIndex > 0 ? clean.slice(0, versionIndex) : clean;
}

function isWorkspaceRootToken(token) {
  const normalized = normalizeWorkspaceRoot(token);
  return normalized.startsWith('apps/')
    || normalized.startsWith('packages/')
    || normalized.startsWith('examples/');
}

export function parseDependencyPath(pathText) {
  const parts = String(pathText || '')
    .split('>')
    .map((part) => part.trim())
    .filter(Boolean);
  const workspaceRoots = [];
  const packages = [];

  for (const part of parts) {
    if (part === '.') {
      continue;
    }
    if (isWorkspaceRootToken(part)) {
      workspaceRoots.push(normalizeWorkspaceRoot(part));
      continue;
    }
    packages.push(stripPackageVersion(part));
  }

  return {
    raw: String(pathText || ''),
    workspaceRoots: uniqueSorted(workspaceRoots),
    packages: packages.filter(Boolean),
  };
}

function readPackageManifest(filePath, manifestRoot) {
  const payload = readJson(filePath);
  return {
    manifestRoot,
    path: toPosix(path.relative(process.cwd(), filePath)),
    name: payload.name || null,
    packageManager: payload.packageManager || null,
    dependencies: payload.dependencies || {},
    devDependencies: payload.devDependencies || {},
    optionalDependencies: payload.optionalDependencies || {},
    peerDependencies: payload.peerDependencies || {},
  };
}

function listWorkspaceManifestPaths(repoRoot) {
  const roots = ['apps', 'packages', 'examples'];
  const manifests = [];
  for (const root of roots) {
    const absoluteRoot = path.join(repoRoot, root);
    if (!fs.existsSync(absoluteRoot)) {
      continue;
    }
    for (const entry of fs.readdirSync(absoluteRoot, { withFileTypes: true })) {
      if (!entry.isDirectory()) {
        continue;
      }
      const manifestPath = path.join(absoluteRoot, entry.name, 'package.json');
      if (fs.existsSync(manifestPath)) {
        manifests.push({
          manifestRoot: toPosix(path.join(root, entry.name)),
          manifestPath,
        });
      }
    }
  }
  return manifests.sort((left, right) => left.manifestRoot.localeCompare(right.manifestRoot));
}

function readPackageManifests(repoRoot) {
  const rootManifestPath = path.join(repoRoot, 'package.json');
  const manifests = [];
  if (fs.existsSync(rootManifestPath)) {
    manifests.push(readPackageManifest(rootManifestPath, '.'));
  }
  for (const { manifestRoot, manifestPath } of listWorkspaceManifestPaths(repoRoot)) {
    manifests.push(readPackageManifest(manifestPath, manifestRoot));
  }
  return manifests;
}

function dependencySection(manifest, packageName) {
  if (Object.prototype.hasOwnProperty.call(manifest.dependencies, packageName)) {
    return 'dependencies';
  }
  if (Object.prototype.hasOwnProperty.call(manifest.optionalDependencies, packageName)) {
    return 'optionalDependencies';
  }
  if (Object.prototype.hasOwnProperty.call(manifest.peerDependencies, packageName)) {
    return 'peerDependencies';
  }
  if (Object.prototype.hasOwnProperty.call(manifest.devDependencies, packageName)) {
    return 'devDependencies';
  }
  return null;
}

function dependencyExposure(section, packageName) {
  if (!section) {
    return 'unknown';
  }
  if (PRODUCTION_SECTIONS.has(section)) {
    return 'production';
  }
  if (section === 'devDependencies' && isTestDependency(packageName)) {
    return 'test';
  }
  if (section === 'devDependencies') {
    return 'development';
  }
  return 'unknown';
}

function isTestDependency(packageName) {
  return TEST_TOOLING_DEPENDENCIES.has(packageName)
    || packageName.startsWith('@vitest/')
    || packageName.startsWith('vitest-')
    || packageName.startsWith('@playwright/');
}

function resolveManifestForPath(manifestsByRoot, parsedPath) {
  const preferredRoot = parsedPath.workspaceRoots[0] || '.';
  return manifestsByRoot.get(preferredRoot) || manifestsByRoot.get('.') || null;
}

function classifyFindingPath(pathText, manifestsByRoot) {
  const parsedPath = parseDependencyPath(pathText);
  const manifest = resolveManifestForPath(manifestsByRoot, parsedPath);
  const rootDependency = parsedPath.packages[0] || null;
  const section = rootDependency && manifest ? dependencySection(manifest, rootDependency) : null;
  return {
    path: String(pathText || ''),
    workspaceRoot: parsedPath.workspaceRoots[0] || '.',
    rootDependency,
    dependencySection: section,
    exposure: dependencyExposure(section, rootDependency || ''),
    packageChain: parsedPath.packages,
  };
}

function uniqueSorted(values) {
  return Array.from(new Set(values.filter((value) => value !== null && value !== undefined && value !== ''))).sort();
}

function uniqueObjects(values, keyFn) {
  const seen = new Set();
  const result = [];
  for (const value of values) {
    const key = keyFn(value);
    if (seen.has(key)) {
      continue;
    }
    seen.add(key);
    result.push(value);
  }
  return result;
}

function severityRank(severity) {
  const rank = SEVERITY_ORDER.indexOf(severity);
  return rank >= 0 ? rank : SEVERITY_ORDER.indexOf('unknown');
}

function exposureRank(exposure) {
  const ranks = {
    production: 0,
    test: 1,
    development: 2,
    workspace: 3,
    unknown: 4,
  };
  return ranks[exposure] ?? ranks.unknown;
}

function directnessRank(directness) {
  return directness === 'direct' ? 0 : 1;
}

function normalizeSeverity(severity) {
  const lower = String(severity || 'unknown').toLowerCase();
  return SEVERITY_ORDER.includes(lower) ? lower : 'unknown';
}

function buildActionIndex(actions) {
  const byAdvisoryId = new Map();

  for (const action of Array.isArray(actions) ? actions : []) {
    const actionName = String(action.action || 'unknown');
    for (const resolve of Array.isArray(action.resolves) ? action.resolves : []) {
      const id = String(resolve.id);
      if (!byAdvisoryId.has(id)) {
        byAdvisoryId.set(id, []);
      }
      byAdvisoryId.get(id).push({
        action: actionName,
        module: action.module || null,
        target: action.target || null,
        depth: typeof action.depth === 'number' ? action.depth : null,
        path: resolve.path || null,
        dev: typeof resolve.dev === 'boolean' ? resolve.dev : null,
      });
    }
  }

  return { byAdvisoryId };
}

function directDependencyEntries(manifests, packageName) {
  const entries = [];
  for (const manifest of manifests) {
    const section = dependencySection(manifest, packageName);
    if (!section) {
      continue;
    }
    entries.push({
      manifestRoot: manifest.manifestRoot,
      section,
      exposure: dependencyExposure(section, packageName),
    });
  }
  return entries;
}

function aggregateExposure(pathClassifications, rootDependencies) {
  const exposures = new Set([
    ...pathClassifications.map((classification) => classification.exposure),
    ...rootDependencies.map((dependency) => dependency.exposure),
  ].filter(Boolean));

  if (exposures.has('production')) {
    return 'production';
  }
  if (exposures.has('test')) {
    return 'test';
  }
  if (exposures.has('development')) {
    return 'development';
  }
  if (pathClassifications.some((classification) => classification.workspaceRoot !== '.')) {
    return 'workspace';
  }
  return 'unknown';
}

function remediationStatus(actions) {
  if (actions.some((action) => action.action === 'update' && action.target)) {
    return 'update-available';
  }
  if (actions.some((action) => action.action === 'install' && action.target)) {
    return 'install-available';
  }
  if (actions.some((action) => action.action === 'review')) {
    return 'manual-review';
  }
  if (actions.length > 0) {
    return 'action-present';
  }
  return 'not-reported';
}

function advisoryFindingPaths(advisory) {
  const paths = [];
  for (const finding of Array.isArray(advisory.findings) ? advisory.findings : []) {
    for (const findingPath of Array.isArray(finding.paths) ? finding.paths : []) {
      paths.push(String(findingPath));
    }
  }
  return paths;
}

function advisoryAffectedVersions(advisory) {
  return uniqueSorted((Array.isArray(advisory.findings) ? advisory.findings : [])
    .map((finding) => finding.version ? String(finding.version) : null));
}

function cvssScore(advisory) {
  if (typeof advisory.cvss?.score === 'number') {
    return advisory.cvss.score;
  }
  if (typeof advisory.cvss?.score === 'string') {
    const parsed = Number.parseFloat(advisory.cvss.score);
    return Number.isNaN(parsed) ? null : parsed;
  }
  return null;
}

function classifyAdvisory(id, advisory, context) {
  const { manifests, manifestsByRoot, actionsByAdvisoryId } = context;
  const severity = normalizeSeverity(advisory.severity);
  const moduleName = String(advisory.module_name || advisory.moduleName || 'unknown');
  const paths = advisoryFindingPaths(advisory);
  const pathClassifications = paths.map((findingPath) => classifyFindingPath(findingPath, manifestsByRoot));
  const directDependencies = directDependencyEntries(manifests, moduleName);
  const rootDependencies = uniqueObjects(
    pathClassifications
      .filter((classification) => classification.rootDependency)
      .map((classification) => ({
        name: classification.rootDependency,
        manifestRoot: classification.workspaceRoot,
        section: classification.dependencySection || 'unknown',
        exposure: classification.exposure,
      })),
    (dependency) => `${dependency.manifestRoot}:${dependency.name}:${dependency.section}`,
  ).sort((left, right) => `${left.manifestRoot}:${left.name}`.localeCompare(`${right.manifestRoot}:${right.name}`));
  const actions = uniqueObjects(actionsByAdvisoryId.get(String(id)) || [], (action) => [
    action.action,
    action.module || '',
    action.target || '',
    action.depth ?? '',
    action.path || '',
  ].join('|'));

  return {
    id: String(id),
    moduleName,
    severity,
    title: advisory.title || '',
    vulnerableVersions: advisory.vulnerable_versions || null,
    patchedVersions: advisory.patched_versions || null,
    recommendation: advisory.recommendation || null,
    url: advisory.url || null,
    githubAdvisoryId: advisory.github_advisory_id || null,
    cves: Array.isArray(advisory.cves) ? advisory.cves : [],
    cvssScore: cvssScore(advisory),
    directness: directDependencies.length > 0 ? 'direct' : 'transitive',
    directDependencies,
    exposure: aggregateExposure(pathClassifications, rootDependencies),
    rootDependencies,
    workspaceRoots: uniqueSorted(pathClassifications
      .map((classification) => classification.workspaceRoot)
      .filter((workspaceRoot) => workspaceRoot !== '.')),
    affectedVersions: advisoryAffectedVersions(advisory),
    findingCount: Array.isArray(advisory.findings) ? advisory.findings.length : 0,
    pathCount: paths.length,
    samplePaths: paths.slice(0, SAMPLE_PATH_LIMIT),
    remediation: actions.map((action) => ({
      action: action.action,
      module: action.module,
      target: action.target,
      depth: action.depth,
      path: action.path,
      dev: action.dev,
    })),
    remediationStatus: remediationStatus(actions),
  };
}

function countBy(values, keyFn) {
  return values.reduce((accumulator, value) => {
    const key = keyFn(value);
    accumulator[key] = (accumulator[key] || 0) + 1;
    return accumulator;
  }, {});
}

function sortedAdvisories(advisories) {
  return [...advisories].sort((left, right) => {
    const severityDelta = severityRank(left.severity) - severityRank(right.severity);
    if (severityDelta !== 0) {
      return severityDelta;
    }
    const exposureDelta = exposureRank(left.exposure) - exposureRank(right.exposure);
    if (exposureDelta !== 0) {
      return exposureDelta;
    }
    const directnessDelta = directnessRank(left.directness) - directnessRank(right.directness);
    if (directnessDelta !== 0) {
      return directnessDelta;
    }
    const pathDelta = right.pathCount - left.pathCount;
    if (pathDelta !== 0) {
      return pathDelta;
    }
    return left.moduleName.localeCompare(right.moduleName);
  });
}

function buildSummary(advisories, actions, auditMetadata) {
  const criticalHigh = advisories.filter((advisory) => ['critical', 'high'].includes(advisory.severity));
  const actionCounts = countBy(Array.isArray(actions) ? actions : [], (action) => String(action.action || 'unknown'));
  const auditVulnerabilityCounts = auditMetadata?.vulnerabilities || {};
  return {
    advisoryCount: advisories.length,
    bySeverity: {
      critical: advisories.filter((advisory) => advisory.severity === 'critical').length,
      high: advisories.filter((advisory) => advisory.severity === 'high').length,
      moderate: advisories.filter((advisory) => advisory.severity === 'moderate').length,
      low: advisories.filter((advisory) => advisory.severity === 'low').length,
      info: advisories.filter((advisory) => advisory.severity === 'info').length,
      unknown: advisories.filter((advisory) => advisory.severity === 'unknown').length,
    },
    auditMetadata: auditMetadata || {},
    auditVulnerabilityCounts,
    criticalHighAdvisoryCount: criticalHigh.length,
    criticalHighUniqueModules: uniqueSorted(criticalHigh.map((advisory) => advisory.moduleName)),
    directAdvisoryCount: advisories.filter((advisory) => advisory.directness === 'direct').length,
    transitiveAdvisoryCount: advisories.filter((advisory) => advisory.directness === 'transitive').length,
    exposureCounts: countBy(advisories, (advisory) => advisory.exposure),
    remediationStatusCounts: countBy(advisories, (advisory) => advisory.remediationStatus),
    actionCounts,
    updateActionCount: actionCounts.update || 0,
    reviewActionCount: actionCounts.review || 0,
  };
}

function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function describeAuditErrorPayload(audit) {
  if (isPlainObject(audit.error)) {
    const code = audit.error.code ? String(audit.error.code) : null;
    const message = audit.error.message ? String(audit.error.message) : null;
    return [code, message].filter(Boolean).join(': ') || 'error object';
  }
  if (audit.error) {
    return String(audit.error);
  }
  if (audit.code) {
    return String(audit.code);
  }
  return 'unknown error payload';
}

function assertPnpmAuditReport(audit, inputPath) {
  if (!isPlainObject(audit)) {
    throw new Error(`pnpm audit input is not a JSON object: ${inputPath}`);
  }
  if (audit.error || audit.code) {
    throw new Error(`pnpm audit input is an error payload (${describeAuditErrorPayload(audit)}): ${inputPath}`);
  }
  if (!isPlainObject(audit.advisories)) {
    throw new Error(`pnpm audit input is missing an advisories object: ${inputPath}`);
  }
  if (!Array.isArray(audit.actions)) {
    throw new Error(`pnpm audit input is missing an actions array: ${inputPath}`);
  }
  if (!isPlainObject(audit.metadata)) {
    throw new Error(`pnpm audit input is missing a metadata object: ${inputPath}`);
  }
}

export function summarizePnpmAudit(options) {
  const repoRoot = path.resolve(options.repoRoot || process.cwd());
  const inputPath = resolveFromRoot(repoRoot, options.input);
  const audit = readJson(inputPath);
  assertPnpmAuditReport(audit, inputPath);
  const manifests = readPackageManifests(repoRoot);
  const manifestsByRoot = new Map(manifests.map((manifest) => [manifest.manifestRoot, manifest]));
  const { byAdvisoryId: actionsByAdvisoryId } = buildActionIndex(audit.actions || []);
  const advisories = sortedAdvisories(Object.entries(audit.advisories || {}).map(([id, advisory]) => classifyAdvisory(id, advisory, {
    manifests,
    manifestsByRoot,
    actionsByAdvisoryId,
  })));
  const criticalHigh = sortedAdvisories(advisories.filter((advisory) => ['critical', 'high'].includes(advisory.severity)));
  const rootManifest = manifests.find((manifest) => manifest.manifestRoot === '.');

  return {
    schemaVersion: SCHEMA_VERSION,
    contractId: CONTRACT_ID,
    generatedAt: options.generatedAt,
    source: {
      input: relativeFromRoot(repoRoot, inputPath),
      packageManager: rootManifest?.packageManager || null,
      auditMetadata: audit.metadata || {},
    },
    enforcement: {
      mode: 'report-only',
      gateWeakening: false,
      rationale: 'Classifies the current pnpm audit advisory set for remediation planning without changing CI enforcement thresholds.',
    },
    summary: buildSummary(advisories, audit.actions || [], audit.metadata),
    manifests: manifests.map((manifest) => ({
      manifestRoot: manifest.manifestRoot,
      name: manifest.name,
    })),
    advisories,
    prioritized: criticalHigh.slice(0, PRIORITIZED_LIMIT).map((advisory) => ({
      id: advisory.id,
      moduleName: advisory.moduleName,
      severity: advisory.severity,
      exposure: advisory.exposure,
      directness: advisory.directness,
      pathCount: advisory.pathCount,
      remediationStatus: advisory.remediationStatus,
      rootDependencies: advisory.rootDependencies,
      patchedVersions: advisory.patchedVersions,
      remediation: advisory.remediation,
      url: advisory.url,
    })),
  };
}

function markdownEscape(value) {
  return String(value ?? '')
    .replaceAll('|', '\\|')
    .replaceAll('\n', '<br>');
}

function formatRootDependencies(rootDependencies) {
  if (!rootDependencies.length) {
    return 'unknown';
  }
  return rootDependencies.map((dependency) => `${dependency.manifestRoot}:${dependency.name} (${dependency.section})`).join('<br>');
}

function formatRemediation(advisory) {
  if (!advisory.remediation.length) {
    return advisory.remediationStatus;
  }
  return advisory.remediation
    .map((item) => `${item.action}${item.module ? ` ${item.module}` : ''}${item.target ? ` -> ${item.target}` : ''}`)
    .join('<br>');
}

export function renderMarkdown(report) {
  const rows = report.prioritized.map((advisory) => [
    advisory.severity,
    advisory.moduleName,
    advisory.exposure,
    advisory.directness,
    formatRootDependencies(advisory.rootDependencies),
    advisory.pathCount,
    advisory.patchedVersions || 'not specified',
    formatRemediation(advisory),
  ]);

  const table = rows.length > 0
    ? rows.map((row) => `| ${row.map(markdownEscape).join(' | ')} |`).join('\n')
    : '| none | none | none | none | none | 0 | none | none |';

  return `# pnpm audit advisory classification\n\nGenerated at: ${report.generatedAt}\n\n## Enforcement boundary\n\n- Mode: **${report.enforcement.mode}**\n- Gate weakening: **${report.enforcement.gateWeakening ? 'yes' : 'no'}**\n- Rationale: ${report.enforcement.rationale}\n\n## Summary\n\n- Advisories: ${report.summary.advisoryCount}\n- Severity counts: critical=${report.summary.bySeverity.critical}, high=${report.summary.bySeverity.high}, moderate=${report.summary.bySeverity.moderate}, low=${report.summary.bySeverity.low}\n- Critical/high advisories: ${report.summary.criticalHighAdvisoryCount}\n- Critical/high unique modules: ${report.summary.criticalHighUniqueModules.length}\n- Direct advisories: ${report.summary.directAdvisoryCount}\n- Transitive advisories: ${report.summary.transitiveAdvisoryCount}\n- Exposure counts: ${Object.entries(report.summary.exposureCounts).map(([key, value]) => `${key}=${value}`).join(', ') || 'none'}\n- Remediation status counts: ${Object.entries(report.summary.remediationStatusCounts).map(([key, value]) => `${key}=${value}`).join(', ') || 'none'}\n\n## Prioritized critical/high surfaces\n\n| Severity | Module | Exposure | Directness | Root dependency surfaces | Paths | Patched versions | pnpm action |\n|---|---|---|---|---|---:|---|---|\n${table}\n\n## Operator notes\n\n- This report is generated from \`pnpm audit --json\` output and package manifest classification.\n- The severity counts above are advisory-object counts. When present, pnpm metadata vulnerability counts are: ${Object.entries(report.summary.auditVulnerabilityCounts).map(([key, value]) => `${key}=${value}`).join(', ') || 'not reported'}.\n- \`production\` exposure means at least one advisory path starts from a dependency/optional/peer dependency manifest section.\n- \`test\` and \`development\` exposure mean the path was reachable only through devDependency surfaces observed in the repository manifests.\n- \`unknown\` exposure requires manual review before using the advisory as a gate exception or waiver.\n- This report does not approve waivers, baselines, or CI threshold changes.\n`;
}

export function writePnpmAuditSummary(report, options) {
  const repoRoot = path.resolve(options.repoRoot || process.cwd());
  const outputJson = resolveFromRoot(repoRoot, options.outputJson);
  const outputMd = resolveFromRoot(repoRoot, options.outputMd);
  writeJson(outputJson, report);
  writeFile(outputMd, renderMarkdown(report));
  return {
    outputJson,
    outputMd,
  };
}

function main() {
  try {
    const options = parseArgs();
    if (options.help) {
      printHelp();
      return;
    }
    const report = summarizePnpmAudit(options);
    const outputs = writePnpmAuditSummary(report, options);
    process.stdout.write(`pnpm audit classification written to ${outputs.outputJson} and ${outputs.outputMd}\n`);
  } catch (error) {
    process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  main();
}
