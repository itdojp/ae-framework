#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import micromatch from 'micromatch';

const DEFAULT_RULES_PATH = 'configs/context-pack/dependency-rules.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/deps-summary.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/deps-summary.md';
const SOURCE_EXTENSIONS = ['.ts', '.tsx', '.js', '.mjs', '.cjs', '.mts', '.cts'];
const JS_SPECIFIER_EXTENSIONS = ['.js', '.mjs', '.cjs'];
const ROOT_DIR = path.resolve(process.cwd());

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack dependency boundary checker

Usage:
  node scripts/context-pack/check-deps.mjs [options]

Options:
  --rules <path>            Dependency rule config path (default: ${DEFAULT_RULES_PATH})
  --sources <glob>          Source glob (repeatable, comma-separated supported)
  --strict <true|false>     Strict mode (default: false)
  --report-json <path>      JSON report path (default: ${DEFAULT_REPORT_JSON})
  --report-md <path>        Markdown report path (default: ${DEFAULT_REPORT_MD})
  --help, -h                Show this help
`);
}

function splitPatterns(rawValue) {
  const chunks = [];
  let buffer = '';
  let braceDepth = 0;
  for (const char of rawValue) {
    if (char === '{') {
      braceDepth += 1;
      buffer += char;
      continue;
    }
    if (char === '}') {
      braceDepth = Math.max(0, braceDepth - 1);
      buffer += char;
      continue;
    }
    if (char === ',' && braceDepth === 0) {
      const trimmed = buffer.trim();
      if (trimmed.length > 0) {
        chunks.push(trimmed);
      }
      buffer = '';
      continue;
    }
    buffer += char;
  }
  const tail = buffer.trim();
  if (tail.length > 0) {
    chunks.push(tail);
  }
  return chunks;
}

function parseBoolean(value, optionName) {
  const normalized = String(value).trim().toLowerCase();
  if (normalized === 'true' || normalized === '1' || normalized === 'yes') {
    return true;
  }
  if (normalized === 'false' || normalized === '0' || normalized === 'no') {
    return false;
  }
  throw new Error(`invalid boolean for ${optionName}: ${value}`);
}

function parseArgs(argv) {
  const options = {
    rulesPath: DEFAULT_RULES_PATH,
    sourceGlobs: [],
    strict: false,
    reportJsonPath: DEFAULT_REPORT_JSON,
    reportMarkdownPath: DEFAULT_REPORT_MD,
    help: false,
  };

  const appendSources = (rawValue) => {
    for (const pattern of splitPatterns(rawValue)) {
      options.sourceGlobs.push(pattern);
    }
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--rules') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --rules');
      }
      options.rulesPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--rules=')) {
      options.rulesPath = arg.slice('--rules='.length);
      continue;
    }
    if (arg === '--sources') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --sources');
      }
      appendSources(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--sources=')) {
      appendSources(arg.slice('--sources='.length));
      continue;
    }
    if (arg === '--strict') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --strict');
      }
      options.strict = parseBoolean(next, '--strict');
      index += 1;
      continue;
    }
    if (arg.startsWith('--strict=')) {
      options.strict = parseBoolean(arg.slice('--strict='.length), '--strict');
      continue;
    }
    if (arg === '--report-json') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --report-json');
      }
      options.reportJsonPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--report-json=')) {
      options.reportJsonPath = arg.slice('--report-json='.length);
      continue;
    }
    if (arg === '--report-md') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --report-md');
      }
      options.reportMarkdownPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--report-md=')) {
      options.reportMarkdownPath = arg.slice('--report-md='.length);
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function loadRules(rulesPath) {
  const resolvedPath = path.resolve(rulesPath);
  if (!fs.existsSync(resolvedPath)) {
    throw new Error(`rules file not found: ${resolvedPath}`);
  }
  const payload = JSON.parse(fs.readFileSync(resolvedPath, 'utf8'));
  if (!payload || typeof payload !== 'object') {
    throw new Error('rules payload must be an object');
  }
  if (!Array.isArray(payload.sourceGlobs) || payload.sourceGlobs.length === 0) {
    throw new Error('rules.sourceGlobs must be a non-empty array');
  }
  if (!Array.isArray(payload.rules)) {
    throw new Error('rules.rules must be an array');
  }
  return { resolvedPath, payload };
}

function discoverSources(sourceGlobs) {
  const matched = new Set();
  for (const pattern of sourceGlobs) {
    const files = globSync(pattern, {
      nodir: true,
      absolute: true,
      ignore: ['**/node_modules/**', '**/.git/**'],
    });
    for (const filePath of files) {
      matched.add(path.normalize(filePath));
    }
  }
  return Array.from(matched).sort((left, right) => left.localeCompare(right));
}

function collectImportSpecifiers(content) {
  const imports = new Set();

  const importExportWithFrom = /(?:^|\n)\s*(?:import|export)\s+(?:type\s+)?(?:[\s\S]*?\s+from\s+|\*\s+from\s+)["']([^"']+)["']/g;
  for (const match of content.matchAll(importExportWithFrom)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }
  const sideEffectImports = /(?:^|\n)\s*import\s+["']([^"']+)["'];?/g;
  for (const match of content.matchAll(sideEffectImports)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }
  const commonJsRequires = /require\(\s*["']([^"']+)["']\s*\)/g;
  for (const match of content.matchAll(commonJsRequires)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }
  const dynamicImports = /import\(\s*["']([^"']+)["']\s*\)/g;
  for (const match of content.matchAll(dynamicImports)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }

  return Array.from(imports);
}

function resolveImportTarget(sourceFilePath, specifier) {
  if (typeof specifier !== 'string' || specifier.length === 0) {
    return null;
  }

  let basePath;
  if (specifier.startsWith('.')) {
    basePath = path.resolve(path.dirname(sourceFilePath), specifier);
  } else if (specifier.startsWith('/')) {
    basePath = path.resolve(process.cwd(), specifier.slice(1));
  } else if (specifier.startsWith('src/') || specifier.startsWith('scripts/') || specifier.startsWith('docs/')) {
    basePath = path.resolve(process.cwd(), specifier);
  } else {
    return null;
  }

  const normalizedBasePath = path.normalize(basePath);
  const candidates = [normalizedBasePath];
  const baseExtension = path.extname(normalizedBasePath);
  if (JS_SPECIFIER_EXTENSIONS.includes(baseExtension)) {
    const baseWithoutExtension = normalizedBasePath.slice(0, -baseExtension.length);
    candidates.push(
      `${baseWithoutExtension}.ts`,
      `${baseWithoutExtension}.tsx`,
      `${baseWithoutExtension}.mts`,
      `${baseWithoutExtension}.cts`,
    );
  }
  for (const extension of SOURCE_EXTENSIONS) {
    candidates.push(`${normalizedBasePath}${extension}`);
  }
  for (const extension of SOURCE_EXTENSIONS) {
    candidates.push(path.join(normalizedBasePath, `index${extension}`));
  }

  const uniqueCandidates = Array.from(new Set(candidates.map((candidate) => path.resolve(candidate))));
  for (const candidate of uniqueCandidates) {
    if (!candidate.startsWith(ROOT_DIR)) {
      continue;
    }
    if (fs.existsSync(candidate) && fs.statSync(candidate).isFile()) {
      return path.normalize(candidate);
    }
  }
  return null;
}

function buildDependencyEdges(sourceFiles) {
  const edges = [];
  const seen = new Set();

  for (const sourceFilePath of sourceFiles) {
    const content = fs.readFileSync(sourceFilePath, 'utf8');
    const specifiers = collectImportSpecifiers(content);
    for (const specifier of specifiers) {
      const targetPath = resolveImportTarget(sourceFilePath, specifier);
      if (!targetPath) {
        continue;
      }
      const from = toRelativePath(sourceFilePath);
      const to = toRelativePath(targetPath);
      const edgeKey = `${from}->${to}:${specifier}`;
      if (seen.has(edgeKey)) {
        continue;
      }
      seen.add(edgeKey);
      edges.push({ from, to, specifier });
    }
  }

  return edges;
}

function matchesAny(value, patterns) {
  if (!Array.isArray(patterns) || patterns.length === 0) {
    return false;
  }
  return micromatch.isMatch(value, patterns, { dot: true });
}

function evaluateBoundaryRules(edges, rules) {
  const violations = [];
  for (const edge of edges) {
    for (const rule of rules) {
      const fromPatterns = Array.isArray(rule.from) ? rule.from : [];
      const toPatterns = Array.isArray(rule.to) ? rule.to : [];
      if (!matchesAny(edge.from, fromPatterns)) {
        continue;
      }
      if (!matchesAny(edge.to, toPatterns)) {
        continue;
      }
      violations.push({
        type: 'boundary-violation',
        severity: 'error',
        ruleId: rule.id || '(unnamed-rule)',
        from: edge.from,
        to: edge.to,
        specifier: edge.specifier,
        reason: rule.reason || 'Dependency direction violation.',
      });
    }
  }
  return violations;
}

function detectCycles(graph) {
  const discoveredCycles = [];
  const seenSignatures = new Set();
  const stack = [];
  const state = new Map();

  const canonicalize = (cycle) => {
    const core = cycle.slice(0, -1);
    if (core.length === 0) {
      return '';
    }
    const rotations = [];
    for (let index = 0; index < core.length; index += 1) {
      const rotated = [...core.slice(index), ...core.slice(0, index)];
      rotations.push(rotated.join('->'));
    }
    rotations.sort((left, right) => left.localeCompare(right));
    return rotations[0];
  };

  const visit = (node) => {
    state.set(node, 'visiting');
    stack.push(node);

    for (const neighbor of graph.get(node) ?? []) {
      if (!graph.has(neighbor)) {
        continue;
      }
      const neighborState = state.get(neighbor);
      if (neighborState === 'visiting') {
        const start = stack.indexOf(neighbor);
        if (start !== -1) {
          const cycle = [...stack.slice(start), neighbor];
          const signature = canonicalize(cycle);
          if (!seenSignatures.has(signature)) {
            seenSignatures.add(signature);
            discoveredCycles.push(cycle);
          }
        }
      } else if (neighborState !== 'visited') {
        visit(neighbor);
      }
    }

    stack.pop();
    state.set(node, 'visited');
  };

  for (const node of graph.keys()) {
    if (state.get(node) === 'visited') {
      continue;
    }
    visit(node);
  }

  return discoveredCycles;
}

function buildCycleViolations(edges, cycleDetectionConfig) {
  const enabled = cycleDetectionConfig && cycleDetectionConfig.enabled !== false;
  if (!enabled) {
    return [];
  }

  const scope = Array.isArray(cycleDetectionConfig.scope) ? cycleDetectionConfig.scope : ['src/**'];
  const groupBy = cycleDetectionConfig.groupBy || 'src-first-segment';
  if (groupBy !== 'src-first-segment') {
    throw new Error(`unsupported cycleDetection.groupBy: ${groupBy}`);
  }

  const moduleFromPath = (value) => {
    if (!value.startsWith('src/')) {
      return null;
    }
    const parts = value.split('/');
    if (parts.length < 2) {
      return null;
    }
    return parts[1] || null;
  };

  const graph = new Map();
  const ensureNode = (node) => {
    if (!graph.has(node)) {
      graph.set(node, new Set());
    }
  };

  for (const edge of edges) {
    if (!matchesAny(edge.from, scope) || !matchesAny(edge.to, scope)) {
      continue;
    }
    const fromModule = moduleFromPath(edge.from);
    const toModule = moduleFromPath(edge.to);
    if (!fromModule || !toModule || fromModule === toModule) {
      continue;
    }
    ensureNode(fromModule);
    ensureNode(toModule);
    graph.get(fromModule)?.add(toModule);
  }

  const normalizedGraph = new Map();
  for (const [moduleName, neighbors] of graph.entries()) {
    normalizedGraph.set(moduleName, Array.from(neighbors));
  }
  const cycles = detectCycles(normalizedGraph);

  return cycles.map((cycle) => ({
    type: 'dependency-cycle',
    severity: 'error',
    ruleId: 'no-module-cycles',
    from: `src/${cycle[0]}`,
    to: `src/${cycle[cycle.length - 2]}`,
    cycle: cycle.map((segment) => `src/${segment}`),
    reason: `Dependency cycle detected: ${cycle.map((segment) => `src/${segment}`).join(' -> ')}`,
  }));
}

function escapeMarkdownTableCell(value) {
  return String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/`/g, '\\`')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');
}

function buildMarkdownReport(report) {
  const lines = [
    '# Context Pack Dependency Boundary Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Strict: ${report.strict}`,
    `- Rules: \`${report.rulesPath}\``,
    `- Source files: ${report.scannedFiles}`,
    `- Dependency edges: ${report.metrics.edgeCount}`,
    `- Boundary violations: ${report.metrics.boundaryViolationCount}`,
    `- Cycles: ${report.metrics.cycleCount}`,
    `- Rule evaluation time (ms): ${report.metrics.ruleEvaluationMs}`,
    '',
    '## Source Patterns',
    ...report.sourceGlobs.map((pattern) => `- \`${pattern}\``),
    '',
  ];

  if (report.violations.length === 0) {
    lines.push('## Violations', '', 'No dependency violations were detected.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Violations (Top 10)', '', '| Type | Rule | From | To | Reason |', '| --- | --- | --- | --- | --- |');
  for (const violation of report.violations.slice(0, 10)) {
    lines.push(
      `| ${escapeMarkdownTableCell(violation.type)} | ${escapeMarkdownTableCell(violation.ruleId)} | ${escapeMarkdownTableCell(violation.from)} | ${escapeMarkdownTableCell(violation.to)} | ${escapeMarkdownTableCell(violation.reason)} |`
    );
  }

  return `${lines.join('\n')}\n`;
}

function writeReport(report, reportJsonPath, reportMarkdownPath) {
  const resolvedJsonPath = path.resolve(reportJsonPath);
  const resolvedMarkdownPath = path.resolve(reportMarkdownPath);
  fs.mkdirSync(path.dirname(resolvedJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(resolvedMarkdownPath), { recursive: true });
  fs.writeFileSync(resolvedJsonPath, `${JSON.stringify(report, null, 2)}\n`);
  fs.writeFileSync(resolvedMarkdownPath, buildMarkdownReport(report));
  return {
    resolvedJsonPath,
    resolvedMarkdownPath,
  };
}

function main() {
  const startAt = Date.now();
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    return;
  }

  const { resolvedPath: resolvedRulesPath, payload: rulesPayload } = loadRules(options.rulesPath);
  const sourceGlobs = options.sourceGlobs.length > 0 ? options.sourceGlobs : rulesPayload.sourceGlobs;
  const sourceFiles = discoverSources(sourceGlobs);
  const edges = buildDependencyEdges(sourceFiles);

  const rules = Array.isArray(rulesPayload.rules) ? rulesPayload.rules : [];
  const ruleEvalStart = Date.now();
  const boundaryViolations = evaluateBoundaryRules(edges, rules);
  const cycleViolations = buildCycleViolations(edges, rulesPayload.cycleDetection);
  const ruleEvaluationMs = Date.now() - ruleEvalStart;
  const violations = [...boundaryViolations, ...cycleViolations];

  const strict = options.strict;
  const status = violations.length === 0 ? 'pass' : strict ? 'fail' : 'warn';
  const report = {
    schemaVersion: 'context-pack-deps-summary/v1',
    generatedAt: new Date().toISOString(),
    status,
    strict,
    rulesPath: toRelativePath(resolvedRulesPath),
    sourceGlobs,
    scannedFiles: sourceFiles.length,
    metrics: {
      edgeCount: edges.length,
      boundaryViolationCount: boundaryViolations.length,
      cycleCount: cycleViolations.length,
      ruleEvaluationMs,
      durationMs: Date.now() - startAt,
    },
    violations,
  };

  const reportPaths = writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack:deps] report(json): ${toRelativePath(reportPaths.resolvedJsonPath)}\n`);
  process.stdout.write(`[context-pack:deps] report(md): ${toRelativePath(reportPaths.resolvedMarkdownPath)}\n`);
  process.stdout.write(`[context-pack:deps] status=${status} violations=${violations.length}\n`);

  if (strict && violations.length > 0) {
    process.stderr.write(`[context-pack:deps] dependency violations detected in strict mode (${violations.length})\n`);
    process.exit(2);
  }
}

try {
  main();
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  process.stderr.write(`[context-pack:deps] failed: ${message}\n`);
  process.exit(1);
}
