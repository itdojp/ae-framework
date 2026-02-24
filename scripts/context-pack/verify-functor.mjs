#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import yaml from 'yaml';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import micromatch from 'micromatch';

const DEFAULT_MAP_PATH = 'spec/context-pack/functor-map.json';
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-functor-map.schema.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/context-pack-functor-report.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/context-pack-functor-report.md';
const SOURCE_EXTENSIONS = ['.ts', '.tsx', '.js', '.mjs', '.cjs', '.mts', '.cts'];
const JS_SPECIFIER_EXTENSIONS = ['.js', '.mjs', '.cjs'];
const ROOT_DIR = path.resolve(process.cwd());

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack Functor validator

Usage:
  node scripts/context-pack/verify-functor.mjs [options]

Options:
  --map <path>                  Functor map JSON path (default: ${DEFAULT_MAP_PATH})
  --schema <path>               JSON Schema path (default: ${DEFAULT_SCHEMA_PATH})
  --report-json <path>          JSON report path (default: ${DEFAULT_REPORT_JSON})
  --report-md <path>            Markdown report path (default: ${DEFAULT_REPORT_MD})
  --context-pack-sources <glob> Override context-pack source glob (repeatable, comma-separated)
  --help, -h                    Show this help
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

function parseArgs(argv) {
  const options = {
    mapPath: DEFAULT_MAP_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    reportJsonPath: DEFAULT_REPORT_JSON,
    reportMarkdownPath: DEFAULT_REPORT_MD,
    contextPackSourcesOverride: [],
    help: false,
  };

  const appendSources = (rawValue) => {
    for (const value of splitPatterns(rawValue)) {
      options.contextPackSourcesOverride.push(value);
    }
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--map') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --map');
      }
      options.mapPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--map=')) {
      options.mapPath = arg.slice('--map='.length);
      continue;
    }
    if (arg === '--schema') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --schema');
      }
      options.schemaPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--schema=')) {
      options.schemaPath = arg.slice('--schema='.length);
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
    if (arg === '--context-pack-sources') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --context-pack-sources');
      }
      appendSources(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--context-pack-sources=')) {
      appendSources(arg.slice('--context-pack-sources='.length));
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function loadJsonFile(filePath) {
  const resolvedPath = path.resolve(filePath);
  if (!fs.existsSync(resolvedPath)) {
    throw new Error(`file not found: ${resolvedPath}`);
  }
  try {
    const data = JSON.parse(fs.readFileSync(resolvedPath, 'utf8'));
    return { resolvedPath, data };
  } catch (error) {
    throw new Error(`failed to parse JSON: ${resolvedPath} (${error instanceof Error ? error.message : String(error)})`);
  }
}

function validateFunctorMap(mapPayload, schemaPath) {
  const schemaRaw = fs.readFileSync(schemaPath, 'utf8');
  const schema = JSON.parse(schemaRaw);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const valid = validate(mapPayload);
  if (valid) {
    return [];
  }
  return (validate.errors ?? []).map((error) => ({
    type: 'functor-map-schema-invalid',
    severity: 'error',
    message: `${error.instancePath || '/'} ${error.message || 'schema validation failed'}`,
    rule: error.keyword,
  }));
}

function discoverSources(sourcePatterns) {
  const matched = new Set();
  for (const pattern of sourcePatterns) {
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

function parseContextPackFile(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  const lowerPath = filePath.toLowerCase();
  if (lowerPath.endsWith('.yml') || lowerPath.endsWith('.yaml')) {
    return yaml.parse(raw);
  }
  return JSON.parse(raw);
}

function toUniqueIds(input) {
  if (!Array.isArray(input)) {
    return [];
  }
  const ids = input
    .map((value) => (value && typeof value === 'object' ? value.id : undefined))
    .filter((value) => typeof value === 'string' && value.trim().length > 0)
    .map((value) => value.trim());
  return Array.from(new Set(ids));
}

function collectContextPackIds(contextPackFiles, violations) {
  const objectIds = new Set();
  const morphismIds = new Set();

  for (const filePath of contextPackFiles) {
    try {
      const payload = parseContextPackFile(filePath);
      if (!payload || typeof payload !== 'object') {
        continue;
      }
      for (const id of toUniqueIds(payload.objects)) {
        objectIds.add(id);
      }
      for (const id of toUniqueIds(payload.morphisms)) {
        morphismIds.add(id);
      }
    } catch (error) {
      violations.push({
        type: 'context-pack-parse-error',
        severity: 'error',
        file: toRelativePath(filePath),
        message: error instanceof Error ? error.message : String(error),
      });
    }
  }

  return {
    objectIds: Array.from(objectIds),
    morphismIds: Array.from(morphismIds),
  };
}

function resolveImportTarget(sourceFilePath, importPathValue) {
  if (typeof importPathValue !== 'string' || importPathValue.length === 0) {
    return null;
  }

  let basePath;
  if (importPathValue.startsWith('.')) {
    basePath = path.resolve(path.dirname(sourceFilePath), importPathValue);
  } else if (importPathValue.startsWith('/')) {
    basePath = path.resolve(process.cwd(), importPathValue.slice(1));
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

  const isInsideRepository = (candidatePath) => {
    const relative = path.relative(ROOT_DIR, candidatePath);
    return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
  };

  const uniqueCandidates = Array.from(new Set(candidates.map((candidate) => path.normalize(candidate))));
  for (const candidate of uniqueCandidates) {
    const resolvedCandidate = path.normalize(path.resolve(candidate));
    if (!isInsideRepository(resolvedCandidate)) {
      continue;
    }
    if (fs.existsSync(resolvedCandidate) && fs.statSync(resolvedCandidate).isFile()) {
      return resolvedCandidate;
    }
  }
  return null;
}

function collectImports(fileContent) {
  const imports = new Set();
  const importExportWithFrom = /(?:^|\n)\s*(?:import|export)\s+(?:type\s+)?(?:[\s\S]*?\s+from\s+|\*\s+from\s+)["']([^"']+)["']/g;
  for (const match of fileContent.matchAll(importExportWithFrom)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }
  const sideEffectImports = /(?:^|\n)\s*import\s+["']([^"']+)["'];?/g;
  for (const match of fileContent.matchAll(sideEffectImports)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }
  const dynamicImports = /import\(\s*["']([^"']+)["']\s*\)/g;
  for (const match of fileContent.matchAll(dynamicImports)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }
  const requireCalls = /\brequire\(\s*["']([^"']+)["']\s*\)/g;
  for (const match of fileContent.matchAll(requireCalls)) {
    if (match[1]) {
      imports.add(match[1]);
    }
  }
  return Array.from(imports);
}

function buildObjectFileIndex(objectMappings, violations) {
  const objectFiles = new Map();
  const fileToObject = new Map();

  for (const objectMapping of objectMappings) {
    const matchedFiles = new Set();
    for (const moduleGlob of objectMapping.moduleGlobs) {
      const files = globSync(moduleGlob, {
        nodir: true,
        absolute: true,
        ignore: ['**/node_modules/**', '**/.git/**'],
      });
      for (const filePath of files) {
        matchedFiles.add(path.normalize(filePath));
      }
    }
    const fileList = Array.from(matchedFiles).sort((left, right) => left.localeCompare(right));
    if (fileList.length === 0) {
      violations.push({
        type: 'object-module-empty',
        severity: 'error',
        objectId: objectMapping.id,
        message: `No files matched moduleGlobs for object '${objectMapping.id}'`,
      });
    }
    objectFiles.set(objectMapping.id, fileList);

    for (const filePath of fileList) {
      const existingOwner = fileToObject.get(filePath);
      if (existingOwner && existingOwner !== objectMapping.id) {
        violations.push({
          type: 'object-module-overlap',
          severity: 'error',
          objectId: objectMapping.id,
          file: toRelativePath(filePath),
          message: `File belongs to multiple object mappings: '${existingOwner}' and '${objectMapping.id}'`,
        });
        continue;
      }
      fileToObject.set(filePath, objectMapping.id);
    }
  }

  return { objectFiles, fileToObject };
}

function escapeRegexLiteral(value) {
  return value
    .replace(/\\/g, '\\\\')
    .replace(/[.*+?^${}()|[\]]/g, '\\$&');
}

function hasEntrypointSymbol(content, symbol) {
  const escapedSymbol = escapeRegexLiteral(symbol);
  const declarationPatterns = [
    new RegExp(`\\b(?:export\\s+)?(?:async\\s+)?function\\s+${escapedSymbol}\\b`),
    new RegExp(`\\b(?:export\\s+)?class\\s+${escapedSymbol}\\b`),
    new RegExp(`\\b(?:export\\s+)?(?:const|let|var|type|interface|enum)\\s+${escapedSymbol}\\b`),
    new RegExp(`(?:^|\\n)\\s*(?:public|private|protected|static|readonly|abstract|override|async|get|set\\s+)*${escapedSymbol}\\s*\\(`),
    new RegExp(`\\bexport\\s*\\{[^}]*\\b${escapedSymbol}\\b[^}]*\\}`),
  ];
  return declarationPatterns.some((pattern) => pattern.test(content));
}

function detectCycles(graph) {
  const cycles = [];
  const seenCycles = new Set();
  const visited = new Set();
  const stack = new Set();

  const canonicalize = (cycle) => {
    const core = cycle.slice(0, -1);
    if (core.length === 0) {
      return '';
    }
    const variants = [];
    for (let index = 0; index < core.length; index += 1) {
      const rotated = [...core.slice(index), ...core.slice(0, index)];
      variants.push(rotated.join('->'));
    }
    return variants.sort()[0] ?? '';
  };

  const visit = (node, pathNodes) => {
    visited.add(node);
    stack.add(node);
    pathNodes.push(node);

    const neighbors = graph.get(node) ?? [];
    for (const neighbor of neighbors) {
      if (!visited.has(neighbor)) {
        visit(neighbor, pathNodes);
        continue;
      }
      if (!stack.has(neighbor)) {
        continue;
      }
      const startIndex = pathNodes.indexOf(neighbor);
      if (startIndex < 0) {
        continue;
      }
      const cycle = [...pathNodes.slice(startIndex), neighbor];
      const key = canonicalize(cycle);
      if (!key || seenCycles.has(key)) {
        continue;
      }
      seenCycles.add(key);
      cycles.push(cycle);
    }

    pathNodes.pop();
    stack.delete(node);
  };

  for (const node of graph.keys()) {
    if (!visited.has(node)) {
      visit(node, []);
    }
  }
  return cycles;
}

function analyzeObjectDependencies(objectMappings, objectFiles, fileToObject, dependencyRules, violations) {
  const rulesByPair = new Map();
  for (const rule of dependencyRules ?? []) {
    rulesByPair.set(`${rule.from}=>${rule.to}`, Boolean(rule.allowed));
  }

  const edges = new Map();
  for (const mapping of objectMappings) {
    edges.set(mapping.id, new Set());
  }

  for (const objectMapping of objectMappings) {
    const files = objectFiles.get(objectMapping.id) ?? [];
    for (const filePath of files) {
      let content = '';
      try {
        content = fs.readFileSync(filePath, 'utf8');
      } catch {
        continue;
      }
      const imports = collectImports(content);
      for (const importPathValue of imports) {
        const resolvedImportFile = resolveImportTarget(filePath, importPathValue);
        if (!resolvedImportFile) {
          continue;
        }
        const targetObject = fileToObject.get(resolvedImportFile);
        if (!targetObject || targetObject === objectMapping.id) {
          continue;
        }

        edges.get(objectMapping.id)?.add(targetObject);
        const relativeTargetPath = toRelativePath(resolvedImportFile);

        if (Array.isArray(objectMapping.forbiddenImportsFrom) && objectMapping.forbiddenImportsFrom.length > 0) {
          if (micromatch.isMatch(relativeTargetPath, objectMapping.forbiddenImportsFrom)) {
            violations.push({
              type: 'forbidden-import',
              severity: 'error',
              objectId: objectMapping.id,
              fromObjectId: objectMapping.id,
              toObjectId: targetObject,
              file: toRelativePath(filePath),
              message: `Forbidden import detected: ${toRelativePath(filePath)} -> ${relativeTargetPath}`,
            });
          }
        }

        const ruleKey = `${objectMapping.id}=>${targetObject}`;
        if (rulesByPair.has(ruleKey) && rulesByPair.get(ruleKey) === false) {
          violations.push({
            type: 'layer-violation',
            severity: 'error',
            objectId: objectMapping.id,
            fromObjectId: objectMapping.id,
            toObjectId: targetObject,
            file: toRelativePath(filePath),
            rule: ruleKey,
            message: `Dependency rule violation: ${ruleKey} is not allowed`,
          });
        }
      }
    }
  }

  const cycleGraph = new Map();
  for (const [id, neighbors] of edges.entries()) {
    cycleGraph.set(id, Array.from(neighbors));
  }
  const cycles = detectCycles(cycleGraph);
  for (const cycle of cycles) {
    violations.push({
      type: 'object-dependency-cycle',
      severity: 'error',
      message: `Object dependency cycle detected: ${cycle.join(' -> ')}`,
    });
  }

  return {
    edgeCount: Array.from(edges.values()).reduce((sum, set) => sum + set.size, 0),
    cycleCount: cycles.length,
  };
}

function validateMorphismEntrypoints(morphismMappings, violations) {
  let checkedEntrypoints = 0;

  for (const morphismMapping of morphismMappings) {
    for (const entrypoint of morphismMapping.entrypoints) {
      checkedEntrypoints += 1;
      const resolvedFilePath = path.resolve(entrypoint.file);
      if (!fs.existsSync(resolvedFilePath)) {
        violations.push({
          type: 'morphism-entrypoint-missing-file',
          severity: 'error',
          morphismId: morphismMapping.id,
          file: toRelativePath(resolvedFilePath),
          message: `Entrypoint file not found for morphism '${morphismMapping.id}': ${entrypoint.file}`,
        });
        continue;
      }
      if (entrypoint.symbol) {
        const content = fs.readFileSync(resolvedFilePath, 'utf8');
        if (!hasEntrypointSymbol(content, entrypoint.symbol)) {
          violations.push({
            type: 'morphism-entrypoint-missing-symbol',
            severity: 'error',
            morphismId: morphismMapping.id,
            file: toRelativePath(resolvedFilePath),
            message: `Symbol '${entrypoint.symbol}' was not found in ${entrypoint.file}`,
          });
        }
      }
    }
  }

  return { checkedEntrypoints };
}

function summarizeViolations(violations) {
  const countByType = (type) => violations.filter((entry) => entry.type === type).length;
  return {
    totalViolations: violations.length,
    missingObjectMappings: countByType('object-mapping-missing'),
    unknownObjectMappings: countByType('object-mapping-unknown'),
    missingMorphismMappings: countByType('morphism-mapping-missing'),
    unknownMorphismMappings: countByType('morphism-mapping-unknown'),
    forbiddenDependencyViolations: countByType('forbidden-import') + countByType('layer-violation'),
    cycleViolations: countByType('object-dependency-cycle'),
    missingEntrypoints: countByType('morphism-entrypoint-missing-file') + countByType('morphism-entrypoint-missing-symbol'),
  };
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
    '# Context Pack Functor Validation Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Map: \`${report.mapPath}\``,
    `- Schema: \`${report.schemaPath}\``,
    `- Context pack files: ${report.scannedContextPackFiles}`,
    `- Object source files: ${report.scannedObjectFiles}`,
    `- Violations: ${report.summary.totalViolations}`,
    '',
    '## Summary',
    `- missing object mappings: ${report.summary.missingObjectMappings}`,
    `- missing morphism mappings: ${report.summary.missingMorphismMappings}`,
    `- forbidden dependency violations: ${report.summary.forbiddenDependencyViolations}`,
    `- dependency cycles: ${report.summary.cycleViolations}`,
    `- missing entrypoints: ${report.summary.missingEntrypoints}`,
    '',
  ];

  if (report.violations.length === 0) {
    lines.push('## Violations', '', 'No violations detected.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Violations', '', '| Type | Object | Morphism | File | Message |', '| --- | --- | --- | --- | --- |');
  for (const violation of report.violations) {
    lines.push(
      `| ${escapeMarkdownTableCell(violation.type)} | ${escapeMarkdownTableCell(violation.objectId || violation.fromObjectId || '-')} | ${escapeMarkdownTableCell(violation.morphismId || '-')} | ${escapeMarkdownTableCell(violation.file || '-')} | ${escapeMarkdownTableCell(violation.message)} |`,
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
}

function validateFunctor(options) {
  const { resolvedPath: resolvedMapPath, data: mapPayload } = loadJsonFile(options.mapPath);
  const resolvedSchemaPath = path.resolve(options.schemaPath);

  const violations = [];
  const schemaViolations = validateFunctorMap(mapPayload, resolvedSchemaPath);
  violations.push(...schemaViolations);

  const sourcePatterns = options.contextPackSourcesOverride.length > 0
    ? options.contextPackSourcesOverride
    : mapPayload.contextPackSources;
  const discoveredContextPackFiles = discoverSources(sourcePatterns);
  const normalizedMapPath = path.normalize(resolvedMapPath);
  const contextPackFiles = discoveredContextPackFiles.filter((sourcePath) => path.normalize(sourcePath) !== normalizedMapPath);
  if (contextPackFiles.length === 0) {
    violations.push({
      type: 'context-pack-sources-empty',
      severity: 'error',
      message: `No context-pack files matched source patterns: ${sourcePatterns.join(', ')}`,
    });
  }

  const contextIds = collectContextPackIds(contextPackFiles, violations);
  const objectMappingIds = mapPayload.objects.map((entry) => entry.id);
  const morphismMappingIds = mapPayload.morphisms.map((entry) => entry.id);

  for (const objectId of contextIds.objectIds) {
    if (!objectMappingIds.includes(objectId)) {
      violations.push({
        type: 'object-mapping-missing',
        severity: 'error',
        objectId,
        message: `Object mapping is missing for '${objectId}'`,
      });
    }
  }
  for (const objectId of objectMappingIds) {
    if (!contextIds.objectIds.includes(objectId)) {
      violations.push({
        type: 'object-mapping-unknown',
        severity: 'error',
        objectId,
        message: `Object mapping references unknown object ID '${objectId}'`,
      });
    }
  }

  for (const morphismId of contextIds.morphismIds) {
    if (!morphismMappingIds.includes(morphismId)) {
      violations.push({
        type: 'morphism-mapping-missing',
        severity: 'error',
        morphismId,
        message: `Morphism mapping is missing for '${morphismId}'`,
      });
    }
  }
  for (const morphismId of morphismMappingIds) {
    if (!contextIds.morphismIds.includes(morphismId)) {
      violations.push({
        type: 'morphism-mapping-unknown',
        severity: 'error',
        morphismId,
        message: `Morphism mapping references unknown morphism ID '${morphismId}'`,
      });
    }
  }

  const { objectFiles, fileToObject } = buildObjectFileIndex(mapPayload.objects, violations);
  const dependencyStats = analyzeObjectDependencies(
    mapPayload.objects,
    objectFiles,
    fileToObject,
    mapPayload.dependencyRules,
    violations,
  );
  const morphismStats = validateMorphismEntrypoints(mapPayload.morphisms, violations);

  const report = {
    schemaVersion: 'context-pack-functor-report/v1',
    generatedAt: new Date().toISOString(),
    mapPath: toRelativePath(resolvedMapPath),
    schemaPath: toRelativePath(resolvedSchemaPath),
    contextPackSources: sourcePatterns,
    scannedContextPackFiles: contextPackFiles.length,
    scannedObjectFiles: Array.from(objectFiles.values()).reduce((sum, files) => sum + files.length, 0),
    contextPackObjectCount: contextIds.objectIds.length,
    contextPackMorphismCount: contextIds.morphismIds.length,
    mappingObjectCount: objectMappingIds.length,
    mappingMorphismCount: morphismMappingIds.length,
    dependencyEdges: dependencyStats.edgeCount,
    checkedEntrypoints: morphismStats.checkedEntrypoints,
    summary: summarizeViolations(violations),
    status: violations.length === 0 ? 'pass' : 'fail',
    violations,
  };

  writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack:functor] report(json): ${toRelativePath(path.resolve(options.reportJsonPath))}\n`);
  process.stdout.write(`[context-pack:functor] report(md): ${toRelativePath(path.resolve(options.reportMarkdownPath))}\n`);

  if (report.status === 'fail') {
    process.stderr.write(`[context-pack:functor] validation failed (${violations.length} violation(s))\n`);
    return 2;
  }
  process.stdout.write(`[context-pack:functor] validation passed (${contextPackFiles.length} context-pack file(s))\n`);
  return 0;
}

try {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    process.exit(0);
  }
  process.exit(validateFunctor(options));
} catch (error) {
  process.stderr.write(`[context-pack:functor] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(1);
}
