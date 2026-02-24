import { Command } from 'commander';
import { globSync } from 'glob';
import fs from 'node:fs';
import path from 'node:path';
import yaml from 'yaml';
import { safeExit } from '../utils/safe-exit.js';

const MAP_SCHEMA_VERSION = 'issue-traceability-map/v1';
const MATRIX_SCHEMA_VERSION = 'issue-traceability-matrix/v1';
const DEFAULT_PATTERN = '(?:LG|REQ)-[A-Z0-9_-]+';
const DEFAULT_CONTEXT_PACK_GLOB = 'spec/context-pack/**/*.{yml,yaml,json}';

type IssueReference = {
  repository: string;
  issueNumber: number;
  issueUrl: string;
};

type IssueTraceabilityMap = {
  schemaVersion: string;
  generatedAt: string;
  source: {
    type: 'github-issue';
    repository: string;
    issueNumber: number;
    issueUrl: string;
    title: string | null;
  };
  pattern: string;
  requirementIds: string[];
  mappings: Array<{
    id: string;
    tests: string[];
    code: string[];
    notes: string | null;
  }>;
};

type IssueTraceabilityRow = {
  requirementId: string;
  tests: string[];
  code: string[];
  diagramId: string[];
  morphismId: string[];
  acceptanceTestId: string[];
  linked: boolean;
};

type IssueTraceabilityMatrix = {
  schemaVersion: string;
  generatedAt: string;
  sourceMap: string;
  summary: {
    totalRequirements: number;
    linkedRequirements: number;
    unlinkedRequirements: number;
    coverage: number;
    contextPackDiagramIds: number;
    contextPackMorphismIds: number;
    contextPackAcceptanceTestIds: number;
    missingDiagramLinks: number;
    missingMorphismLinks: number;
    missingAcceptanceTestLinks: number;
    rowsMissingContextPackLinks: number;
  };
  rows: IssueTraceabilityRow[];
};

type ScannedFile = {
  path: string;
  content: string;
};

type ContextPackIds = {
  diagramIds: string[];
  morphismIds: string[];
  acceptanceTestIds: string[];
};

function readJsonFile<T>(filePath: string): T {
  const raw = fs.readFileSync(filePath, 'utf8');
  return JSON.parse(raw) as T;
}

function ensureParentDir(filePath: string) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function compilePattern(patternSource: string): RegExp {
  try {
    return new RegExp(patternSource, 'g');
  } catch (error) {
    throw new Error(`Invalid pattern: ${patternSource} (${error instanceof Error ? error.message : String(error)})`);
  }
}

export function extractRequirementIds(text: string, patternSource: string): string[] {
  const regex = compilePattern(patternSource);
  const ids: string[] = [];
  const seen = new Set<string>();
  for (const match of text.matchAll(regex)) {
    const captured = match[0]?.trim();
    if (!captured || seen.has(captured)) {
      continue;
    }
    seen.add(captured);
    ids.push(captured);
  }
  return ids;
}

export function parseIssueReference(issueValue: string, repoValue?: string, envRepo?: string): IssueReference {
  const issue = issueValue.trim();
  if (!issue) {
    throw new Error('--issue is required');
  }

  const urlMatch = issue.match(/^https:\/\/github\.com\/([^/]+)\/([^/]+)\/issues\/(\d+)$/i);
  if (urlMatch) {
    const owner = urlMatch[1];
    const repo = urlMatch[2];
    const issueNumber = Number.parseInt(urlMatch[3] ?? '0', 10);
    return {
      repository: `${owner}/${repo}`,
      issueNumber,
      issueUrl: `https://github.com/${owner}/${repo}/issues/${issueNumber}`,
    };
  }

  const issueNumber = Number.parseInt(issue, 10);
  if (!Number.isFinite(issueNumber) || issueNumber <= 0) {
    throw new Error(`Unsupported --issue value: ${issueValue}`);
  }

  const repository = (repoValue || envRepo || '').trim();
  if (!repository) {
    throw new Error('Repository is required when --issue is not a full URL (use --repo <owner/repo> or GITHUB_REPOSITORY).');
  }

  return {
    repository,
    issueNumber,
    issueUrl: `https://github.com/${repository}/issues/${issueNumber}`,
  };
}

async function fetchIssueBody(issueRef: IssueReference): Promise<{ title: string | null; body: string }> {
  const apiUrl = `https://api.github.com/repos/${issueRef.repository}/issues/${issueRef.issueNumber}`;
  const token = process.env['GH_TOKEN'] || process.env['GITHUB_TOKEN'] || '';
  const headers: Record<string, string> = {
    Accept: 'application/vnd.github+json',
    'User-Agent': 'ae-framework-traceability-cli',
  };
  if (token) {
    headers['Authorization'] = `Bearer ${token}`;
  }

  const response = await fetch(apiUrl, { headers });
  if (!response.ok) {
    throw new Error(`GitHub API request failed (${response.status} ${response.statusText})`);
  }

  const payload = await response.json() as { title?: unknown; body?: unknown };
  return {
    title: typeof payload.title === 'string' ? payload.title : null,
    body: typeof payload.body === 'string' ? payload.body : '',
  };
}

function resolveGlobPatterns(value: string): string[] {
  const patterns: string[] = [];
  let token = '';
  let braceDepth = 0;
  for (const character of value) {
    if (character === '{') {
      braceDepth += 1;
      token += character;
      continue;
    }
    if (character === '}') {
      braceDepth = Math.max(0, braceDepth - 1);
      token += character;
      continue;
    }
    if (character === ',' && braceDepth === 0) {
      const trimmed = token.trim();
      if (trimmed.length > 0) {
        patterns.push(trimmed);
      }
      token = '';
      continue;
    }
    token += character;
  }
  const tail = token.trim();
  if (tail.length > 0) {
    patterns.push(tail);
  }
  return patterns;
}

function scanFiles(patterns: string[], cwd: string): ScannedFile[] {
  const seen = new Set<string>();
  const files: ScannedFile[] = [];
  for (const pattern of patterns) {
    const matches = globSync(pattern, {
      cwd,
      absolute: true,
      nodir: true,
      ignore: ['**/node_modules/**', '**/.git/**'],
    });
    for (const match of matches) {
      const normalized = path.normalize(match);
      if (seen.has(normalized)) {
        continue;
      }
      seen.add(normalized);
      try {
        const content = fs.readFileSync(normalized, 'utf8');
        files.push({ path: normalized, content });
      } catch {
        // Ignore unreadable files and keep scanning.
      }
    }
  }
  return files;
}

function escapeRegexLiteral(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function hasRequirementIdToken(text: string, requirementId: string): boolean {
  const escapedId = escapeRegexLiteral(requirementId);
  const matcher = new RegExp(`(^|[^A-Za-z0-9_-])${escapedId}(?=$|[^A-Za-z0-9_-])`);
  return matcher.test(text);
}

function toUniqueIds(input: unknown): string[] {
  if (!Array.isArray(input)) {
    return [];
  }
  const ids = input
    .map((item) => (item && typeof item === 'object' ? (item as { id?: unknown }).id : undefined))
    .filter((id): id is string => typeof id === 'string' && id.trim().length > 0)
    .map((id) => id.trim());
  return Array.from(new Set(ids));
}

function parseStructuredFile(file: ScannedFile): unknown {
  const lowerPath = file.path.toLowerCase();
  if (lowerPath.endsWith('.yaml') || lowerPath.endsWith('.yml')) {
    return yaml.parse(file.content);
  }
  return JSON.parse(file.content);
}

function readContextPackIds(contextPackFiles: ScannedFile[]): ContextPackIds {
  const diagramIds = new Set<string>();
  const morphismIds = new Set<string>();
  const acceptanceTestIds = new Set<string>();

  for (const file of contextPackFiles) {
    let payload: unknown;
    try {
      payload = parseStructuredFile(file);
    } catch {
      continue;
    }
    if (!payload || typeof payload !== 'object') {
      continue;
    }

    const diagrams = toUniqueIds((payload as { diagrams?: unknown }).diagrams);
    const morphisms = toUniqueIds((payload as { morphisms?: unknown }).morphisms);
    const acceptanceTests = toUniqueIds((payload as { acceptance_tests?: unknown }).acceptance_tests);

    for (const id of diagrams) {
      diagramIds.add(id);
    }
    for (const id of morphisms) {
      morphismIds.add(id);
    }
    for (const id of acceptanceTests) {
      acceptanceTestIds.add(id);
    }
  }

  return {
    diagramIds: Array.from(diagramIds),
    morphismIds: Array.from(morphismIds),
    acceptanceTestIds: Array.from(acceptanceTestIds),
  };
}

function collectMatchedIds(evidenceFiles: ScannedFile[], contextIds: string[]): string[] {
  const matches: string[] = [];
  for (const contextId of contextIds) {
    const found = evidenceFiles.some((file) => hasRequirementIdToken(file.content, contextId));
    if (found) {
      matches.push(contextId);
    }
  }
  return matches;
}

export function buildTraceabilityMatrix(
  requirementIds: string[],
  testFiles: ScannedFile[],
  codeFiles: ScannedFile[],
  cwd: string,
  contextPackIds: ContextPackIds = {
    diagramIds: [],
    morphismIds: [],
    acceptanceTestIds: [],
  },
): IssueTraceabilityMatrix {
  const rows: IssueTraceabilityRow[] = requirementIds.map((requirementId) => {
    const linkedTestFiles = testFiles.filter((file) => hasRequirementIdToken(file.content, requirementId));
    const linkedCodeFiles = codeFiles.filter((file) => hasRequirementIdToken(file.content, requirementId));
    const tests = linkedTestFiles.map((file) => path.relative(cwd, file.path));
    const code = linkedCodeFiles.map((file) => path.relative(cwd, file.path));
    const evidenceFiles = [...linkedTestFiles, ...linkedCodeFiles];

    return {
      requirementId,
      tests,
      code,
      diagramId: collectMatchedIds(evidenceFiles, contextPackIds.diagramIds),
      morphismId: collectMatchedIds(evidenceFiles, contextPackIds.morphismIds),
      acceptanceTestId: collectMatchedIds(evidenceFiles, contextPackIds.acceptanceTestIds),
      linked: tests.length > 0 && code.length > 0,
    };
  });

  const linkedRequirements = rows.filter((row) => row.linked).length;
  const totalRequirements = rows.length;
  const contextPackTracked = contextPackIds.diagramIds.length > 0
    || contextPackIds.morphismIds.length > 0
    || contextPackIds.acceptanceTestIds.length > 0;
  const missingDiagramLinks = contextPackTracked
    ? rows.filter((row) => row.diagramId.length === 0).length
    : 0;
  const missingMorphismLinks = contextPackTracked
    ? rows.filter((row) => row.morphismId.length === 0).length
    : 0;
  const missingAcceptanceTestLinks = contextPackTracked
    ? rows.filter((row) => row.acceptanceTestId.length === 0).length
    : 0;
  const rowsMissingContextPackLinks = contextPackTracked
    ? rows.filter(
      (row) => row.diagramId.length === 0 || row.morphismId.length === 0 || row.acceptanceTestId.length === 0,
    ).length
    : 0;
  const coverage = totalRequirements > 0
    ? Math.round((linkedRequirements / totalRequirements) * 100)
    : 0;

  return {
    schemaVersion: MATRIX_SCHEMA_VERSION,
    generatedAt: new Date().toISOString(),
    sourceMap: '',
    summary: {
      totalRequirements,
      linkedRequirements,
      unlinkedRequirements: totalRequirements - linkedRequirements,
      coverage,
      contextPackDiagramIds: contextPackIds.diagramIds.length,
      contextPackMorphismIds: contextPackIds.morphismIds.length,
      contextPackAcceptanceTestIds: contextPackIds.acceptanceTestIds.length,
      missingDiagramLinks,
      missingMorphismLinks,
      missingAcceptanceTestLinks,
      rowsMissingContextPackLinks,
    },
    rows,
  };
}

function renderMatrixMarkdown(matrix: IssueTraceabilityMatrix): string {
  const lines = [
    '# Issue Traceability Matrix',
    '',
    `- Generated at: ${matrix.generatedAt}`,
    `- Coverage: ${matrix.summary.coverage}% (${matrix.summary.linkedRequirements}/${matrix.summary.totalRequirements})`,
    `- Context Pack IDs tracked: diagram=${matrix.summary.contextPackDiagramIds}, morphism=${matrix.summary.contextPackMorphismIds}, acceptance_test=${matrix.summary.contextPackAcceptanceTestIds}`,
    `- Missing Context Pack links: rows=${matrix.summary.rowsMissingContextPackLinks}, diagram=${matrix.summary.missingDiagramLinks}, morphism=${matrix.summary.missingMorphismLinks}, acceptance_test=${matrix.summary.missingAcceptanceTestLinks}`,
    '',
    '| Requirement ID | Tests | Code | Diagram ID | Morphism ID | Acceptance Test ID | Linked |',
    '| --- | --- | --- | --- | --- | --- | --- |',
  ];
  for (const row of matrix.rows) {
    lines.push(
      `| ${row.requirementId} | ${row.tests.join('<br>') || '-'} | ${row.code.join('<br>') || '-'} | ${row.diagramId.join('<br>') || '-'} | ${row.morphismId.join('<br>') || '-'} | ${row.acceptanceTestId.join('<br>') || '-'} | ${row.linked ? 'yes' : 'no'} |`,
    );
  }
  return `${lines.join('\n')}\n`;
}

function loadRequirementIdsFromMap(mapPath: string): string[] {
  const mapPayload = readJsonFile<IssueTraceabilityMap & { requirementIds?: unknown; mappings?: unknown }>(mapPath);
  const fromRequirementIds = Array.isArray(mapPayload.requirementIds)
    ? mapPayload.requirementIds.filter((id): id is string => typeof id === 'string' && id.trim().length > 0)
    : [];
  if (fromRequirementIds.length > 0) {
    return Array.from(new Set(fromRequirementIds));
  }
  const fromMappings = Array.isArray(mapPayload.mappings)
    ? mapPayload.mappings
        .map((item) => (item && typeof item === 'object' ? (item as { id?: unknown }).id : undefined))
        .filter((id): id is string => typeof id === 'string' && id.trim().length > 0)
    : [];
  return Array.from(new Set(fromMappings));
}

export function createTraceabilityCommand(): Command {
  const command = new Command('traceability');
  command.description('Issue要件ID（LG-*/REQ-*）起点のトレーサビリティ補助コマンド');

  command
    .command('extract-ids')
    .description('GitHub Issue 本文から要件IDを抽出し map JSON を生成')
    .requiredOption('--issue <issue>', 'Issue URL または issue number')
    .option('--repo <owner/repo>', 'Issue number 指定時の対象リポジトリ')
    .option('--pattern <regex>', '要件ID抽出パターン', DEFAULT_PATTERN)
    .requiredOption('--output <file>', '出力先 map JSON')
    .action(async (options) => {
      try {
        const issueRef = parseIssueReference(
          String(options.issue),
          typeof options.repo === 'string' ? options.repo : undefined,
          process.env['GITHUB_REPOSITORY'],
        );
        const issueData = await fetchIssueBody(issueRef);
        const requirementIds = extractRequirementIds(issueData.body, String(options.pattern));
        const mapPayload: IssueTraceabilityMap = {
          schemaVersion: MAP_SCHEMA_VERSION,
          generatedAt: new Date().toISOString(),
          source: {
            type: 'github-issue',
            repository: issueRef.repository,
            issueNumber: issueRef.issueNumber,
            issueUrl: issueRef.issueUrl,
            title: issueData.title,
          },
          pattern: String(options.pattern),
          requirementIds,
          mappings: requirementIds.map((id) => ({
            id,
            tests: [],
            code: [],
            notes: null,
          })),
        };

        const outputPath = path.resolve(process.cwd(), String(options.output));
        ensureParentDir(outputPath);
        fs.writeFileSync(outputPath, JSON.stringify(mapPayload, null, 2), 'utf8');
        console.log(`[traceability] extracted ${requirementIds.length} IDs from ${issueRef.issueUrl}`);
        console.log(`[traceability] wrote ${path.relative(process.cwd(), outputPath)}`);
      } catch (error) {
        console.error(`[traceability] extract-ids failed: ${error instanceof Error ? error.message : String(error)}`);
        safeExit(2);
      }
    });

  command
    .command('matrix')
    .description('traceability map から requirement × tests/code マトリクスを生成')
    .requiredOption('--map <file>', 'traceability map JSON')
    .option('--tests <glob>', 'テストファイルの glob（comma-separated 可）', 'tests/**/*')
    .option('--code <glob>', '実装ファイルの glob（comma-separated 可）', 'src/**/*')
    .option('--context-pack <glob>', 'Context Pack ファイルの glob（comma-separated 可）', DEFAULT_CONTEXT_PACK_GLOB)
    .option('--format <format>', '出力形式 (json|md)', 'md')
    .requiredOption('--output <file>', '出力先')
    .action((options) => {
      try {
        const cwd = process.cwd();
        const mapPath = path.resolve(cwd, String(options.map));
        const requirementIds = loadRequirementIdsFromMap(mapPath);
        if (requirementIds.length === 0) {
          throw new Error(`No requirement IDs found in map: ${path.relative(cwd, mapPath)}`);
        }

        const testPatterns = resolveGlobPatterns(String(options.tests));
        const codePatterns = resolveGlobPatterns(String(options.code));
        const contextPackPatterns = resolveGlobPatterns(String(options.contextPack ?? ''));
        const testFiles = scanFiles(testPatterns, cwd);
        const codeFiles = scanFiles(codePatterns, cwd);
        const contextPackFiles = contextPackPatterns.length > 0
          ? scanFiles(contextPackPatterns, cwd)
          : [];
        const contextPackIds = readContextPackIds(contextPackFiles);
        const matrix = buildTraceabilityMatrix(requirementIds, testFiles, codeFiles, cwd, contextPackIds);
        matrix.sourceMap = path.relative(cwd, mapPath);

        const format = String(options.format).toLowerCase();
        const outputPath = path.resolve(cwd, String(options.output));
        ensureParentDir(outputPath);
        if (format === 'json') {
          fs.writeFileSync(outputPath, JSON.stringify(matrix, null, 2), 'utf8');
        } else if (format === 'md') {
          fs.writeFileSync(outputPath, renderMatrixMarkdown(matrix), 'utf8');
        } else {
          throw new Error(`Unsupported format: ${options.format}. Use json or md.`);
        }

        console.log(
          `[traceability] matrix coverage ${matrix.summary.coverage}% (${matrix.summary.linkedRequirements}/${matrix.summary.totalRequirements})`,
        );
        if (contextPackPatterns.length > 0) {
          console.log(
            `[traceability] context-pack missing rows=${matrix.summary.rowsMissingContextPackLinks} (diagram=${matrix.summary.missingDiagramLinks}, morphism=${matrix.summary.missingMorphismLinks}, acceptance_test=${matrix.summary.missingAcceptanceTestLinks})`,
          );
        }
        console.log(`[traceability] wrote ${path.relative(cwd, outputPath)}`);
      } catch (error) {
        console.error(`[traceability] matrix failed: ${error instanceof Error ? error.message : String(error)}`);
        safeExit(2);
      }
    });

  return command;
}
