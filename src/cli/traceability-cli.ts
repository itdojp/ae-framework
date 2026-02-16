import { Command } from 'commander';
import { globSync } from 'glob';
import fs from 'node:fs';
import path from 'node:path';
import { safeExit } from '../utils/safe-exit.js';

const MAP_SCHEMA_VERSION = 'issue-traceability-map/v1';
const MATRIX_SCHEMA_VERSION = 'issue-traceability-matrix/v1';
const DEFAULT_PATTERN = '(?:LG|REQ)-[A-Z0-9_-]+';

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
  };
  rows: IssueTraceabilityRow[];
};

type ScannedFile = {
  path: string;
  content: string;
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
  return value
    .split(',')
    .map((item) => item.trim())
    .filter(Boolean);
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

export function buildTraceabilityMatrix(
  requirementIds: string[],
  testFiles: ScannedFile[],
  codeFiles: ScannedFile[],
  cwd: string,
): IssueTraceabilityMatrix {
  const rows: IssueTraceabilityRow[] = requirementIds.map((requirementId) => {
    const tests = testFiles
      .filter((file) => file.content.includes(requirementId))
      .map((file) => path.relative(cwd, file.path));
    const code = codeFiles
      .filter((file) => file.content.includes(requirementId))
      .map((file) => path.relative(cwd, file.path));

    return {
      requirementId,
      tests,
      code,
      linked: tests.length > 0 && code.length > 0,
    };
  });

  const linkedRequirements = rows.filter((row) => row.linked).length;
  const totalRequirements = rows.length;
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
    '',
    '| Requirement ID | Tests | Code | Linked |',
    '| --- | --- | --- | --- |',
  ];
  for (const row of matrix.rows) {
    lines.push(
      `| ${row.requirementId} | ${row.tests.join('<br>') || '-'} | ${row.code.join('<br>') || '-'} | ${row.linked ? 'yes' : 'no'} |`,
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
        const testFiles = scanFiles(testPatterns, cwd);
        const codeFiles = scanFiles(codePatterns, cwd);
        const matrix = buildTraceabilityMatrix(requirementIds, testFiles, codeFiles, cwd);
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
        console.log(`[traceability] wrote ${path.relative(cwd, outputPath)}`);
      } catch (error) {
        console.error(`[traceability] matrix failed: ${error instanceof Error ? error.message : String(error)}`);
        safeExit(2);
      }
    });

  return command;
}
