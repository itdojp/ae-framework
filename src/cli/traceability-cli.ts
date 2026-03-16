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
  diagramId?: string[];
  morphismId?: string[];
  acceptanceTestId?: string[];
  discoveryGoalIds?: string[];
  discoveryRequirementIds?: string[];
  discoveryBusinessUseCaseIds?: string[];
  discoveryDecisionIds?: string[];
  linked: boolean;
};

type IssueTraceabilityDiscoveryRefs = {
  goalIds: string[];
  requirementIds: string[];
  businessUseCaseIds: string[];
  decisionIds: string[];
};

type IssueTraceabilityDiscoverySummary = {
  tracked: boolean;
  goalIds: string[];
  requirementIds: string[];
  businessUseCaseIds: string[];
  decisionIds: string[];
  mappedGoalIds: string[];
  mappedRequirementIds: string[];
  mappedBusinessUseCaseIds: string[];
  mappedDecisionIds: string[];
  approvedRequirementIds: string[];
  approvedBusinessUseCaseIds: string[];
  unmappedApprovedRequirements: number;
  unmappedApprovedBusinessUseCases: number;
  unresolvedGoalRefs: number;
  unresolvedRequirementRefs: number;
  unresolvedBusinessUseCaseRefs: number;
  unresolvedDecisionRefs: number;
  morphismsMissingUpstreamRefs: number;
  acceptanceTestsMissingUpstreamRefs: number;
  diagramsMissingUpstreamRefs: number;
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
    discoveryGoalIds?: number;
    discoveryRequirementIds?: number;
    discoveryBusinessUseCaseIds?: number;
    discoveryDecisionIds?: number;
    mappedDiscoveryGoalIds?: number;
    mappedDiscoveryRequirementIds?: number;
    mappedDiscoveryBusinessUseCaseIds?: number;
    mappedDiscoveryDecisionIds?: number;
    unmappedApprovedDiscoveryRequirements?: number;
    unmappedApprovedDiscoveryBusinessUseCases?: number;
    unresolvedDiscoveryGoalRefs?: number;
    unresolvedDiscoveryRequirementRefs?: number;
    unresolvedDiscoveryBusinessUseCaseRefs?: number;
    unresolvedDiscoveryDecisionRefs?: number;
    morphismsMissingUpstreamRefs?: number;
    acceptanceTestsMissingUpstreamRefs?: number;
    diagramsMissingUpstreamRefs?: number;
    rowsMissingDiscoveryLinks?: number;
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
  diagramDiscoveryRefs?: Record<string, IssueTraceabilityDiscoveryRefs>;
  morphismDiscoveryRefs?: Record<string, IssueTraceabilityDiscoveryRefs>;
  acceptanceTestDiscoveryRefs?: Record<string, IssueTraceabilityDiscoveryRefs>;
  discoverySummary?: IssueTraceabilityDiscoverySummary | null;
};

type DiscoveryPackIndex = {
  goalIds: Set<string>;
  requirementIds: Set<string>;
  businessUseCaseIds: Set<string>;
  decisionIds: Set<string>;
  approvedRequirementIds: Set<string>;
  approvedBusinessUseCaseIds: Set<string>;
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

function mergeUniqueStrings(current: string[], incoming: string[]): string[] {
  const merged = [...current];
  const seen = new Set(current);
  for (const value of incoming) {
    if (seen.has(value)) {
      continue;
    }
    seen.add(value);
    merged.push(value);
  }
  return merged;
}

function toUniqueStringList(input: unknown): string[] {
  if (!Array.isArray(input)) {
    return [];
  }
  const values = input
    .filter((item): item is string => typeof item === 'string' && item.trim().length > 0)
    .map((item) => item.trim());
  return Array.from(new Set(values));
}

function emptyDiscoveryRefs(): IssueTraceabilityDiscoveryRefs {
  return {
    goalIds: [],
    requirementIds: [],
    businessUseCaseIds: [],
    decisionIds: [],
  };
}

function toDiscoveryRefs(input: unknown): IssueTraceabilityDiscoveryRefs {
  if (!input || typeof input !== 'object') {
    return emptyDiscoveryRefs();
  }
  const upstream = input as Record<string, unknown>;
  return {
    goalIds: toUniqueStringList(upstream['goal_ids']),
    requirementIds: toUniqueStringList(upstream['requirement_ids']),
    businessUseCaseIds: toUniqueStringList(upstream['business_use_case_ids']),
    decisionIds: toUniqueStringList(upstream['decision_ids']),
  };
}

function mergeDiscoveryRefs(
  current: IssueTraceabilityDiscoveryRefs,
  incoming: IssueTraceabilityDiscoveryRefs,
): IssueTraceabilityDiscoveryRefs {
  return {
    goalIds: mergeUniqueStrings(current.goalIds, incoming.goalIds),
    requirementIds: mergeUniqueStrings(current.requirementIds, incoming.requirementIds),
    businessUseCaseIds: mergeUniqueStrings(current.businessUseCaseIds, incoming.businessUseCaseIds),
    decisionIds: mergeUniqueStrings(current.decisionIds, incoming.decisionIds),
  };
}

function hasDiscoveryRefs(refs: IssueTraceabilityDiscoveryRefs): boolean {
  return refs.goalIds.length > 0
    || refs.requirementIds.length > 0
    || refs.businessUseCaseIds.length > 0
    || refs.decisionIds.length > 0;
}

function parseStructuredFile(file: ScannedFile): unknown {
  const lowerPath = file.path.toLowerCase();
  if (lowerPath.endsWith('.yaml') || lowerPath.endsWith('.yml')) {
    return yaml.parse(file.content);
  }
  return JSON.parse(file.content);
}

function readDiscoveryPackIndex(discoveryPackFile: ScannedFile): DiscoveryPackIndex {
  const payload = parseStructuredFile(discoveryPackFile) as Record<string, unknown>;
  const index: DiscoveryPackIndex = {
    goalIds: new Set<string>(),
    requirementIds: new Set<string>(),
    businessUseCaseIds: new Set<string>(),
    decisionIds: new Set<string>(),
    approvedRequirementIds: new Set<string>(),
    approvedBusinessUseCaseIds: new Set<string>(),
  };

  const registerSection = (
    section: string,
    target: Set<string>,
    approvedTarget?: Set<string>,
  ) => {
    const entries = Array.isArray(payload?.[section]) ? payload[section] : [];
    for (const entry of entries) {
      if (!entry || typeof entry !== 'object') {
        continue;
      }
      const id = typeof (entry as { id?: unknown }).id === 'string'
        ? (entry as { id: string }).id.trim()
        : '';
      if (!id) {
        continue;
      }
      target.add(id);
      if (
        approvedTarget
        && typeof (entry as { status?: unknown }).status === 'string'
        && (entry as { status: string }).status === 'approved'
      ) {
        approvedTarget.add(id);
      }
    }
  };

  registerSection('goals', index.goalIds);
  registerSection('requirements', index.requirementIds, index.approvedRequirementIds);
  registerSection('business_use_cases', index.businessUseCaseIds, index.approvedBusinessUseCaseIds);
  registerSection('decisions', index.decisionIds);
  return index;
}

function readContextPackIds(
  contextPackFiles: ScannedFile[],
  discoveryPackIndex?: DiscoveryPackIndex,
): ContextPackIds {
  const diagramIds = new Set<string>();
  const morphismIds = new Set<string>();
  const acceptanceTestIds = new Set<string>();
  const diagramDiscoveryRefs: Record<string, IssueTraceabilityDiscoveryRefs> = {};
  const morphismDiscoveryRefs: Record<string, IssueTraceabilityDiscoveryRefs> = {};
  const acceptanceTestDiscoveryRefs: Record<string, IssueTraceabilityDiscoveryRefs> = {};
  const mappedGoalIds = new Set<string>();
  const mappedRequirementIds = new Set<string>();
  const mappedBusinessUseCaseIds = new Set<string>();
  const mappedDecisionIds = new Set<string>();
  let unresolvedGoalRefs = 0;
  let unresolvedRequirementRefs = 0;
  let unresolvedBusinessUseCaseRefs = 0;
  let unresolvedDecisionRefs = 0;
  let morphismsMissingUpstreamRefs = 0;
  let acceptanceTestsMissingUpstreamRefs = 0;
  let diagramsMissingUpstreamRefs = 0;

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

    const registerRefs = (
      entries: unknown,
      targetMap: Record<string, IssueTraceabilityDiscoveryRefs>,
      missingCounter: { value: number },
      required: boolean,
    ) => {
      if (!Array.isArray(entries)) {
        return;
      }
      for (const entry of entries) {
        if (!entry || typeof entry !== 'object') {
          continue;
        }
        const id = typeof (entry as { id?: unknown }).id === 'string'
          ? (entry as { id: string }).id.trim()
          : '';
        if (!id) {
          continue;
        }
        const refs = toDiscoveryRefs((entry as { upstream_refs?: unknown }).upstream_refs);
        if (!hasDiscoveryRefs(refs)) {
          missingCounter.value += 1;
          continue;
        }
        targetMap[id] = mergeDiscoveryRefs(targetMap[id] ?? emptyDiscoveryRefs(), refs);
        if (!discoveryPackIndex) {
          continue;
        }
        for (const ref of refs.goalIds) {
          if (discoveryPackIndex.goalIds.has(ref)) {
            mappedGoalIds.add(ref);
          } else {
            unresolvedGoalRefs += 1;
          }
        }
        for (const ref of refs.requirementIds) {
          if (discoveryPackIndex.requirementIds.has(ref)) {
            mappedRequirementIds.add(ref);
          } else {
            unresolvedRequirementRefs += 1;
          }
        }
        for (const ref of refs.businessUseCaseIds) {
          if (discoveryPackIndex.businessUseCaseIds.has(ref)) {
            mappedBusinessUseCaseIds.add(ref);
          } else {
            unresolvedBusinessUseCaseRefs += 1;
          }
        }
        for (const ref of refs.decisionIds) {
          if (discoveryPackIndex.decisionIds.has(ref)) {
            mappedDecisionIds.add(ref);
          } else {
            unresolvedDecisionRefs += 1;
          }
        }
      }
    };

    const morphismMissing = { value: 0 };
    const acceptanceMissing = { value: 0 };
    const diagramMissing = { value: 0 };
    registerRefs(
      (payload as { morphisms?: unknown }).morphisms,
      morphismDiscoveryRefs,
      morphismMissing,
      true,
    );
    registerRefs(
      (payload as { acceptance_tests?: unknown }).acceptance_tests,
      acceptanceTestDiscoveryRefs,
      acceptanceMissing,
      true,
    );
    registerRefs(
      (payload as { diagrams?: unknown }).diagrams,
      diagramDiscoveryRefs,
      diagramMissing,
      false,
    );
    morphismsMissingUpstreamRefs += morphismMissing.value;
    acceptanceTestsMissingUpstreamRefs += acceptanceMissing.value;
    diagramsMissingUpstreamRefs += diagramMissing.value;
  }

  return {
    diagramIds: Array.from(diagramIds),
    morphismIds: Array.from(morphismIds),
    acceptanceTestIds: Array.from(acceptanceTestIds),
    diagramDiscoveryRefs,
    morphismDiscoveryRefs,
    acceptanceTestDiscoveryRefs,
    discoverySummary: discoveryPackIndex
      ? {
          tracked: true,
          goalIds: Array.from(discoveryPackIndex.goalIds),
          requirementIds: Array.from(discoveryPackIndex.requirementIds),
          businessUseCaseIds: Array.from(discoveryPackIndex.businessUseCaseIds),
          decisionIds: Array.from(discoveryPackIndex.decisionIds),
          mappedGoalIds: Array.from(mappedGoalIds),
          mappedRequirementIds: Array.from(mappedRequirementIds),
          mappedBusinessUseCaseIds: Array.from(mappedBusinessUseCaseIds),
          mappedDecisionIds: Array.from(mappedDecisionIds),
          approvedRequirementIds: Array.from(discoveryPackIndex.approvedRequirementIds),
          approvedBusinessUseCaseIds: Array.from(discoveryPackIndex.approvedBusinessUseCaseIds),
          unmappedApprovedRequirements: Array.from(discoveryPackIndex.approvedRequirementIds)
            .filter((id) => !mappedRequirementIds.has(id))
            .length,
          unmappedApprovedBusinessUseCases: Array.from(discoveryPackIndex.approvedBusinessUseCaseIds)
            .filter((id) => !mappedBusinessUseCaseIds.has(id))
            .length,
          unresolvedGoalRefs,
          unresolvedRequirementRefs,
          unresolvedBusinessUseCaseRefs,
          unresolvedDecisionRefs,
          morphismsMissingUpstreamRefs,
          acceptanceTestsMissingUpstreamRefs,
          diagramsMissingUpstreamRefs,
        }
      : null,
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

function collectDiscoveryRefsFromMatches(
  ids: string[],
  upstreamRefsById: Record<string, IssueTraceabilityDiscoveryRefs>,
): IssueTraceabilityDiscoveryRefs {
  return ids.reduce<IssueTraceabilityDiscoveryRefs>(
    (accumulator, id) => mergeDiscoveryRefs(accumulator, upstreamRefsById[id] ?? emptyDiscoveryRefs()),
    emptyDiscoveryRefs(),
  );
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
    diagramDiscoveryRefs: {},
    morphismDiscoveryRefs: {},
    acceptanceTestDiscoveryRefs: {},
    discoverySummary: null,
  },
): IssueTraceabilityMatrix {
  const contextPackTracked = contextPackIds.diagramIds.length > 0
    || contextPackIds.morphismIds.length > 0
    || contextPackIds.acceptanceTestIds.length > 0;
  const discoveryTracked = Boolean(contextPackIds.discoverySummary?.tracked);

  const rows: IssueTraceabilityRow[] = requirementIds.map((requirementId) => {
    const linkedTestFiles = testFiles.filter((file) => hasRequirementIdToken(file.content, requirementId));
    const linkedCodeFiles = codeFiles.filter((file) => hasRequirementIdToken(file.content, requirementId));
    const tests = linkedTestFiles.map((file) => path.relative(cwd, file.path));
    const code = linkedCodeFiles.map((file) => path.relative(cwd, file.path));
    const evidenceFiles = [...linkedTestFiles, ...linkedCodeFiles];

    const row: IssueTraceabilityRow = {
      requirementId,
      tests,
      code,
      linked: tests.length > 0 && code.length > 0,
    };
    if (contextPackTracked) {
      row.diagramId = collectMatchedIds(evidenceFiles, contextPackIds.diagramIds);
      row.morphismId = collectMatchedIds(evidenceFiles, contextPackIds.morphismIds);
      row.acceptanceTestId = collectMatchedIds(evidenceFiles, contextPackIds.acceptanceTestIds);
    }
    if (discoveryTracked) {
      const diagramRefs = collectDiscoveryRefsFromMatches(
        row.diagramId ?? [],
        contextPackIds.diagramDiscoveryRefs ?? {},
      );
      const morphismRefs = collectDiscoveryRefsFromMatches(
        row.morphismId ?? [],
        contextPackIds.morphismDiscoveryRefs ?? {},
      );
      const acceptanceRefs = collectDiscoveryRefsFromMatches(
        row.acceptanceTestId ?? [],
        contextPackIds.acceptanceTestDiscoveryRefs ?? {},
      );
      const discoveryRefs = mergeDiscoveryRefs(
        mergeDiscoveryRefs(diagramRefs, morphismRefs),
        acceptanceRefs,
      );
      row.discoveryGoalIds = discoveryRefs.goalIds;
      row.discoveryRequirementIds = discoveryRefs.requirementIds;
      row.discoveryBusinessUseCaseIds = discoveryRefs.businessUseCaseIds;
      row.discoveryDecisionIds = discoveryRefs.decisionIds;
    }
    return row;
  });

  const linkedRequirements = rows.filter((row) => row.linked).length;
  const totalRequirements = rows.length;
  const missingDiagramLinks = contextPackTracked
    ? rows.filter((row) => (row.diagramId?.length ?? 0) === 0).length
    : 0;
  const missingMorphismLinks = contextPackTracked
    ? rows.filter((row) => (row.morphismId?.length ?? 0) === 0).length
    : 0;
  const missingAcceptanceTestLinks = contextPackTracked
    ? rows.filter((row) => (row.acceptanceTestId?.length ?? 0) === 0).length
    : 0;
  const rowsMissingContextPackLinks = contextPackTracked
    ? rows.filter(
      (row) => (row.diagramId?.length ?? 0) === 0
        || (row.morphismId?.length ?? 0) === 0
        || (row.acceptanceTestId?.length ?? 0) === 0,
    ).length
    : 0;
  const rowsMissingDiscoveryLinks = discoveryTracked
    ? rows.filter(
      (row) => row.linked
        && (row.discoveryGoalIds?.length ?? 0) === 0
        && (row.discoveryRequirementIds?.length ?? 0) === 0
        && (row.discoveryBusinessUseCaseIds?.length ?? 0) === 0
        && (row.discoveryDecisionIds?.length ?? 0) === 0,
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
      discoveryGoalIds: contextPackIds.discoverySummary?.goalIds.length ?? 0,
      discoveryRequirementIds: contextPackIds.discoverySummary?.requirementIds.length ?? 0,
      discoveryBusinessUseCaseIds: contextPackIds.discoverySummary?.businessUseCaseIds.length ?? 0,
      discoveryDecisionIds: contextPackIds.discoverySummary?.decisionIds.length ?? 0,
      mappedDiscoveryGoalIds: contextPackIds.discoverySummary?.mappedGoalIds.length ?? 0,
      mappedDiscoveryRequirementIds: contextPackIds.discoverySummary?.mappedRequirementIds.length ?? 0,
      mappedDiscoveryBusinessUseCaseIds: contextPackIds.discoverySummary?.mappedBusinessUseCaseIds.length ?? 0,
      mappedDiscoveryDecisionIds: contextPackIds.discoverySummary?.mappedDecisionIds.length ?? 0,
      unmappedApprovedDiscoveryRequirements: contextPackIds.discoverySummary?.unmappedApprovedRequirements ?? 0,
      unmappedApprovedDiscoveryBusinessUseCases: contextPackIds.discoverySummary?.unmappedApprovedBusinessUseCases ?? 0,
      unresolvedDiscoveryGoalRefs: contextPackIds.discoverySummary?.unresolvedGoalRefs ?? 0,
      unresolvedDiscoveryRequirementRefs: contextPackIds.discoverySummary?.unresolvedRequirementRefs ?? 0,
      unresolvedDiscoveryBusinessUseCaseRefs: contextPackIds.discoverySummary?.unresolvedBusinessUseCaseRefs ?? 0,
      unresolvedDiscoveryDecisionRefs: contextPackIds.discoverySummary?.unresolvedDecisionRefs ?? 0,
      morphismsMissingUpstreamRefs: contextPackIds.discoverySummary?.morphismsMissingUpstreamRefs ?? 0,
      acceptanceTestsMissingUpstreamRefs: contextPackIds.discoverySummary?.acceptanceTestsMissingUpstreamRefs ?? 0,
      diagramsMissingUpstreamRefs: contextPackIds.discoverySummary?.diagramsMissingUpstreamRefs ?? 0,
      rowsMissingDiscoveryLinks,
    },
    rows,
  };
}

function renderMatrixMarkdown(matrix: IssueTraceabilityMatrix): string {
  const hasContextPackColumns = matrix.summary.contextPackDiagramIds > 0
    || matrix.summary.contextPackMorphismIds > 0
    || matrix.summary.contextPackAcceptanceTestIds > 0;
  const hasDiscoveryColumns = (matrix.summary.discoveryGoalIds ?? 0) > 0
    || (matrix.summary.discoveryRequirementIds ?? 0) > 0
    || (matrix.summary.discoveryBusinessUseCaseIds ?? 0) > 0
    || (matrix.summary.discoveryDecisionIds ?? 0) > 0;
  const lines = [
    '# Issue Traceability Matrix',
    '',
    `- Generated at: ${matrix.generatedAt}`,
    `- Coverage: ${matrix.summary.coverage}% (${matrix.summary.linkedRequirements}/${matrix.summary.totalRequirements})`,
    `- Context Pack IDs tracked: diagram=${matrix.summary.contextPackDiagramIds}, morphism=${matrix.summary.contextPackMorphismIds}, acceptance_test=${matrix.summary.contextPackAcceptanceTestIds}`,
    `- Missing Context Pack links: rows=${matrix.summary.rowsMissingContextPackLinks}, diagram=${matrix.summary.missingDiagramLinks}, morphism=${matrix.summary.missingMorphismLinks}, acceptance_test=${matrix.summary.missingAcceptanceTestLinks}`,
    `- Discovery refs tracked: goal=${matrix.summary.discoveryGoalIds ?? 0}, requirement=${matrix.summary.discoveryRequirementIds ?? 0}, business_use_case=${matrix.summary.discoveryBusinessUseCaseIds ?? 0}, decision=${matrix.summary.discoveryDecisionIds ?? 0}`,
    `- Discovery refs mapped: goal=${matrix.summary.mappedDiscoveryGoalIds ?? 0}, requirement=${matrix.summary.mappedDiscoveryRequirementIds ?? 0}, business_use_case=${matrix.summary.mappedDiscoveryBusinessUseCaseIds ?? 0}, decision=${matrix.summary.mappedDiscoveryDecisionIds ?? 0}`,
    `- Discovery gaps: rows_missing=${matrix.summary.rowsMissingDiscoveryLinks ?? 0}, unmapped_approved_requirements=${matrix.summary.unmappedApprovedDiscoveryRequirements ?? 0}, unmapped_approved_business_use_cases=${matrix.summary.unmappedApprovedDiscoveryBusinessUseCases ?? 0}`,
    `- Discovery unresolved refs: goal=${matrix.summary.unresolvedDiscoveryGoalRefs ?? 0}, requirement=${matrix.summary.unresolvedDiscoveryRequirementRefs ?? 0}, business_use_case=${matrix.summary.unresolvedDiscoveryBusinessUseCaseRefs ?? 0}, decision=${matrix.summary.unresolvedDiscoveryDecisionRefs ?? 0}`,
    `- Context Pack upstream ref gaps: morphism=${matrix.summary.morphismsMissingUpstreamRefs ?? 0}, acceptance_test=${matrix.summary.acceptanceTestsMissingUpstreamRefs ?? 0}, diagram=${matrix.summary.diagramsMissingUpstreamRefs ?? 0}`,
    '',
    hasContextPackColumns && hasDiscoveryColumns
      ? '| Requirement ID | Tests | Code | Diagram ID | Morphism ID | Acceptance Test ID | Discovery Goal IDs | Discovery Requirement IDs | Discovery Business Use Case IDs | Discovery Decision IDs | Linked |'
      : hasContextPackColumns
      ? '| Requirement ID | Tests | Code | Diagram ID | Morphism ID | Acceptance Test ID | Linked |'
      : hasDiscoveryColumns
      ? '| Requirement ID | Tests | Code | Discovery Goal IDs | Discovery Requirement IDs | Discovery Business Use Case IDs | Discovery Decision IDs | Linked |'
      : '| Requirement ID | Tests | Code | Linked |',
    hasContextPackColumns && hasDiscoveryColumns
      ? '| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |'
      : hasContextPackColumns
      ? '| --- | --- | --- | --- | --- | --- | --- |'
      : hasDiscoveryColumns
      ? '| --- | --- | --- | --- | --- | --- | --- | --- |'
      : '| --- | --- | --- | --- |',
  ];
  for (const row of matrix.rows) {
    if (hasContextPackColumns && hasDiscoveryColumns) {
      lines.push(
        `| ${row.requirementId} | ${row.tests.join('<br>') || '-'} | ${row.code.join('<br>') || '-'} | ${row.diagramId?.join('<br>') || '-'} | ${row.morphismId?.join('<br>') || '-'} | ${row.acceptanceTestId?.join('<br>') || '-'} | ${row.discoveryGoalIds?.join('<br>') || '-'} | ${row.discoveryRequirementIds?.join('<br>') || '-'} | ${row.discoveryBusinessUseCaseIds?.join('<br>') || '-'} | ${row.discoveryDecisionIds?.join('<br>') || '-'} | ${row.linked ? 'yes' : 'no'} |`,
      );
    } else if (hasContextPackColumns) {
      lines.push(
        `| ${row.requirementId} | ${row.tests.join('<br>') || '-'} | ${row.code.join('<br>') || '-'} | ${row.diagramId?.join('<br>') || '-'} | ${row.morphismId?.join('<br>') || '-'} | ${row.acceptanceTestId?.join('<br>') || '-'} | ${row.linked ? 'yes' : 'no'} |`,
      );
    } else if (hasDiscoveryColumns) {
      lines.push(
        `| ${row.requirementId} | ${row.tests.join('<br>') || '-'} | ${row.code.join('<br>') || '-'} | ${row.discoveryGoalIds?.join('<br>') || '-'} | ${row.discoveryRequirementIds?.join('<br>') || '-'} | ${row.discoveryBusinessUseCaseIds?.join('<br>') || '-'} | ${row.discoveryDecisionIds?.join('<br>') || '-'} | ${row.linked ? 'yes' : 'no'} |`,
      );
    } else {
      lines.push(
        `| ${row.requirementId} | ${row.tests.join('<br>') || '-'} | ${row.code.join('<br>') || '-'} | ${row.linked ? 'yes' : 'no'} |`,
      );
    }
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
    .option('--discovery-pack <glob>', 'Discovery Pack ファイルの glob（comma-separated 可）')
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
        const discoveryPackPatterns = resolveGlobPatterns(String(options.discoveryPack ?? ''));
        const testFiles = scanFiles(testPatterns, cwd);
        const codeFiles = scanFiles(codePatterns, cwd);
        const contextPackFiles = contextPackPatterns.length > 0
          ? scanFiles(contextPackPatterns, cwd)
          : [];
        let discoveryPackIndex: DiscoveryPackIndex | undefined;
        if (discoveryPackPatterns.length > 0) {
          const discoveryPackFiles = scanFiles(discoveryPackPatterns, cwd);
          if (discoveryPackFiles.length === 0) {
            throw new Error(`No Discovery Pack files matched: ${discoveryPackPatterns.join(', ')}`);
          }
          if (discoveryPackFiles.length !== 1) {
            throw new Error(`Expected exactly one Discovery Pack file, matched ${discoveryPackFiles.length}`);
          }
          discoveryPackIndex = readDiscoveryPackIndex(discoveryPackFiles[0]);
        }
        const contextPackIds = readContextPackIds(contextPackFiles, discoveryPackIndex);
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
        if (discoveryPackPatterns.length > 0) {
          console.log(
            `[traceability] discovery mapped goal=${matrix.summary.mappedDiscoveryGoalIds ?? 0}/${matrix.summary.discoveryGoalIds ?? 0} requirement=${matrix.summary.mappedDiscoveryRequirementIds ?? 0}/${matrix.summary.discoveryRequirementIds ?? 0} business_use_case=${matrix.summary.mappedDiscoveryBusinessUseCaseIds ?? 0}/${matrix.summary.discoveryBusinessUseCaseIds ?? 0} decision=${matrix.summary.mappedDiscoveryDecisionIds ?? 0}/${matrix.summary.discoveryDecisionIds ?? 0}`,
          );
          console.log(
            `[traceability] discovery gaps rows=${matrix.summary.rowsMissingDiscoveryLinks ?? 0} unresolved=${(matrix.summary.unresolvedDiscoveryGoalRefs ?? 0) + (matrix.summary.unresolvedDiscoveryRequirementRefs ?? 0) + (matrix.summary.unresolvedDiscoveryBusinessUseCaseRefs ?? 0) + (matrix.summary.unresolvedDiscoveryDecisionRefs ?? 0)} unmappedApprovedRequirements=${matrix.summary.unmappedApprovedDiscoveryRequirements ?? 0} unmappedApprovedBusinessUseCases=${matrix.summary.unmappedApprovedDiscoveryBusinessUseCases ?? 0}`,
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
