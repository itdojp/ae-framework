import fs from 'node:fs';
import path from 'node:path';

import type { TaskRequest } from './task-types.js';
import type { ValidationInput, ValidationSourceItem } from './validation-task-adapter.types.js';

const DEFAULT_SOURCE_FILE_LIMIT = 200;
const SUPPORTED_EXTENSIONS = new Set([
  '.md',
  '.txt',
  '.yaml',
  '.yml',
  '.json',
  '.feature',
  '.adoc',
  '.rst',
  '.spec',
]);

export interface ValidationSourceResolutionOptions {
  cwd?: string;
  sourceFileLimit?: number;
}

export function extractValidationInput(
  request: TaskRequest,
  options: ValidationSourceResolutionOptions = {},
): ValidationInput {
  const requestedSources = collectRequestedSources(request);
  const resolved = resolveValidationSources(requestedSources, options);
  if (resolved.requestedSources.length > 0 && resolved.resolvedSources.length === 0) {
    throw new Error(`No readable validation sources found. Requested: ${resolved.requestedSources.join(', ')}`);
  }
  return {
    ...resolved,
    strict: Boolean(request.context?.strict),
  };
}

export function collectRequestedSources(request: TaskRequest): string[] {
  const contextSources = request.context?.sources;
  if (Array.isArray(contextSources)) {
    return contextSources
      .filter((value): value is string => typeof value === 'string')
      .map((value) => value.trim())
      .filter(Boolean);
  }
  if (typeof contextSources === 'string') {
    return parseSourceTokens(contextSources);
  }

  const prompt = (request.prompt || '').trim();
  if (!prompt || prompt.toLowerCase() === 'validate available artifacts') {
    return [];
  }
  return parseSourceTokens(prompt);
}

export function parseSourceTokens(value: string): string[] {
  return value
    .split(/[\n,]/)
    .map((item) => item.trim())
    .filter(Boolean);
}

export function resolveValidationSources(
  requestedSources: string[],
  options: ValidationSourceResolutionOptions = {},
): Omit<ValidationInput, 'strict'> {
  const resolvedSources: ValidationSourceItem[] = [];
  const missingSources: string[] = [];
  const seen = new Set<string>();
  const cwd = options.cwd ?? process.cwd();
  const sourceFileLimit = options.sourceFileLimit ?? DEFAULT_SOURCE_FILE_LIMIT;

  for (const source of requestedSources) {
    const abs = path.resolve(cwd, source);
    if (fs.existsSync(abs)) {
      const stat = fs.statSync(abs);
      if (stat.isFile()) {
        const content = tryReadFile(abs);
        if (content === null) {
          missingSources.push(source);
          continue;
        }
        const key = path.normalize(abs);
        if (seen.has(key)) {
          continue;
        }
        seen.add(key);
        resolvedSources.push({ path: source, content });
        continue;
      }

      if (stat.isDirectory()) {
        const files = collectReadableFiles(abs, sourceFileLimit);
        if (files.length === 0) {
          missingSources.push(source);
          continue;
        }
        for (const file of files) {
          const key = path.normalize(file);
          if (seen.has(key)) {
            continue;
          }
          seen.add(key);
          const content = tryReadFile(file);
          if (content === null) {
            continue;
          }
          resolvedSources.push({ path: path.relative(cwd, file), content });
          if (resolvedSources.length >= sourceFileLimit) {
            break;
          }
        }
      }
    } else if (/\s/.test(source)) {
      resolvedSources.push({ path: `inline:${source.slice(0, 40)}`, content: source });
    } else {
      missingSources.push(source);
    }

    if (resolvedSources.length >= sourceFileLimit) {
      break;
    }
  }

  return {
    requestedSources,
    resolvedSources,
    missingSources,
  };
}

export function collectReadableFiles(root: string, sourceFileLimit = DEFAULT_SOURCE_FILE_LIMIT): string[] {
  const stack: string[] = [root];
  const files: string[] = [];
  while (stack.length > 0 && files.length < sourceFileLimit) {
    const current = stack.pop();
    if (!current) {
      continue;
    }
    let entries: fs.Dirent[] = [];
    try {
      entries = fs.readdirSync(current, { withFileTypes: true });
    } catch {
      continue;
    }
    entries.sort((a, b) => a.name.localeCompare(b.name));
    for (const entry of entries) {
      const abs = path.join(current, entry.name);
      if (entry.isDirectory()) {
        stack.push(abs);
        continue;
      }
      if (!entry.isFile()) {
        continue;
      }
      const ext = path.extname(entry.name).toLowerCase();
      if (SUPPORTED_EXTENSIONS.has(ext) || entry.name.toLowerCase().includes('requirement')) {
        files.push(abs);
        if (files.length >= sourceFileLimit) {
          break;
        }
      }
    }
  }
  return files;
}

export function tryReadFile(filePath: string): string | null {
  try {
    const stat = fs.statSync(filePath);
    if (!stat.isFile() || stat.size > 1024 * 1024) {
      return null;
    }
    return fs.readFileSync(filePath, 'utf8');
  } catch {
    return null;
  }
}

export function formatSourceSummary(input: ValidationInput): string {
  const resolvedPreview = input.resolvedSources
    .slice(0, 5)
    .map((source) => `- ${source.path}`)
    .join('\n');

  return `
## Source Inputs
- Requested: ${input.requestedSources.length}
- Resolved: ${input.resolvedSources.length}
- Missing: ${input.missingSources.length}
${resolvedPreview ? `- Sample:\n${resolvedPreview}` : ''}
`.trim();
}

export function toValidationInput(input: unknown): ValidationInput {
  if (input && typeof input === 'object') {
    const candidate = input as Record<string, unknown>;
    const requestedSources = candidate['requestedSources'];
    const resolvedSources = candidate['resolvedSources'];
    const missingSources = candidate['missingSources'];
    if (
      Array.isArray(requestedSources) &&
      Array.isArray(resolvedSources) &&
      Array.isArray(missingSources)
    ) {
      const validRequestedSources = requestedSources.filter(
        (value): value is string => typeof value === 'string',
      );
      const validResolvedSources = resolvedSources.filter(
        (value): value is ValidationSourceItem => isValidationSourceItem(value),
      );
      const validMissingSources = missingSources.filter(
        (value): value is string => typeof value === 'string',
      );

      const invalidRequestedCount = requestedSources.length - validRequestedSources.length;
      const invalidResolvedCount = resolvedSources.length - validResolvedSources.length;
      const invalidMissingCount = missingSources.length - validMissingSources.length;

      if (invalidRequestedCount > 0 || invalidResolvedCount > 0 || invalidMissingCount > 0) {
        console.warn('[ValidationTaskAdapter] Ignored invalid source entries in validation input.', {
          invalidRequestedCount,
          invalidResolvedCount,
          invalidMissingCount,
        });
      }

      return {
        requestedSources: validRequestedSources,
        resolvedSources: validResolvedSources,
        missingSources: validMissingSources,
        strict: Boolean(candidate['strict']),
      };
    }
  }
  if (typeof input === 'string') {
    return {
      requestedSources: ['inline'],
      resolvedSources: [{ path: 'inline', content: input }],
      missingSources: [],
      strict: false,
    };
  }
  if (input && typeof input === 'object') {
    return {
      requestedSources: [],
      resolvedSources: [{ path: 'inline:object', content: JSON.stringify(input, null, 2) }],
      missingSources: [],
      strict: false,
    };
  }
  return {
    requestedSources: [],
    resolvedSources: [],
    missingSources: [],
    strict: false,
  };
}

export function isValidationSourceItem(value: unknown): value is ValidationSourceItem {
  if (!value || typeof value !== 'object') {
    return false;
  }
  const candidate = value as Record<string, unknown>;
  const pathValue = candidate['path'];
  const contentValue = candidate['content'];
  return (
    typeof pathValue === 'string' &&
    pathValue.trim().length > 0 &&
    typeof contentValue === 'string' &&
    contentValue.trim().length > 0
  );
}
