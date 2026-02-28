#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

const DEFAULT_OUTPUT_CSV = 'tmp/maintenance/todo-markers.csv';
const DEFAULT_OUTPUT_MD = 'tmp/maintenance/todo-markers-summary.md';
const DEFAULT_EXCLUDED_PREFIXES = [
  'node_modules/',
  'dist/',
  'coverage/',
  'artifacts/',
  'tmp/',
  'temp-reports/',
];
const GENERATED_INVENTORY_PATTERN =
  /^docs\/maintenance\/todo-triage-inventory-\d{4}-\d{2}-\d{2}\.(csv|md)$/;
const MARKER_PATTERN = /\b(TODO|FIXME|XXX)\b/g;
const STRUCTURED_SUFFIX_PATTERN = /^\s*(?:\(#\d+\))?\s*:/;
const ISSUE_REF_SUFFIX_PATTERN = /^\s*\(#\d+\)/;
const COMMENT_PREFIX_PATTERN = /^\s*(?:\/\/|#(?!#)|\/\*|\*|--|;|<!--)/;

const usage = () => {
  console.log(`Usage: node scripts/maintenance/extract-todo-markers.mjs [options]

Options:
  --output-csv <path>   Output CSV path (default: ${DEFAULT_OUTPUT_CSV})
  --output-md <path>    Output markdown summary path (default: ${DEFAULT_OUTPUT_MD})
  --exclude-prefix <p>  Exclude files under prefix (repeatable)
  --help                Show this help
`);
};

const parseArgs = (argv) => {
  const options = {
    outputCsv: DEFAULT_OUTPUT_CSV,
    outputMd: DEFAULT_OUTPUT_MD,
    excludedPrefixes: [...DEFAULT_EXCLUDED_PREFIXES],
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--output-csv') {
      options.outputCsv = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--exclude-prefix') {
      const prefix = String(argv[++i] || '').trim();
      if (prefix) options.excludedPrefixes.push(prefix);
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.outputCsv) throw new Error('--output-csv is required');
  if (!options.outputMd) throw new Error('--output-md is required');
  return options;
};

const getRepoRoot = () =>
  execFileSync('git', ['rev-parse', '--show-toplevel'], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  }).trim();

const listTrackedFiles = (repoRoot) =>
  execFileSync('git', ['-C', repoRoot, 'ls-files', '-z'], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  })
    .split('\u0000')
    .map((item) => item.trim())
    .filter(Boolean);

const toPosixPath = (filePath) => filePath.split(path.sep).join('/');

const toRepoRelativePath = (repoRoot, filePath) => {
  const relative = path.relative(repoRoot, path.resolve(filePath));
  return toPosixPath(relative);
};

const normalizeMarker = (line) => {
  for (const match of line.matchAll(MARKER_PATTERN)) {
    const marker = match[1];
    const index = match.index ?? -1;
    if (index < 0) continue;

    const suffix = line.slice(index + marker.length);
    if (STRUCTURED_SUFFIX_PATTERN.test(suffix) || ISSUE_REF_SUFFIX_PATTERN.test(suffix)) {
      return marker;
    }

    const prefix = line.slice(0, index);
    if (COMMENT_PREFIX_PATTERN.test(prefix)) {
      return marker;
    }
  }
  return null;
};

const parseIssueRefs = (line) => {
  const refs = [];
  const regex = /#(\d+)/g;
  let match = regex.exec(line);
  while (match) {
    refs.push(`#${match[1]}`);
    match = regex.exec(line);
  }
  return refs;
};

const csvEscape = (value) => {
  const text = String(value ?? '');
  if (/[",\n]/.test(text)) {
    return `"${text.replace(/"/g, '""')}"`;
  }
  return text;
};

const topLevelArea = (filePath) => {
  const parts = filePath.split('/');
  if (parts.length <= 1) return '(root)';
  return parts[0];
};

try {
  const repoRoot = getRepoRoot();
  const options = parseArgs(process.argv.slice(2));
  const excludedFiles = new Set([
    toRepoRelativePath(repoRoot, options.outputCsv),
    toRepoRelativePath(repoRoot, options.outputMd),
  ]);
  const files = listTrackedFiles(repoRoot).filter(
    (file) =>
      !options.excludedPrefixes.some((prefix) => file.startsWith(prefix)) &&
      !excludedFiles.has(file) &&
      !GENERATED_INVENTORY_PATTERN.test(file),
  );
  const rows = [];
  let idCounter = 1;

  for (const file of files) {
    let content;
    try {
      content = fs.readFileSync(path.join(repoRoot, file), 'utf8');
    } catch {
      continue;
    }
    if (content.includes('\u0000')) {
      continue;
    }

    const lines = content.split('\n');
    for (let index = 0; index < lines.length; index += 1) {
      const rawLine = lines[index];
      const marker = normalizeMarker(rawLine);
      if (!marker) continue;

      const issueRefs = parseIssueRefs(rawLine);
      rows.push({
        id: `TD-${String(idCounter).padStart(4, '0')}`,
        file,
        line: index + 1,
        marker,
        text: rawLine.trim(),
        issueRefs: issueRefs.join(' '),
        hasIssueRef: issueRefs.length > 0 ? 'yes' : 'no',
        area: topLevelArea(file),
        triageStatus: '',
        severity: '',
        impact: '',
        reproducibility: '',
        dependency: '',
        owner: '',
        due: '',
        notes: '',
      });
      idCounter += 1;
    }
  }

  const countsByMarker = rows.reduce((acc, row) => {
    acc[row.marker] = (acc[row.marker] || 0) + 1;
    return acc;
  }, {});
  const countsByArea = rows.reduce((acc, row) => {
    acc[row.area] = (acc[row.area] || 0) + 1;
    return acc;
  }, {});
  const sortedAreaEntries = Object.entries(countsByArea).sort((a, b) => b[1] - a[1]);

  const headers = [
    'id',
    'file',
    'line',
    'marker',
    'text',
    'issue_refs',
    'has_issue_ref',
    'area',
    'triage_status',
    'severity',
    'impact',
    'reproducibility',
    'dependency',
    'owner',
    'due',
    'notes',
  ];
  const csvLines = [headers.join(',')];
  for (const row of rows) {
    const values = [
      row.id,
      row.file,
      row.line,
      row.marker,
      row.text,
      row.issueRefs,
      row.hasIssueRef,
      row.area,
      row.triageStatus,
      row.severity,
      row.impact,
      row.reproducibility,
      row.dependency,
      row.owner,
      row.due,
      row.notes,
    ];
    csvLines.push(values.map(csvEscape).join(','));
  }

  const markdown = `# TODO Marker Inventory Summary

- generatedAt: ${new Date().toISOString()}
- tracked files scanned: ${files.length}
- markers found: ${rows.length}
- excluded prefixes: ${options.excludedPrefixes.join(', ')}

## Counts by marker

- TODO: ${countsByMarker.TODO || 0}
- FIXME: ${countsByMarker.FIXME || 0}
- XXX: ${countsByMarker.XXX || 0}

## Top areas (by count)

${sortedAreaEntries
  .slice(0, 15)
  .map(([area, count]) => `- ${area}: ${count}`)
  .join('\n')}
`;

  const csvPath = path.resolve(options.outputCsv);
  const mdPath = path.resolve(options.outputMd);
  fs.mkdirSync(path.dirname(csvPath), { recursive: true });
  fs.mkdirSync(path.dirname(mdPath), { recursive: true });
  fs.writeFileSync(csvPath, `${csvLines.join('\n')}\n`, 'utf8');
  fs.writeFileSync(mdPath, markdown, 'utf8');

  console.log(`[todo-extract] wrote ${csvPath}`);
  console.log(`[todo-extract] wrote ${mdPath}`);
  console.log(`[todo-extract] markers=${rows.length}`);
} catch (error) {
  console.error(`[todo-extract] ${error instanceof Error ? error.message : String(error)}`);
  process.exit(1);
}
