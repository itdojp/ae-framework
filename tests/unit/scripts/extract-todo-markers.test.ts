import { describe, expect, it } from 'vitest';
import {
  csvEscape,
  normalizeMarker,
  shouldIncludeFile,
  topLevelArea,
} from '../../../scripts/maintenance/extract-todo-markers.mjs';

describe('extract-todo-markers helpers', () => {
  it('detects TODO markers only in intentional contexts', () => {
    expect(normalizeMarker('// TODO: implement this', 'src/main.ts')).toBe('TODO');
    expect(normalizeMarker('TODO(#2333) handle follow-up', 'src/main.ts')).toBe('TODO');
    expect(normalizeMarker('const label = "todo-app"', 'src/main.ts')).toBeNull();
  });

  it('skips markdown prose TODO occurrences', () => {
    expect(normalizeMarker('**A complete TODO app is ready**', 'docs/article.md')).toBeNull();
    expect(normalizeMarker('# TODO/FIXME/XXX Triage Runbook', 'docs/runbook.md')).toBeNull();
    expect(normalizeMarker('// TODO: placeholder in fenced code', 'docs/template.md')).toBe('TODO');
  });

  it('escapes CSV values safely', () => {
    expect(csvEscape('plain')).toBe('plain');
    expect(csvEscape('a,b')).toBe('"a,b"');
    expect(csvEscape('a"b')).toBe('"a""b"');
    expect(csvEscape('a\nb')).toBe('"a\nb"');
  });

  it('classifies top-level area consistently', () => {
    expect(topLevelArea('README.md')).toBe('(root)');
    expect(topLevelArea('src/index.ts')).toBe('src');
  });

  it('excludes generated and explicitly excluded files', () => {
    const options = {
      excludedPrefixes: ['tmp/', 'dist/'],
      excludedFiles: new Set(['docs/maintenance/custom.csv']),
    };

    expect(shouldIncludeFile('src/main.ts', options)).toBe(true);
    expect(shouldIncludeFile('tmp/report.csv', options)).toBe(false);
    expect(shouldIncludeFile('docs/maintenance/custom.csv', options)).toBe(false);
    expect(shouldIncludeFile('docs/maintenance/todo-triage-inventory-2026-02-28.md', options)).toBe(false);
  });
});
