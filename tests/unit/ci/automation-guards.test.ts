import { describe, expect, it } from 'vitest';
import {
  collectNonDocs,
  hasLabel,
  isActorAllowed,
  isDocsPath,
  normalizeLabelNames,
  parseActorCsv,
  toActorSet,
} from '../../../scripts/ci/lib/automation-guards.mjs';

describe('automation-guards', () => {
  it('parses actor csv with fallback', () => {
    expect(parseActorCsv('', 'a,b')).toEqual(['a', 'b']);
    expect(parseActorCsv(' x, y ,,z ')).toEqual(['x', 'y', 'z']);
  });

  it('checks actor allowlist case-insensitively', () => {
    const actors = toActorSet(['Copilot', 'github-copilot[bot]']);
    expect(isActorAllowed('copilot', actors)).toBe(true);
    expect(isActorAllowed('GITHUB-COPILOT[BOT]', actors)).toBe(true);
    expect(isActorAllowed('someone-else', actors)).toBe(false);
  });

  it('normalizes labels and checks opt-in label', () => {
    const labels = normalizeLabelNames([
      { name: 'auto-merge' },
      'copilot-auto-fix',
      { foo: 'ignored' },
      '',
    ]);
    expect(labels).toEqual(['auto-merge', 'copilot-auto-fix']);
    expect(hasLabel(labels, 'auto-merge')).toBe(true);
    expect(hasLabel(labels, 'missing')).toBe(false);
  });

  it('applies docs allowlist consistently', () => {
    expect(isDocsPath('docs/guide.md')).toBe(true);
    expect(isDocsPath('README.md')).toBe(true);
    expect(isDocsPath('src/index.ts')).toBe(false);

    expect(collectNonDocs(['docs/a.md', 'README.md', 'src/main.ts'])).toEqual(['src/main.ts']);
  });
});
