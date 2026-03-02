import { describe, expect, it } from 'vitest';
import {
  collectNonDocs,
  hasLabel,
  isActorAllowed,
  isDocsPath,
  normalizeLabelNames,
  parseActorCsv,
  resolveReviewActors,
  toActorSet,
} from '../../../scripts/ci/lib/automation-guards.mjs';

describe('automation-guards', () => {
  it('parses actor csv with fallback', () => {
    expect(parseActorCsv('', 'a,b')).toEqual(['a', 'b']);
    expect(parseActorCsv(' x, y ,,z ')).toEqual(['x', 'y', 'z']);
  });

  it('resolves review actors from primary/legacy env with fallback', () => {
    expect(resolveReviewActors('actor-a, actor-b', 'legacy-a', 'fallback-a')).toEqual(['actor-a', 'actor-b']);
    expect(resolveReviewActors('', 'legacy-a, legacy-b', 'fallback-a')).toEqual(['legacy-a', 'legacy-b']);
    expect(resolveReviewActors('', '', 'fallback-a, fallback-b')).toEqual(['fallback-a', 'fallback-b']);
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

  it('does not trim file paths before docs matching', () => {
    expect(isDocsPath(' docs/guide.md')).toBe(false);
    expect(isDocsPath('README.md ')).toBe(false);
    expect(collectNonDocs(['docs/a.md', ' README.md', 'src/main.ts'])).toEqual([
      ' README.md',
      'src/main.ts',
    ]);
  });
});
