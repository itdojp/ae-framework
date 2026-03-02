import { describe, expect, it } from 'vitest';
import {
  buildActionTaskFromComment,
  classifyReviewCommentBody,
  extractSuggestionBlocks,
  isActionableText,
  summarizeActionTasks,
} from '../../../scripts/ci/lib/review-comment-classifier.mjs';

describe('review-comment-classifier', () => {
  it('extracts suggestion blocks from review body', () => {
    const body = [
      'Please apply this.',
      '```suggestion',
      'const x = 1;',
      '```',
      'And this too.',
      '```suggestion',
      'const y = 2;',
      '```',
    ].join('\n');
    expect(extractSuggestionBlocks(body)).toEqual(['const x = 1;\n', 'const y = 2;\n']);
  });

  it('classifies suggestion comments first', () => {
    const classification = classifyReviewCommentBody('```suggestion\nreturn value;\n```');
    expect(classification.category).toBe('suggestion');
    expect(classification.reason).toBe('contains-suggestion-block');
  });

  it('detects actionable text in English and Japanese', () => {
    expect(isActionableText('Please add null check for this branch.')).toBe(true);
    expect(isActionableText('ここは命名を統一してください。')).toBe(true);
    expect(isActionableText('Thanks! Please rename this helper.')).toBe(true);
    expect(isActionableText('Looks good to me, thanks.')).toBe(false);
  });

  it('builds deterministic action task from actionable comment', () => {
    const task = buildActionTaskFromComment({
      id: 10,
      path: 'src/app.ts',
      start_line: 40,
      line: 42,
      body: 'Can you replace this with a typed helper and add tests?',
      html_url: 'https://example.com/comment/10',
    });

    expect(task).toMatchObject({
      source: 'review_comment',
      commentId: 10,
      path: 'src/app.ts',
      startLine: 40,
      endLine: 42,
      title: 'Address actionable review comment (src/app.ts:40)',
    });
    expect(task?.instruction).toContain('typed helper');
  });

  it('returns null task for non-actionable comment', () => {
    const task = buildActionTaskFromComment({
      id: 11,
      path: 'src/app.ts',
      line: 1,
      body: 'LGTM',
    });
    expect(task).toBeNull();
  });

  it('returns null task when comment id is missing (fail-closed)', () => {
    const task = buildActionTaskFromComment({
      path: 'src/app.ts',
      line: 12,
      body: 'Please update this branch name.',
    });
    expect(task).toBeNull();
  });

  it('normalizes inverted line range', () => {
    const task = buildActionTaskFromComment({
      id: 30,
      path: 'src/range.ts',
      start_line: 20,
      line: 10,
      body: 'Please replace this block with a helper.',
    });
    expect(task).toMatchObject({
      startLine: 10,
      endLine: 20,
      title: 'Address actionable review comment (src/range.ts:10)',
    });
  });

  it('summarizes tasks deterministically', () => {
    const tasks = [
      buildActionTaskFromComment({
        id: 20,
        path: 'src/a.ts',
        line: 5,
        body: 'Please rename this function to reflect behavior.',
      }),
      buildActionTaskFromComment({
        id: 21,
        path: 'src/b.ts',
        line: 9,
        body: 'Can you add validation for empty inputs?',
      }),
    ].filter(Boolean);
    const summary = summarizeActionTasks(tasks, 5);
    expect(summary).toHaveLength(2);
    expect(summary[0]).toContain('comment=20');
    expect(summary[1]).toContain('location=src/b.ts:9');
  });
});
