import fs from 'node:fs';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import {
  ARTIFACT_PROVENANCE_SCHEMA_VERSION,
  buildArtifactProvenance,
  normalizeSubjectPath,
  validateArtifactProvenance,
} from '../../../scripts/ci/lib/artifact-provenance.mjs';

const tmpDirs: string[] = [];

const makeTmpDir = () => {
  const base = path.join(process.cwd(), 'artifacts', 'tmp', 'unit-tests');
  fs.mkdirSync(base, { recursive: true });
  const dir = fs.mkdtempSync(path.join(base, 'ae-artifact-provenance-'));
  tmpDirs.push(dir);
  return dir;
};

afterEach(() => {
  for (const dir of tmpDirs.splice(0)) {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

describe('artifact provenance helpers', () => {
  it('writes and validates provenance bound to workflow and subject digest', () => {
    const root = makeTmpDir();
    fs.mkdirSync(path.join(root, 'summary'), { recursive: true });
    fs.writeFileSync(path.join(root, 'summary', 'PR_SUMMARY.md'), 'trusted publisher input\n');
    const eventPath = path.join(root, 'event.json');
    fs.writeFileSync(eventPath, JSON.stringify({
      pull_request: {
        number: 3464,
        head: { sha: 'a'.repeat(40), repo: { full_name: 'itdojp/ae-framework' } },
        base: { sha: 'b'.repeat(40), repo: { full_name: 'itdojp/ae-framework' } },
      },
    }));

    const provenance = buildArtifactProvenance({
      artifactName: 'pr-summary-publish-pr-3464',
      root,
      subjects: ['summary/PR_SUMMARY.md'],
      generatedAt: '2026-06-07T00:00:00.000Z',
      env: {
        GITHUB_REPOSITORY: 'itdojp/ae-framework',
        GITHUB_WORKFLOW: 'PR Maintenance',
        GITHUB_WORKFLOW_REF: 'itdojp/ae-framework/.github/workflows/pr-ci-status-comment.yml@refs/pull/3464/merge',
        GITHUB_RUN_ID: '123456789',
        GITHUB_RUN_ATTEMPT: '2',
        GITHUB_EVENT_NAME: 'pull_request',
        GITHUB_SHA: 'c'.repeat(40),
        GITHUB_EVENT_PATH: eventPath,
      } as any,
    });

    expect(provenance.schemaVersion).toBe(ARTIFACT_PROVENANCE_SCHEMA_VERSION);
    expect(provenance.producer.headSha).toBe('a'.repeat(40));
    expect(provenance.producer.baseSha).toBe('b'.repeat(40));
    expect(provenance.producer.prNumber).toBe(3464);
    expect(provenance.artifact.subjects).toHaveLength(1);

    expect(validateArtifactProvenance({
      provenance,
      root,
      expected: {
        artifactName: 'pr-summary-publish-pr-3464',
        repository: 'itdojp/ae-framework',
        workflow: 'PR Maintenance',
        runId: '123456789',
        runAttempt: '2',
        eventName: 'pull_request',
        headSha: 'a'.repeat(40),
        baseSha: 'b'.repeat(40),
        prNumber: '3464',
      },
      requireSubjects: ['summary/PR_SUMMARY.md'],
    })).toEqual([]);
  });

  it('fails validation when a subject is changed after provenance is written', () => {
    const root = makeTmpDir();
    fs.writeFileSync(path.join(root, 'artifact.json'), '{"ok":true}\n');
    const provenance = buildArtifactProvenance({
      artifactName: 'quality-gates-report',
      root,
      subjects: ['artifact.json'],
      env: {
        GITHUB_REPOSITORY: 'itdojp/ae-framework',
        GITHUB_WORKFLOW: 'Quality Gates',
        GITHUB_RUN_ID: '42',
        GITHUB_RUN_ATTEMPT: '1',
        GITHUB_EVENT_NAME: 'pull_request',
        GITHUB_SHA: 'd'.repeat(40),
      } as any,
    });

    fs.writeFileSync(path.join(root, 'artifact.json'), '{"ok":false}\n');
    const errors = validateArtifactProvenance({
      provenance,
      root,
      expected: { artifactName: 'quality-gates-report', runId: '42' },
      requireSubjects: ['artifact.json'],
    });

    expect(errors.join('\n')).toContain('sha256 mismatch');
  });

  it('rejects absolute and parent-traversal subject paths', () => {
    expect(() => normalizeSubjectPath('/tmp/report.json')).toThrow(/repository-relative/);
    expect(() => normalizeSubjectPath('../report.json')).toThrow(/artifact root/);
    expect(() => normalizeSubjectPath('safe/../../report.json')).toThrow(/artifact root/);
  });
});
