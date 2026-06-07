import fs from 'node:fs';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import {
  ARTIFACT_PROVENANCE_SCHEMA_VERSION,
  buildArtifactProvenance,
  normalizeSubjectPath,
  validateArtifactProvenance,
  validateArtifactProvenanceSchema,
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
        workflowRefPrefix: 'itdojp/ae-framework/.github/workflows/pr-ci-status-comment.yml@',
        runId: '123456789',
        runAttempt: '2',
        eventName: 'pull_request',
        headSha: 'a'.repeat(40),
        baseSha: 'b'.repeat(40),
        prNumber: '3464',
      },
      requireSubjects: ['summary/PR_SUMMARY.md'],
    })).toEqual([]);
    expect(validateArtifactProvenanceSchema(provenance)).toEqual([]);
  });

  it('derives PR head provenance from workflow_run events', () => {
    const root = makeTmpDir();
    fs.mkdirSync(path.join(root, 'ci'), { recursive: true });
    fs.writeFileSync(path.join(root, 'ci', 'policy-gate-summary.json'), '{"ok":true}\n');
    const eventPath = path.join(root, 'workflow-run-event.json');
    fs.writeFileSync(eventPath, JSON.stringify({
      workflow_run: {
        id: 27086228694,
        head_sha: 'e'.repeat(40),
        head_repository: { full_name: 'itdojp/ae-framework' },
        pull_requests: [
          {
            number: 3468,
            base: { sha: 'f'.repeat(40), repo: { full_name: 'itdojp/ae-framework' } },
          },
        ],
      },
      repository: { full_name: 'itdojp/ae-framework' },
    }));

    const provenance = buildArtifactProvenance({
      artifactName: 'policy-gate-artifacts',
      root,
      subjects: ['ci/policy-gate-summary.json'],
      generatedAt: '2026-06-07T00:00:00.000Z',
      env: {
        GITHUB_REPOSITORY: 'itdojp/ae-framework',
        GITHUB_WORKFLOW: 'Policy Gate',
        GITHUB_WORKFLOW_REF: 'itdojp/ae-framework/.github/workflows/policy-gate.yml@refs/heads/main',
        GITHUB_RUN_ID: '27086228694',
        GITHUB_RUN_ATTEMPT: '1',
        GITHUB_EVENT_NAME: 'workflow_run',
        GITHUB_SHA: 'c'.repeat(40),
        GITHUB_EVENT_PATH: eventPath,
      } as any,
    });

    expect(provenance.producer.prNumber).toBe(3468);
    expect(provenance.producer.headSha).toBe('e'.repeat(40));
    expect(provenance.producer.baseSha).toBe('f'.repeat(40));
    expect(provenance.producer.headRepository).toBe('itdojp/ae-framework');
    expect(provenance.producer.baseRepository).toBe('itdojp/ae-framework');
  });

  it('preserves fork head repository provenance from pull_request events', () => {
    const root = makeTmpDir();
    fs.writeFileSync(path.join(root, 'artifact.json'), '{"ok":true}\n');
    const eventPath = path.join(root, 'fork-pr-event.json');
    fs.writeFileSync(eventPath, JSON.stringify({
      pull_request: {
        number: 3468,
        head: { sha: 'a'.repeat(40), repo: { full_name: 'external/forked-ae-framework' } },
        base: { sha: 'b'.repeat(40), repo: { full_name: 'itdojp/ae-framework' } },
      },
      repository: { full_name: 'itdojp/ae-framework' },
    }));

    const provenance = buildArtifactProvenance({
      artifactName: 'policy-gate-artifacts',
      root,
      subjects: ['artifact.json'],
      env: {
        GITHUB_REPOSITORY: 'itdojp/ae-framework',
        GITHUB_WORKFLOW: 'Policy Gate',
        GITHUB_WORKFLOW_REF: 'itdojp/ae-framework/.github/workflows/policy-gate.yml@refs/pull/3468/merge',
        GITHUB_RUN_ID: '27086228694',
        GITHUB_RUN_ATTEMPT: '1',
        GITHUB_EVENT_NAME: 'pull_request',
        GITHUB_SHA: 'c'.repeat(40),
        GITHUB_EVENT_PATH: eventPath,
      } as any,
    });

    expect(validateArtifactProvenance({
      provenance,
      root,
      expected: {
        artifactName: 'policy-gate-artifacts',
        headRepository: 'external/forked-ae-framework',
        baseRepository: 'itdojp/ae-framework',
      },
      requireSubjects: ['artifact.json'],
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
        GITHUB_WORKFLOW_REF: 'itdojp/ae-framework/.github/workflows/quality-gates-centralized.yml@refs/pull/42/merge',
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

  it('fails validation when producer workflow ref does not match the trusted workflow file', () => {
    const root = makeTmpDir();
    fs.writeFileSync(path.join(root, 'artifact.json'), '{"ok":true}\n');
    const provenance = buildArtifactProvenance({
      artifactName: 'quality-gates-report',
      root,
      subjects: ['artifact.json'],
      env: {
        GITHUB_REPOSITORY: 'itdojp/ae-framework',
        GITHUB_WORKFLOW: 'Quality Gates',
        GITHUB_WORKFLOW_REF: 'itdojp/ae-framework/.github/workflows/quality-gates-centralized.yml@refs/pull/1/merge',
        GITHUB_RUN_ID: '42',
        GITHUB_RUN_ATTEMPT: '1',
        GITHUB_EVENT_NAME: 'pull_request',
        GITHUB_SHA: 'd'.repeat(40),
      } as any,
    });

    const errors = validateArtifactProvenance({
      provenance,
      root,
      expected: {
        workflowRefPrefix: 'itdojp/ae-framework/.github/workflows/pr-ci-status-comment.yml@',
      },
    });

    expect(errors.join('\n')).toContain('producer.workflowRef prefix mismatch');
  });

  it('fails validation when artifact metadata does not satisfy the provenance schema', () => {
    const errors = validateArtifactProvenance({
      provenance: {
        schemaVersion: ARTIFACT_PROVENANCE_SCHEMA_VERSION,
        generatedAt: '2026-06-07T00:00:00.000Z',
        artifact: {
          name: 'broken-artifact',
          subjects: [
            {
              path: 'artifact.json',
              sha256: 'not-a-digest',
              size: -1,
            },
          ],
        },
        producer: {
          repository: 'itdojp/ae-framework',
          workflow: 'Policy Gate',
          workflowRef: '',
          runId: '1',
          runAttempt: '1',
          eventName: 'pull_request',
          headSha: 'not-a-sha',
          baseSha: '',
          prNumber: 3468,
          headRepository: '',
          baseRepository: '',
        },
      },
      root: makeTmpDir(),
    });

    expect(errors.join('\n')).toContain('artifact provenance schema');
    expect(errors.join('\n')).toContain('must NOT have fewer than 1 characters');
    expect(errors.join('\n')).toContain('invalid sha256');
  });

  it('rejects absolute and parent-traversal subject paths', () => {
    expect(() => normalizeSubjectPath('/tmp/report.json')).toThrow(/repository-relative/);
    expect(() => normalizeSubjectPath('../report.json')).toThrow(/artifact root/);
    expect(() => normalizeSubjectPath('safe/../../report.json')).toThrow(/artifact root/);
  });
});
