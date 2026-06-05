import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, expect, it } from 'vitest';

const writeJson = (filePath: string, value: unknown) => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`);
};

describe('aggregate-formal-reports', () => {
  it('escapes untrusted formal artifact fields before writing PR-facing markdown', () => {
    const repoRoot = process.cwd();
    const tmpRoot = path.join(repoRoot, '.codex-local', 'tmp');
    fs.mkdirSync(tmpRoot, { recursive: true });
    const workdir = fs.mkdtempSync(path.join(tmpRoot, 'formal-aggregate-'));

    try {
      writeJson(path.join(workdir, 'artifacts_dl', 'formal-reports-csp', 'csp-summary.json'), {
        status: '<script>@formal-reviewers</script>',
        backend: '`fdr` <unsafe>',
        resultStatus: '@team passed <maybe>',
        exitCode: 0,
      });
      writeJson(path.join(workdir, 'artifacts_dl', 'formal-reports-apalache', 'apalache-summary.json'), {
        version: '1.0.0',
        ok: false,
        ran: true,
        status: '@ops <failed>',
        errors: ['<counterexample>@ops should not ping reviewers</counterexample>'],
      });

      const result = spawnSync(
        process.execPath,
        [path.join(repoRoot, 'scripts', 'formal', 'aggregate-formal-reports.mjs')],
        {
          cwd: workdir,
          env: {
            ...process.env,
            FORMAL_AGG_LINE_CLAMP: '120',
            FORMAL_AGG_ERRORS_LIMIT: '1',
          },
          encoding: 'utf8',
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const markdown = fs.readFileSync(
        path.join(workdir, 'artifacts', 'formal', 'formal-aggregate.md'),
        'utf8',
      );
      const escapedFormalMention = '@\u200bformal-reviewers';
      const escapedOpsMention = '@\u200bops';

      expect(markdown).toContain('&lt;script&gt;');
      expect(markdown).toContain(escapedFormalMention);
      expect(markdown).toContain(escapedOpsMention);
      expect(markdown).not.toContain('<script>');
      expect(markdown).not.toContain('@formal-reviewers');
      expect(markdown).not.toContain('@ops should not ping');
    } finally {
      fs.rmSync(workdir, { recursive: true, force: true });
      try {
        if (fs.existsSync(tmpRoot) && fs.readdirSync(tmpRoot).length === 0) {
          fs.rmdirSync(tmpRoot);
        }
      } catch {
        // Best-effort cleanup only; test assertions above are authoritative.
      }
    }
  });
});
