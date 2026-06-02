import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { join, resolve, dirname } from 'node:path';
import { spawnSync } from 'node:child_process';

const scriptPath = resolve('scripts/verify/run-model-checks.mjs');
const tmpRoot = resolve('.codex-local/tmp');

const makeRepo = () => {
  mkdirSync(tmpRoot, { recursive: true });
  const dir = mkdtempSync(join(tmpRoot, 'run-model-checks-security-'));
  mkdirSync(join(dir, 'spec', 'formal'), { recursive: true });
  writeFileSync(join(dir, 'spec', 'formal', 'safe;name.als'), 'sig A {}\n', 'utf8');
  return dir;
};

const makeFakeJava = (dir: string) => {
  const bin = join(dir, 'bin');
  mkdirSync(bin, { recursive: true });
  const log = join(dir, 'java-argv.json');
  const java = join(bin, 'java');
  writeFileSync(java, `#!/usr/bin/env node\nimport fs from 'node:fs';\nfs.writeFileSync(${JSON.stringify(log)}, JSON.stringify(process.argv.slice(2)));\nconsole.log('fake alloy ok');\n`, { mode: 0o755 });
  return { bin, log };
};

describe('run-model-checks Alloy execution security', () => {
  it('ignores ALLOY_RUN_CMD shell templates and passes Alloy file paths as argv', () => {
    const dir = makeRepo();
    const marker = join(dir, 'shell-marker');
    const alloyJar = join(dir, '.cache', 'tools', 'alloy.jar');
    mkdirSync(dirname(alloyJar), { recursive: true });
    writeFileSync(alloyJar, 'fake jar', 'utf8');
    const fakeJava = makeFakeJava(dir);

    const result = spawnSync(process.execPath, [scriptPath], {
      cwd: dir,
      encoding: 'utf8',
      env: {
        ...process.env,
        ALLOY_JAR: alloyJar,
        ALLOY_RUN_CMD: `node -e "require('fs').writeFileSync('${marker}', 'executed')"`,
        ALLOY_CMD_JSON: '["exec","-q","-o","-","-f","{file}"]',
        PATH: `${fakeJava.bin}:${process.env.PATH ?? ''}`,
      },
    });

    expect(result.status).toBe(0);
    expect(existsSync(marker)).toBe(false);
    expect(result.stderr + result.stdout).toContain('ALLOY_RUN_CMD shell templates are ignored');
    const argv = JSON.parse(readFileSync(fakeJava.log, 'utf8')) as string[];
    expect(argv.slice(0, 6)).toEqual(['-jar', alloyJar, 'exec', '-q', '-o', '-']);
    expect(argv[6]).toBe('-f');
    expect(argv[7]).toBe(join(dir, 'spec', 'formal', 'safe;name.als'));

    const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'codex', 'model-check.json'), 'utf8'));
    expect(summary.alloy.results[0].ok).toBe(true);
  });
});
