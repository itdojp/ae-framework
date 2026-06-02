import { afterEach, describe, expect, it, vi } from 'vitest';
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { RustVerificationAgent } from '../../../src/agents/rust-verification-agent.js';

vi.mock('node:child_process', () => ({
  execFileSync: vi.fn(() => ''),
}));
vi.mock('child_process', () => ({
  execFileSync: vi.fn(() => ''),
}));

const artifactRoot = join(process.cwd(), 'artifacts', 'testing');

function makeWorkspace(): { projectPath: string; sourcePath: string; cleanup: () => void } {
  mkdirSync(artifactRoot, { recursive: true });
  const projectPath = join(artifactRoot, `rust-agent-mutation-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`);
  const sourcePath = join(projectPath, 'src', 'main.rs');
  mkdirSync(join(projectPath, 'src'), { recursive: true });
  writeFileSync(join(projectPath, 'Cargo.toml'), '[package]\nname = "fixture"\nversion = "0.1.0"\nedition = "2021"\n', 'utf8');
  writeFileSync(sourcePath, 'fn main() {\n    println!("ok");\n}\n', 'utf8');
  return {
    projectPath,
    sourcePath,
    cleanup: () => rmSync(projectPath, { recursive: true, force: true }),
  };
}

describe('RustVerificationAgent mutation policy', () => {
  let cleanup: (() => void) | undefined;

  afterEach(() => {
    cleanup?.();
    cleanup = undefined;
  });

  it('does not mutate Rust sources for annotation preparation unless explicitly enabled', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const original = readFileSync(fixture.sourcePath, 'utf8');
    const agent = new RustVerificationAgent();

    await agent.verifyRustProject({
      projectPath: fixture.projectPath,
      sourceFiles: [{
        path: fixture.sourcePath,
        content: original,
        annotations: [{ type: 'assert', line: 1, content: 'true' }],
      }],
      verificationTools: [],
      options: { generateReport: false },
    });

    expect(readFileSync(fixture.sourcePath, 'utf8')).toBe(original);
  });

  it('writes combined reports into target/ae-verification instead of the project root', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const original = readFileSync(fixture.sourcePath, 'utf8');
    const agent = new RustVerificationAgent();

    await agent.verifyRustProject({
      projectPath: fixture.projectPath,
      sourceFiles: [{ path: fixture.sourcePath, content: original }],
      verificationTools: [],
      options: { generateReport: true },
    });

    expect(existsSync(join(fixture.projectPath, 'verification-report.json'))).toBe(false);
    expect(existsSync(join(fixture.projectPath, 'target', 'ae-verification', 'verification-report.json'))).toBe(true);
  });
});
