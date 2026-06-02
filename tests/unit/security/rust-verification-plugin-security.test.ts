import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { existsSync, mkdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join, relative } from 'node:path';
import { MCPServer, type MCPRequest } from '../../../src/services/mcp-server.js';
import { RustVerificationPlugin } from '../../../src/services/plugins/rust-verification-plugin.js';

vi.mock('node:child_process', () => ({
  execFileSync: vi.fn(() => ''),
}));
vi.mock('child_process', () => ({
  execFileSync: vi.fn(() => ''),
}));

type RustAgentStub = {
  getAvailableTools: () => string[];
  verifyRustProject: ReturnType<typeof vi.fn>;
};

const artifactRoot = join(process.cwd(), 'artifacts', 'testing');

function makeWorkspace(): { workspace: string; cratePath: string; cleanup: () => void } {
  mkdirSync(artifactRoot, { recursive: true });
  const workspace = join(artifactRoot, `rust-plugin-security-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`);
  const cratePath = join(workspace, 'crate');
  mkdirSync(join(cratePath, 'src'), { recursive: true });
  writeFileSync(join(cratePath, 'Cargo.toml'), '[package]\nname = "fixture"\nversion = "0.1.0"\nedition = "2021"\n', 'utf8');
  writeFileSync(join(cratePath, 'src', 'main.rs'), 'fn main() {}\n', 'utf8');
  return {
    workspace,
    cratePath,
    cleanup: () => rmSync(workspace, { recursive: true, force: true }),
  };
}

async function makeServer(workspace: string, rustAgent: RustAgentStub): Promise<MCPServer> {
  const plugin = new RustVerificationPlugin({
    enabledTools: [],
    security: {
      requireOperatorApproval: true,
      workspaceRoot: workspace,
    },
  });
  (plugin as unknown as { rustAgent: RustAgentStub }).rustAgent = rustAgent;
  const server = new MCPServer({
    name: 'rust-security-test',
    version: '1.0.0',
    endpoints: [],
    capabilities: [],
    plugins: [plugin],
  }, workspace);
  await server.start();
  return server;
}

function makeRequest(workspace: string, overrides: Partial<MCPRequest> = {}): MCPRequest {
  const base: MCPRequest = {
    path: '/rust/verify',
    method: 'POST',
    params: {},
    headers: {},
    user: {
      id: 'operator-1',
      name: 'Operator',
      roles: [],
      permissions: ['rust:verify'],
    },
    context: {
      requestId: `req-${Date.now()}`,
      timestamp: Date.now(),
      serverName: 'rust-security-test',
      version: '1.0.0',
      environment: 'testing',
      projectRoot: workspace,
    },
    body: {
      projectPath: 'crate',
      sourceFiles: [{ path: 'src/main.rs', content: 'fn main() {}\n' }],
      options: { generateReport: false },
      approval: { approved: true, scope: 'rust-verification' },
    },
  };
  return {
    ...base,
    ...overrides,
    body: overrides.body ?? base.body,
    context: overrides.context ?? base.context,
    params: overrides.params ?? base.params,
    headers: overrides.headers ?? base.headers,
  };
}

describe('RustVerificationPlugin security boundary', () => {
  let cleanup: (() => void) | undefined;

  beforeEach(() => {
    vi.clearAllMocks();
  });

  afterEach(() => {
    cleanup?.();
    cleanup = undefined;
  });

  it('requires authentication before Rust verification can reach writes or process execution', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn() };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace, { user: undefined }));

    expect(response.status).toBe(401);
    expect(response.error).toContain('Authentication required');
    expect(rustAgent.verifyRustProject).not.toHaveBeenCalled();
  });

  it('requires rust verification permission or operator role before executing tools', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn() };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace, {
      user: { id: 'viewer', name: 'Viewer', roles: [], permissions: [] },
    }));

    expect(response.status).toBe(403);
    expect(response.error).toContain('requires rust:verify permission');
    expect(rustAgent.verifyRustProject).not.toHaveBeenCalled();
  });

  it('requires explicit operator approval for verification writes/process execution', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn() };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace, {
      body: {
        projectPath: 'crate',
        sourceFiles: [{ path: 'src/main.rs', content: 'fn main() {}\n' }],
        options: { generateReport: false },
      },
    }));

    expect(response.status).toBe(403);
    expect(response.error).toContain('approval.scope=rust-verification');
    expect(rustAgent.verifyRustProject).not.toHaveBeenCalled();
  });

  it('rejects absolute project paths before executing tools', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn() };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace, {
      body: {
        projectPath: fixture.cratePath,
        sourceFiles: [{ path: 'src/main.rs', content: 'fn main() {}\n' }],
        options: { generateReport: false },
        approval: { approved: true, scope: 'rust-verification' },
      },
    }));

    expect(response.status).toBe(400);
    expect(response.error).toContain('projectPath must be repository-relative');
    expect(rustAgent.verifyRustProject).not.toHaveBeenCalled();
  });

  it('rejects source file traversal before executing tools', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn() };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace, {
      body: {
        projectPath: 'crate',
        sourceFiles: [{ path: '../outside.rs', content: 'fn main() {}\n' }],
        options: { generateReport: false },
        approval: { approved: true, scope: 'rust-verification' },
      },
    }));

    expect(response.status).toBe(400);
    expect(response.error).toContain('sourceFiles[0].path must not contain parent-directory');
    expect(rustAgent.verifyRustProject).not.toHaveBeenCalled();
  });

  it('rejects workspace symlink escapes before executing tools', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const outside = join(artifactRoot, `rust-plugin-outside-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`);
    mkdirSync(join(outside, 'src'), { recursive: true });
    writeFileSync(join(outside, 'Cargo.toml'), '[package]\nname = "outside"\nversion = "0.1.0"\nedition = "2021"\n', 'utf8');
    writeFileSync(join(outside, 'src', 'main.rs'), 'fn main() {}\n', 'utf8');
    try {
      symlinkSync(outside, join(fixture.workspace, 'linked-crate'), 'dir');
    } catch {
      rmSync(outside, { recursive: true, force: true });
      return;
    }
    const previousCleanup = cleanup;
    cleanup = () => {
      previousCleanup?.();
      rmSync(outside, { recursive: true, force: true });
    };
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn() };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace, {
      body: {
        projectPath: 'linked-crate',
        sourceFiles: [{ path: 'src/main.rs', content: 'fn main() {}\n' }],
        options: { generateReport: false },
        approval: { approved: true, scope: 'rust-verification' },
      },
    }));

    expect(response.status).toBe(400);
    expect(response.error).toContain('projectPath resolves outside');
    expect(rustAgent.verifyRustProject).not.toHaveBeenCalled();
  });

  it('normalizes approved project and source paths under the workspace before delegating', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn(async () => []) };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace));

    expect(response.status).toBe(200);
    expect(rustAgent.verifyRustProject).toHaveBeenCalledTimes(1);
    const verificationRequest = rustAgent.verifyRustProject.mock.calls[0]?.[0];
    expect(verificationRequest.projectPath).toBe(fixture.cratePath);
    expect(verificationRequest.sourceFiles[0].path).toBe(join(fixture.cratePath, 'src', 'main.rs'));
    expect(relative(fixture.workspace, verificationRequest.projectPath)).not.toMatch(/^\.\./u);
    expect(existsSync(verificationRequest.sourceFiles[0].path)).toBe(true);
  });

  it('accepts approved verification tool arrays after endpoint validation', async () => {
    const fixture = makeWorkspace();
    cleanup = fixture.cleanup;
    const rustAgent = { getAvailableTools: () => [], verifyRustProject: vi.fn(async () => []) };
    const server = await makeServer(fixture.workspace, rustAgent);

    const response = await server.processRequest(makeRequest(fixture.workspace, {
      body: {
        projectPath: 'crate',
        sourceFiles: [{ path: 'src/main.rs', content: 'fn main() {}\\n' }],
        verificationTools: ['miri'],
        options: { generateReport: false },
        approval: { approved: true, scope: 'rust-verification' },
      },
    }));

    expect(response.status).toBe(200);
    expect(rustAgent.verifyRustProject.mock.calls[0]?.[0].verificationTools).toEqual(['miri']);
  });
});
